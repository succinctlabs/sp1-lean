import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddOperation.Populate
import SP1Clean.Proofs.Operations.LtOperationSigned.Formal
import SP1Clean.Native.Operations.LtOperationSigned.Populate
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReaderImmutable
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The BRANCH chip row as a `GeneralFormalCircuit`

Conditional control flow (opcodes 40–45: BEQ/BNE/BLT/BGE/BLTU/BGEU): `next_pc` is data-dependent
(`pc + sign_extend(imm)` taken, `pc + 4` fall-through, chosen by the compare). The row composes
`LtOperationSigned` (mode `is_blt + is_bge`), `CPUState`, and `ITypeReaderImmutable`, then states
SP1's eight inline gated carry equations for the two possible PC additions exactly. `AddOperation`
is used only as proof-oriented witness-generation mathematics; it is not a Branch AIR subcircuit and
does not contribute interactions. The six opcode flags sum to `is_real` (one-hot); the branch opcode
is threaded via `ProverHint`. Implements pinned SP1 v6.3.1's `Branch` `air.rs::eval`. -/

namespace SP1Clean.BranchChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `14 < p`, so the alignment `Range` byte-row width column `14` round-trips through `byteRowSpec_range`. -/
lemma h14p : (14 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- The six honest opcode flags the prover supplies via the `"branch_flags"` hint key (one-hot for the
active branch opcode `Σ is_b*·k`, all-zero on padding). Falls back to all-zero when the key is absent. -/
def hintFlags (h : ProverHint (ZMod p)) : Vector (ZMod p) 6 :=
  ((h "branch_flags" 6)[0]?).getD #v[0, 0, 0, 0, 0, 0]

/-- The honest `is_branching` decision the prover supplies via the `"branch_branching"` hint key. -/
def hintBranching (h : ProverHint (ZMod p)) : ZMod p :=
  (((h "branch_branching" 1)[0]?).getD #v[0])[0]

/-- The rs1 register value (the `op_a` source read's prior value) as a 4-limb word, from the inputs. -/
def rs1WordInput (input : Inputs (ZMod p)) : Word (ZMod p) :=
  #v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
     input.adapter.op_a_memory.prev_value[2], input.adapter.op_a_memory.prev_value[3]]

/-- The rs2 register value (the `op_b` source read's prior value) as a 4-limb word, from the inputs. -/
def rs2WordInput (input : Inputs (ZMod p)) : Word (ZMod p) :=
  #v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
     input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]]

/-- Compose the BRANCH row with the exact Rust-owned local-column shape:
six opcode flags, `is_branching`, three `next_pc` limbs, and the ten `LtOperationSigned` columns.
The witness closure uses `AddOperation.populate` to compute the selected target, while the circuit
itself commits only SP1's inline carry equations and its three `next_pc` range interactions. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let rs1WordV : Word (Expression (ZMod p)) :=
    #v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
       input.adapter.op_a_memory.prev_value[2], input.adapter.op_a_memory.prev_value[3]]
  let rs2WordV : Word (Expression (ZMod p)) :=
    #v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
       input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]]
  -- six opcode flags + is_branching: threaded via ProverHint (not an Inputs field).
  let flags ← witnessVectorNative 6 (fun env => hintFlags env.hint)
  let is_beq := flags[0]; let is_bne := flags[1]; let is_blt := flags[2]
  let is_bge := flags[3]; let is_bltu := flags[4]; let is_bgeu := flags[5]
  let is_branching ← witnessNative (var := Expression) (fun env => hintBranching env.hint)
  let next_pc ← witnessVectorNative 3 (fun env =>
    let pc : Word (ZMod p) :=
      #v[env input.state.pc[0], env input.state.pc[1],
        env input.state.pc[2], 0]
    let imm : Word (ZMod p) :=
      #v[env input.adapter.op_c_imm[0], env input.adapter.op_c_imm[1],
        env input.adapter.op_c_imm[2], env input.adapter.op_c_imm[3]]
    let branchValue := AddOperation.populate pc imm
    let fallValue := AddOperation.populate pc #v[4, 0, 0, 0]
    let branch := env is_branching
    let real := env input.is_real
    #v[branch * branchValue[0] + (real - branch) * fallValue[0],
      branch * branchValue[1] + (real - branch) * fallValue[1],
      branch * branchValue[2] + (real - branch) * fallValue[2]])
  let lt_cols ← witnessNative (var := Var Extracted.LtOperationSigned) (fun env =>
    LtOperationSigned.populate
      #v[env input.adapter.op_a_memory.prev_value[0], env input.adapter.op_a_memory.prev_value[1],
         env input.adapter.op_a_memory.prev_value[2], env input.adapter.op_a_memory.prev_value[3]]
      #v[env input.adapter.op_b_memory.prev_value[0], env input.adapter.op_b_memory.prev_value[1],
         env input.adapter.op_b_memory.prev_value[2], env input.adapter.op_b_memory.prev_value[3]]
      (env (is_blt + is_bge)) (env input.is_real))
  let cmp := lt_cols
  assertion LtOperationSigned.circuit ⟨rs1WordV, rs2WordV, lt_cols, is_blt + is_bge, input.is_real⟩
  is_beq * (is_beq - 1) === 0
  is_bne * (is_bne - 1) === 0
  is_blt * (is_blt - 1) === 0
  is_bge * (is_bge - 1) === 0
  is_bltu * (is_bltu - 1) === 0
  is_bgeu * (is_bgeu - 1) === 0
  let sum := is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu
  -- shallow (`assertZero`, W11 Phase 0c): the three next_pc byte pulls are gated by `input.is_real`, whose
  -- binarity is `is_real = Σ flags` ∧ `Σ flags ∈ {0,1}`; both must be visible to `ConstraintsHold.Shallow`.
  assertZero (input.is_real - sum)
  assertZero (sum * (sum - 1))
  let is_eq := (1 : Expression (ZMod p)) - (cmp.result.u16_flags[0] + cmp.result.u16_flags[1]
    + cmp.result.u16_flags[2] + cmp.result.u16_flags[3])
  let bit := cmp.result.u16_compare_operation.bit
  let decision := is_beq * is_eq + is_bne * (1 - is_eq)
    + (is_bge + is_bgeu) * (1 - bit) + (is_blt + is_bltu) * bit
  is_branching * (is_branching - 1) === 0
  sum * (is_branching - decision) === 0
  let baseInv : Expression (ZMod p) :=
    Expression.const ((65536 : ZMod p)⁻¹)
  let taken0 :=
    (input.state.pc[0] + input.adapter.op_c_imm[0] - next_pc[0]) *
      baseInv
  let taken1 :=
    (input.state.pc[1] + input.adapter.op_c_imm[1] - next_pc[1] +
      taken0) * baseInv
  let taken2 :=
    (input.state.pc[2] + input.adapter.op_c_imm[2] - next_pc[2] +
      taken1) * baseInv
  let taken3 := (input.adapter.op_c_imm[3] + taken2) * baseInv
  assertZero (is_branching * (taken0 * (taken0 - 1)))
  assertZero (is_branching * (taken1 * (taken1 - 1)))
  assertZero (is_branching * (taken2 * (taken2 - 1)))
  assertZero (is_branching * (taken3 * (taken3 - 1)))
  let fall0 :=
    (input.state.pc[0] + (4 : Expression (ZMod p)) - next_pc[0]) *
      baseInv
  let fall1 := (input.state.pc[1] - next_pc[1] + fall0) * baseInv
  let fall2 := (input.state.pc[2] - next_pc[2] + fall1) * baseInv
  let fall3 := fall2 * baseInv
  let fallGate := sum - is_branching
  assertZero (fallGate * (fall0 * (fall0 - 1)))
  assertZero (fallGate * (fall1 * (fall1 - 1)))
  assertZero (fallGate * (fall2 * (fall2 - 1)))
  assertZero (fallGate * (fall3 * (fall3 - 1)))
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[next_pc[0], next_pc[1], next_pc[2]], 8, input.is_real⟩
  let opcode := is_beq * 40 + is_bne * 41 + is_blt * 42 + is_bge * 43 + is_bltu * 44 + is_bgeu * 45
  -- `ITypeReaderImmutable` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ITypeReaderImmutable.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, opcode⟩
  byteChannel.pullIf input.is_real
    (⟨6, (next_pc[0] * (4 : ZMod p)⁻¹), Expression.const ((14 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨6, next_pc[1], Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨6, next_pc[2], Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  return ⟨input.state, input.adapter, next_pc,
    is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_branching, cmp⟩

/-- Derive the 20 Rust-owned witness cells and complete four-channel interface from `main`. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main := by
  elaborate_circuit

/-- Folded completed-row layout used by the whole-chip Rust AIR codec.  The 20 Rust-owned local
cells are, in order, the six opcode flags, `is_branching`, the three `next_pc` limbs, and the ten
`LtOperationSigned` cells. -/
@[circuit_norm] lemma directOutput_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        Vector.mapRange 3 fun i => var { index := offset + 7 + i },
        var { index := offset },
        var { index := offset + 1 },
        var { index := offset + 2 },
        var { index := offset + 3 },
        var { index := offset + 4 },
        var { index := offset + 5 },
        var { index := offset + 6 },
        varFromOffset Extracted.LtOperationSigned (offset + 10)⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of the independent Branch input prefix. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real,
         state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Folded projection of the Branch input activity flag.

Keeping this projection behind a theorem prevents `eval_inputFirstRow` consumers from asking
reducibility to unfold the completed circuit while recovering the first input cell. -/
@[circuit_norm] theorem eval_inputIsReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).is_real = Expression.eval env input.is_real := by
  simpa only [CircuitType.eval_expr] using
    congrArg (fun value : Inputs F => value.is_real) (eval_inputs env input)

/-- Component-wise evaluation of the completed Branch row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state,
         adapter := Eval.eval env cols.adapter,
         next_pc := Eval.eval env cols.next_pc,
         is_beq := Eval.eval env cols.is_beq,
         is_bne := Eval.eval env cols.is_bne,
         is_blt := Eval.eval env cols.is_blt,
         is_bge := Eval.eval env cols.is_bge,
         is_bltu := Eval.eval env cols.is_bltu,
         is_bgeu := Eval.eval env cols.is_bgeu,
         is_branching := Eval.eval env cols.is_branching,
         compare_operation := Eval.eval env cols.compare_operation } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (input : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength input = 20 := rfl

/-- The taken target word the chip witnesses for `branch_value` (`pc + op_c_imm`, base-2^16). -/
def branchTargetWord (input : Inputs (ZMod p)) : Word (ZMod p) :=
  AddOperation.populate
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] input.adapter.op_c_imm

/-- The fall-through word the chip witnesses for `fall_value` (`pc + 4`, base-2^16). -/
def fallThroughWord (input : Inputs (ZMod p)) : Word (ZMod p) :=
  AddOperation.populate
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] #v[4, 0, 0, 0]

/-- The committed `next_pc` limbs the chip selects: the `is_branching`-mux of the taken/​fall targets,
as a pure function of the inputs and the prover's `is_branching` value (matches the `main` witness). -/
def committedNextPc (input : Inputs (ZMod p)) (br : ZMod p) : Vector (ZMod p) 3 :=
  let b := branchTargetWord input
  let f := fallThroughWord input
  #v[br * b[0] + (input.is_real - br) * f[0],
     br * b[1] + (input.is_real - br) * f[1],
     br * b[2] + (input.is_real - br) * f[2]]

end SP1Clean.BranchChip
