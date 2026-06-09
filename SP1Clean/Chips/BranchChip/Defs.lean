import SP1Clean.Specs.Chip
import SP1Clean.Operations.AddOperation.Formal
import SP1Clean.Operations.LtOperationSigned.Formal
import SP1Clean.Operations.LtOperationSigned.Populate
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.ITypeReaderImmutable
import SP1Clean.Foundations.Channels
import SP1Clean.Foundations.ByteTable
import SP1Clean.Extracted.BranchChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The BRANCH chip row as a `GeneralFormalCircuit`

Conditional control flow (opcodes 40–45: BEQ/BNE/BLT/BGE/BLTU/BGEU): `next_pc` is data-dependent
(`pc + sign_extend(imm)` taken, `pc + 4` fall-through, chosen by the compare). Composes
`LtOperationSigned` (mode `is_blt + is_bge`), two `AddOperation` gadgets (gates `is_branching` /
`is_real - is_branching`), `CPUState`, `ITypeReaderImmutable`, and three next_pc byte-range sends. The
six opcode flags sum to `is_real` (one-hot); the branch opcode is threaded via `ProverHint`. Implements
SP1's `Branch` `air.rs:eval`. -/

namespace SP1Clean.BranchChip

open Circuit
open Extracted (BranchColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `14 < p`, so the alignment `Range` byte-row width column `14` round-trips through `byteRowSpec_range`. -/
lemma h14p : (14 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

omit [Fact p.Prime] in
/-- `16 < p`, for the `next_pc[1]`/`next_pc[2]` u16 range sends. -/
lemma h16p : (16 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

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

/-- Compose the BRANCH row. Witnesses the six opcode flags + `is_branching`, the two `AddOperation` targets
(`branch_value = pc + op_c_imm`, `fall_value = pc + 4`) via `AddOperation.populate`, and the selected
`next_pc`; composes the demoted `AddOperation` gadget and the signed-compare gadget as Clean subcircuits;
binds `is_real = Σ is_b*`, derives the `is_branching` decision from the compare, and emits the program /
state / memory / byte buses. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var BranchColumns (ZMod p)) := do
  let pcWordV : Word (Expression (ZMod p)) :=
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0]
  let rs1WordV : Word (Expression (ZMod p)) :=
    #v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
       input.adapter.op_a_memory.prev_value[2], input.adapter.op_a_memory.prev_value[3]]
  let rs2WordV : Word (Expression (ZMod p)) :=
    #v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
       input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]]
  -- six opcode flags + is_branching: threaded via ProverHint (not an Inputs field).
  let flags ← witnessVector 6 (fun env => hintFlags env.hint)
  let is_beq := flags[0]; let is_bne := flags[1]; let is_blt := flags[2]
  let is_bge := flags[3]; let is_bltu := flags[4]; let is_bgeu := flags[5]
  let is_branching ← witnessField (fun env => hintBranching env.hint)
  let branch_value ← witnessVector 4 (fun env =>
    AddOperation.populate
      #v[env input.state.pc[0], env input.state.pc[1], env input.state.pc[2], 0]
      #v[env input.adapter.op_c_imm[0], env input.adapter.op_c_imm[1],
         env input.adapter.op_c_imm[2], env input.adapter.op_c_imm[3]])
  let fall_value ← witnessVector 4 (fun env =>
    AddOperation.populate
      #v[env input.state.pc[0], env input.state.pc[1], env input.state.pc[2], 0]
      #v[4, 0, 0, 0])
  -- next_pc: `is_branching·branch + (is_real - is_branching)·fall` (matches selection asserts below).
  let next_pc ← witnessVector 3 (fun env =>
    let br := env is_branching
    let re := env input.is_real
    #v[br * env branch_value[0] + (re - br) * env fall_value[0],
       br * env branch_value[1] + (re - br) * env fall_value[1],
       br * env branch_value[2] + (re - br) * env fall_value[2]])
  -- The chip witnesses the `LtOperationSigned` column block (unsigned compare + two sign bits) via
  -- `populate` (`is_signed := is_blt + is_bge`), placed at the same offset the old subcircuit occupied,
  -- then composes `LtOperationSigned.circuit` as a Clean `assertion` (a `FormalAssertion`).
  let lt_cols ← ProvableType.witness (fun env =>
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
  input.is_real === sum
  sum * (sum - 1) === 0
  let is_eq := (1 : Expression (ZMod p)) - (cmp.result.u16_flags[0] + cmp.result.u16_flags[1]
    + cmp.result.u16_flags[2] + cmp.result.u16_flags[3])
  let bit := cmp.result.u16_compare_operation.bit
  let decision := is_beq * is_eq + is_bne * (1 - is_eq)
    + (is_bge + is_bgeu) * (1 - bit) + (is_blt + is_bltu) * bit
  is_branching * (is_branching - 1) === 0
  input.is_real * (is_branching - decision) === 0
  -- padding: `is_real = 0 → is_branching = 0` keeps `is_real - is_branching` binary.
  (input.is_real - 1) * is_branching === 0
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[next_pc[0], next_pc[1], next_pc[2]], 8, input.is_real⟩
  assertion AddOperation.circuit ⟨pcWordV, input.adapter.op_c_imm, { value := branch_value }, is_branching⟩
  branch_value[3] === 0
  assertion AddOperation.circuit
    ⟨pcWordV, #v[4, 0, 0, 0], { value := fall_value }, input.is_real - is_branching⟩
  fall_value[3] === 0
  next_pc[0] === is_branching * branch_value[0] + (input.is_real - is_branching) * fall_value[0]
  next_pc[1] === is_branching * branch_value[1] + (input.is_real - is_branching) * fall_value[1]
  next_pc[2] === is_branching * branch_value[2] + (input.is_real - is_branching) * fall_value[2]
  let opcode := is_beq * 40 + is_bne * 41 + is_blt * 42 + is_bge * 43 + is_bltu * 44 + is_bgeu * 45
  assertion Readers.ITypeReaderImmutable.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, opcode⟩
  byteChannel.gatedReceive input.is_real
    (⟨6, (next_pc[0] * (4 : ZMod p)⁻¹), Expression.const ((14 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.gatedReceive input.is_real
    (⟨6, next_pc[1], Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.gatedReceive input.is_real
    (⟨6, next_pc[2], Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  return ⟨input.state, input.adapter, next_pc,
    is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_branching, cmp⟩

set_option maxHeartbeats 4000000 in
instance elaborated : ElaboratedCircuit (ZMod p) Inputs BranchColumns main where
  channelsLawful := by simp [circuit_norm, main, AddOperation.circuit, LtOperationSigned.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit]
  -- 6 flags + 1 is_branching + 8 add targets + 3 next_pc + 10 (LtOperationSigned subcircuit).
  localLength _ := 18 + 10
  localLength_eq := by simp +arith [circuit_norm, main, AddOperation.circuit, LtOperationSigned.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit]
  subcircuitsConsistent := by simp only [circuit_norm, main, AddOperation.circuit, LtOperationSigned.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit]; try omega
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

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
