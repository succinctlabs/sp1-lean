import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ITypeReaderImmutable.ITypeReaderImmutable
import SP1Chips.Branch.BranchChip
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode

/-! # Chip-level `BranchChip` mirror — bundled 6-variant conditional branch

The Branch chip bundles six RV64I conditional-branch variants
(`beq`/`bne`/`blt`/`bge`/`bltu`/`bgeu`) into a single 45-column trace.
Variants are distinguished by selectors at `Main[28..33]`. Uses
`ITypeReaderImmutable` (op_a / op_b read, no write) plus an inline
`LtOperationSigned` sub-fragment to compute the comparison result.

Structural mirror discipline (Spec only). The `LtOperationSigned`
constraint clause is left in raw `allHold` form. The next_pc
chain is state-bus content (per-row `True`); cross-row PC consistency
is a separate trace-level concern.

Opcode encoding: `is_beq * 40 + is_bne * 41 + is_blt * 42 + is_bge * 43
+ is_bltu * 44 + is_bgeu * 45` (40-45 = BEQ/BNE/BLT/BGE/BLTU/BGEU).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Branch

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `BranchCols<T>`. -/
structure BranchCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  next_pc : Vector T 3                      -- Main[25..27]
  is_beq : T                                -- Main[28]
  is_bne : T                                -- Main[29]
  is_blt : T                                -- Main[30]
  is_bge : T                                -- Main[31]
  is_bltu : T                               -- Main[32]
  is_bgeu : T                               -- Main[33]
  -- Main[34] mirrors upstream's `is_branching: T` — forced equal under `is_real`
  -- to `is_beq*(b==c) + is_bne*(b!=c) + (is_bge+is_bgeu)*(b>=c) + (is_blt+is_bltu)*(b<c)`
  -- by the bridge's E94/E96 assertZeros. The previous Lean name `lt_is_signed`
  -- was a misnomer: this column is NOT the `is_signed` arg to LtOperationSigned
  -- (which is `is_blt + is_bge`); it is the branch-taken predicate output.
  is_branching : T                          -- Main[34] (Rust-aligned name)
  compare_operation : LtOperationSigned T   -- Main[35..44]
  -- Iter-8 sub-task C: state-bus next_pc grounding mux selector.
  -- Semantically redundant with `is_branching` (Main[34]) — both encode the
  -- branch-taken predicate. Kept as a separate Clean-only column for now to
  -- preserve the existing Assertion.main mux structure; Phase 4 (TrustMode)
  -- — adapter_cols scaffolding landed; this is_branching_aux removal is
  -- still pending.
  is_branching_aux : T                      -- Clean-only mux selector (duplicates is_branching)
  next_pc_branched_carry : Vector T 3       -- Clean-only: pc + op_c_imm carry-aware result
  next_pc_unbranched_carry : Vector T 3     -- Clean-only: pc + 4 carry-aware result
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Aggregate is-real flag: sum of 6 selectors. -/
def isRealExpr (cols : Var BranchCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
    cols.is_bltu + cols.is_bgeu

/-- Selector-weighted opcode expression. -/
def opcodeExpr (cols : Var BranchCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
    cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45

def main (cols : Var BranchCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c_imm⟩, _next_pc,
       is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu,
       _is_branching, _compare_operation,
       _is_branching_aux, _next_pc_branched_carry, _next_pc_unbranched_carry,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_beq * 40 + is_bne * 41 + is_blt * 42 +
                    is_bge * 43 + is_bltu * 44 + is_bgeu * 45
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Six opcode-selector boolean gates plus the aggregate-is-real boolean.
  is_beq * (is_beq - 1) === 0
  is_bne * (is_bne - 1) === 0
  is_blt * (is_blt - 1) === 0
  is_bge * (is_bge - 1) === 0
  is_bltu * (is_bltu - 1) === 0
  is_bgeu * (is_bgeu - 1) === 0
  let sum := is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu
  sum * (sum - 1) === 0

def Spec (cols : BranchCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu
  let opcode_e : ZMod p :=
    cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
      cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45
  (_root_.LtOperationSigned.constraints (F := ZMod p)
      cols.adapter.op_a_memory.prev_value cols.adapter.op_b_memory.prev_value
      cols.compare_operation (cols.is_blt + cols.is_bge) is_real).allHold ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := opcode_e,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_beq * (cols.is_beq - 1) = 0 ∧
  cols.is_bne * (cols.is_bne - 1) = 0 ∧
  cols.is_blt * (cols.is_blt - 1) = 0 ∧
  cols.is_bge * (cols.is_bge - 1) = 0 ∧
  cols.is_bltu * (cols.is_bltu - 1) = 0 ∧
  cols.is_bgeu * (cols.is_bgeu - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.adapter_cols.is_trusted = 1

/-- The op_a / op_b register accesses (both reads; no writes — Branch
doesn't update any register, only PC). -/
def opAMemoryAccess (cols : BranchCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_a, 0, 0],
    prev_value := cols.adapter.op_a_memory.prev_value,
    prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }

def opBMemoryAccess (cols : BranchCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_b, 0, 0],
    prev_value := cols.adapter.op_b_memory.prev_value,
    prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }

/-- Project a raw SP1 row into the structured `BranchCols` view.
45 columns; `compare_operation : LtOperationSigned T` packed from
Main[35..44]. Clean-only fields (`is_branching_aux`, branched/unbranched
carry vectors) default to placeholder values since the SP1 row doesn't
carry them. Note: `is_branching` at Main[34] *is* on the row (Rust-aligned
name; previously misnamed `lt_is_signed`). -/
@[reducible] def fromMain (Main : Vector (ZMod p) 45) : BranchCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28], Main[29], Main[30], Main[31], Main[32], Main[33],
   Main[34],
   { result :=
       { u16_compare_operation := { bit := Main[35] },
         u16_flags := #v[Main[36], Main[37], Main[38], Main[39]],
         not_eq_inv := Main[40],
         comparison_limbs := #v[Main[41], Main[42]] },
     b_msb := { msb := Main[43] },
     c_msb := { msb := Main[44] } },
   0, #v[0, 0, 0], #v[0, 0, 0],
   ⟨Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33]⟩⟩

/-- The chip-level half-iff bridge (Branch). **Proof body sorry'd**. -/
theorem spec_implies_allHold (Main : Vector (ZMod p) 45)
    (h_is_real : Main[28] + Main[29] + Main[30] + Main[31] +
                 Main[32] + Main[33] = 1)
    (h_spec : Spec (fromMain Main)) :
    (_root_.Branch.constraints Main).allHold := by
  sorry

/-- Clean-side `correct_beq`: branch-if-equal. -/
theorem correct_beq
    (Main : Vector (ZMod p) 45) (s : SailState) (hs : s.isInitialized)
    (h_is_beq : Main[28] = 1)
    (h_others_zero : Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧
                     Main[32] = 0 ∧ Main[33] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Branch.constraints Main).initialState s) :
    let imm := _root_.Branch.sp1_imm Main
    let op_b := regidx.Regidx (_root_.Branch.sp1_op_b Main)
    let op_a := regidx.Regidx (_root_.Branch.sp1_op_a Main)
    (_root_.Branch.BEQ.spec_beq imm op_b op_a).run s =
      (_root_.Branch.sp1_branch Main).run s :=
  _root_.Branch.BEQ.correct_beq Main s hs h_is_beq
    (spec_implies_allHold Main
      (by obtain ⟨h29, h30, h31, h32, h33⟩ := h_others_zero
          rw [h_is_beq, h29, h30, h31, h32, h33]; ring)
      h_spec)
    state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2)

`Assertion.main` is identical to the chip's `main` (no byte lookups
to drop). The `LtOperationSigned.constraints` clause that drives the
branch-taken comparison stays in legacy `Spec` and is deferred to the
trace-level OfflineMemory + state-bus bridge. Memory-bus consistency
likewise deferred. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var BranchCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, next_pc,
       is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu,
       _is_branching, _compare_operation,
       is_branching_aux, next_pc_branched_carry, next_pc_unbranched_carry,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_beq * 40 + is_bne * 41 + is_blt * 42 +
                    is_bge * 43 + is_bltu * 44 + is_bgeu * 45
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_beq * (is_beq - 1) === 0
  is_bne * (is_bne - 1) === 0
  is_blt * (is_blt - 1) === 0
  is_bge * (is_bge - 1) === 0
  is_bltu * (is_bltu - 1) === 0
  is_bgeu * (is_bgeu - 1) === 0
  let sum := is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu
  sum * (sum - 1) === 0
  -- State-bus next_pc grounding (iter-8 sub-task C). Both arms' carry-aware
  -- AddrAddOp constraints are emitted unconditionally; the chip's `next_pc`
  -- column is the `is_branching`-weighted mux of the two arm results.
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       op_c_imm,
       next_pc_branched_carry⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_unbranched_carry⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_branching_aux * (is_branching_aux - 1) === 0
  -- Per-limb mux: next_pc[i] = is_branching_aux * (branched[i] - unbranched[i]) + unbranched[i].
  -- Equivalent to `is_branching_aux * branched + (1 - is_branching_aux) * unbranched`
  -- but avoids `(1 : ℕ) - is_branching_aux : Expression _` type ambiguity.
  -- `is_branching_aux` is the Clean-only mux selector duplicating Main[34]'s
  -- `is_branching`; Phase 4 (TrustMode) — adapter_cols scaffolding landed;
  -- this is_branching_aux removal is still pending.
  next_pc[0] -
    (is_branching_aux * (next_pc_branched_carry[0] - next_pc_unbranched_carry[0]) +
     next_pc_unbranched_carry[0]) === 0
  next_pc[1] -
    (is_branching_aux * (next_pc_branched_carry[1] - next_pc_unbranched_carry[1]) +
     next_pc_unbranched_carry[1]) === 0
  next_pc[2] -
    (is_branching_aux * (next_pc_branched_carry[2] - next_pc_unbranched_carry[2]) +
     next_pc_unbranched_carry[2]) === 0
  -- Iter-8 sub-task E: per-operand memory-bus byte content. Branch
  -- emits 2 register accesses (op_a at +4, op_b at +3) — both pure
  -- reads (no register writes; only PC is updated).
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

set_option maxHeartbeats 800000 in
-- Higher heartbeats: Branch has 26 input fields + 4 subcircuit calls
-- + 2 OperandAccess calls; localLength_eq synthesis hits the 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) BranchCols unit where
  name := "SP1Clean.Branch"
  main := main
  localLength _ := 0

def Assumptions (_ : BranchCols (ZMod p)) : Prop := True

def FormalSpec (cols : BranchCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu
  let opcode_e : ZMod p :=
    cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
      cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := opcode_e, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_beq * (cols.is_beq - 1) = 0 ∧
  cols.is_bne * (cols.is_bne - 1) = 0 ∧
  cols.is_blt * (cols.is_blt - 1) = 0 ∧
  cols.is_bge * (cols.is_bge - 1) = 0 ∧
  cols.is_bltu * (cols.is_bltu - 1) = 0 ∧
  cols.is_bgeu * (cols.is_bgeu - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  -- Iter-8 sub-task C: state-bus next_pc grounding (case-split on `is_branching`).
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     cols.adapter.op_c_imm,
     cols.next_pc_branched_carry⟩ ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_unbranched_carry⟩ ∧
  cols.is_branching_aux * (cols.is_branching_aux - 1) = 0 ∧
  cols.next_pc[0] = cols.is_branching_aux *
      (cols.next_pc_branched_carry[0] - cols.next_pc_unbranched_carry[0]) +
    cols.next_pc_unbranched_carry[0] ∧
  cols.next_pc[1] = cols.is_branching_aux *
      (cols.next_pc_branched_carry[1] - cols.next_pc_unbranched_carry[1]) +
    cols.next_pc_unbranched_carry[1] ∧
  cols.next_pc[2] = cols.is_branching_aux *
      (cols.next_pc_branched_carry[2] - cols.next_pc_unbranched_carry[2]) +
    cols.next_pc_unbranched_carry[2] ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- Branch emits 2 register accesses: op_a/+4 and op_b/+3 (pure reads).
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
          h_sum, h_addr_taken, h_addr_unt, h_branching_bool,
          h_mux0, h_mux1, h_mux2, h_oa_a, h_oa_b⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_beq
  · linear_combination h_bne
  · linear_combination h_blt
  · linear_combination h_bge
  · linear_combination h_bltu
  · linear_combination h_bgeu
  · linear_combination h_sum
  · simp only [Vector.getElem_map]
    exact h_addr_taken trivial
  · simp only [Vector.getElem_map]
    exact h_addr_unt trivial
  · linear_combination h_branching_bool
  · dsimp only
    simp only [Vector.getElem_map]
    linear_combination h_mux0
  · dsimp only
    simp only [Vector.getElem_map]
    linear_combination h_mux1
  · dsimp only
    simp only [Vector.getElem_map]
    linear_combination h_mux2
  · exact h_oa_a trivial
  · exact h_oa_b trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_sum,
          h_addr_taken, h_addr_unt, h_branching_bool,
          h_mux0, h_mux1, h_mux2, h_oa_a, h_oa_b⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_beq
  · linear_combination h_bne
  · linear_combination h_blt
  · linear_combination h_bge
  · linear_combination h_bltu
  · linear_combination h_bgeu
  · linear_combination h_sum
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr_taken
    exact h_addr_taken
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr_unt
    exact h_addr_unt
  · linear_combination h_branching_bool
  · dsimp only at h_mux0
    simp only [Vector.getElem_map] at h_mux0
    linear_combination h_mux0
  · dsimp only at h_mux1
    simp only [Vector.getElem_map] at h_mux1
    linear_combination h_mux1
  · dsimp only at h_mux2
    simp only [Vector.getElem_map] at h_mux2
    linear_combination h_mux2
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩

end Assertion

def assertion : FormalAssertion (ZMod p) BranchCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Branch
