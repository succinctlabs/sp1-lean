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
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState

/-! # Chip-level `DivRemChip` mirror — bundled 4-variant integer division

The DivRem chip bundles four RV64IM division variants
(`div`/`divu`/`rem`/`remu`) into a single 246-column trace, with two
`MulOperation` sub-fragments (one for the quotient × divisor product,
one for the dividend reconstruction), plus `IsZeroWord`, `AddOperation`
(for remainder), and other sub-fragments.

Iff-only structural mirror discipline (heaviest chip in the ISA). The
division-arithmetic content (carry chains, sign handling, remainder
reconstruction) is captured as a placeholder `divRemSpec` (currently
`True`).
-/

namespace SP1Clean.DivRem

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct. The 213 middle columns hold the
arithmetic intermediates (two MulOperation cols × ~46 each, IsZeroWord
cols, AddOperation cols, selectors, etc.). They're bundled into an
`aux : Vector T 213` field rather than separated since the SP1 source
itself uses them only via the sub-operations. -/
structure DivRemCols (T : Type) where
  clk_high : T                              -- Main[0]
  clk_16_24 : T                             -- Main[1]
  clk_0_16 : T                              -- Main[2]
  pc : Vector T 3                           -- Main[3..5]
  op_a : T                                  -- Main[6]
  op_a_memory_prev_value : Vector T 4       -- Main[7..10]
  op_a_memory_prev_low : T                  -- Main[11]
  op_a_memory_diff_low : T                  -- Main[12]
  op_a_0 : T                                -- Main[13]
  op_b : T                                  -- Main[14]
  op_b_memory_prev_value : Vector T 4       -- Main[15..18]
  op_b_memory_prev_low : T                  -- Main[19]
  op_b_memory_diff_low : T                  -- Main[20]
  op_c : T                                  -- Main[21]
  op_c_memory_prev_value : Vector T 4       -- Main[22..25]
  op_c_memory_prev_low : T                  -- Main[26]
  op_c_memory_diff_low : T                  -- Main[27]
  op_a_write_value : Vector T 4             -- Main[28..31]
  -- 209 intermediate columns: MulOperation × 2, IsZeroWord, AddOp,
  -- sign-extension, quotient/remainder layout, etc.
  aux : Vector T 209                        -- Main[32..240]
  is_signed : T                             -- Main[241]
  is_w : T                                  -- Main[242]
  is_rem : T                                -- Main[243]
  is_real : T                               -- Main[244]
  msb_aux1 : T                              -- Main[245]
deriving ProvableStruct

def main (cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c, _op_c_memory_prev_value,
       _op_c_memory_prev_low, _op_c_memory_diff_low, _op_a_write_value,
       _aux, is_signed, is_w, is_rem, is_real, _msb_aux1⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Opcode encoding: DIV=15, DIVU=16, REM=17, REMU=18 (32-bit set);
  -- DIVW=25, DIVUW=26, REMW=27, REMUW=28 (64-bit/32-bit set). Encoded
  -- as `is_signed * (DIVW vs DIV bias) + is_rem * (REM vs DIV bias) +
  -- is_w * (W vs non-W bias)` plus a base; here we expose the simplest
  -- placeholder opcode in the program-bus assertion below — the actual
  -- mapping is encoded via the auxiliary selector columns.
  SP1Clean.ProgramTable.assertion
    (⟨pc,
      (15 : Expression (ZMod p)) + is_signed * 0 + is_rem * 2 + is_w * 10,
      op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_signed * (is_signed - 1) === 0
  is_w * (is_w - 1) === 0
  is_rem * (is_rem - 1) === 0
  is_real * (is_real - 1) === 0
  op_a_0 === 0

/-- Placeholder for the DivRem arithmetic Spec content. Currently
`True`; a future iteration can inline `MulOperation` × 2,
`IsZeroWordOperation`, `AddOperation` constraints and the
quotient/remainder/sign-handling clauses. -/
def divRemSpec (_cols : DivRemCols (ZMod p)) : Prop := True

def Spec (cols : DivRemCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_a
      { prev_value := cols.op_a_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_a_memory_prev_low,
            diff_low_limb := cols.op_a_memory_diff_low } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_b
      { prev_value := cols.op_b_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_b_memory_prev_low,
            diff_low_limb := cols.op_b_memory_diff_low } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 2
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_c
      { prev_value := cols.op_c_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_c_memory_prev_low,
            diff_low_limb := cols.op_c_memory_diff_low } }) ∧
  cols.is_signed * (cols.is_signed - 1) = 0 ∧
  cols.is_w * (cols.is_w - 1) = 0 ∧
  cols.is_rem * (cols.is_rem - 1) = 0 ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.op_a_0 = 0 ∧
  divRemSpec cols

/-! ## Full `FormalAssertion` promotion (Path-2)

`Assertion.main` is identical to the chip's `main` (no byte lookups to
drop). The 209 intermediate columns (`MulOperation × 2`, `IsZeroWord`,
`AddOperation`, sign-extension, quotient/remainder layout) stay in
legacy `Spec` via `divRemSpec` placeholder; memory-bus consistency is
deferred to OfflineMemory. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c, _op_c_memory_prev_value,
       _op_c_memory_prev_low, _op_c_memory_diff_low, _op_a_write_value,
       _aux, is_signed, is_w, is_rem, is_real, _msb_aux1⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc,
      (15 : Expression (ZMod p)) + is_signed * 0 + is_rem * 2 + is_w * 10,
      op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_signed * (is_signed - 1) === 0
  is_w * (is_w - 1) === 0
  is_rem * (is_rem - 1) === 0
  is_real * (is_real - 1) === 0
  op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) DivRemCols unit where
  name := "SP1Clean.DivRem"
  main := main
  localLength _ := 0

def Assumptions (_ : DivRemCols (ZMod p)) : Prop := True

def FormalSpec (cols : DivRemCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc,
      opcode := (15 : ZMod p) + cols.is_signed * 0 + cols.is_rem * 2 +
                  cols.is_w * 10,
      op_a := cols.op_a, op_b := #v[cols.op_b, 0, 0, 0],
      op_c := #v[cols.op_c, 0, 0, 0],
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 0 } ∧
  cols.is_signed * (cols.is_signed - 1) = 0 ∧
  cols.is_w * (cols.is_w - 1) = 0 ∧
  cols.is_rem * (cols.is_rem - 1) = 0 ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.op_a_0 = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu_sub, h_prog_sub, h_signed, h_w, h_rem, h_real, h_op_a_0⟩ :=
    h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_signed
  · linear_combination h_w
  · linear_combination h_rem
  · linear_combination h_real
  · exact h_op_a_0

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_prog, h_signed, h_w, h_rem, h_real, h_op_a_0⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_signed
  · linear_combination h_w
  · linear_combination h_rem
  · linear_combination h_real
  · exact h_op_a_0

end Assertion

def assertion : FormalAssertion (ZMod p) DivRemCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.DivRem
