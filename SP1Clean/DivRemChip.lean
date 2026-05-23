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
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess
import SP1Chips.DivRem.DivRemChip

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
  state : CPUState T
  op_a : T                                  -- Main[6]
  op_a_memory : MemoryAccessInSharedCols T
  op_a_0 : T                                -- Main[13]
  op_b : T                                  -- Main[14]
  op_b_memory : MemoryAccessInSharedCols T
  op_c : T                                  -- Main[21]
  op_c_memory : MemoryAccessInSharedCols T
  op_a_write_value : Vector T 4             -- Main[28..31]
  -- 209 intermediate columns: MulOperation × 2, IsZeroWord, AddOp,
  -- sign-extension, quotient/remainder layout, etc.
  aux : Vector T 209                        -- Main[32..240]
  is_signed : T                             -- Main[241]
  is_w : T                                  -- Main[242]
  is_rem : T                                -- Main[243]
  is_real : T                               -- Main[244]
  msb_aux1 : T                              -- Main[245]
  next_pc_carry_value : Vector T 3
deriving ProvableStruct

def main (cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩, op_a,
       _op_a_memory,
       op_a_0, op_b, _op_b_memory, op_c, _op_c_memory, _op_a_write_value,
       _aux, is_signed, is_w, is_rem, is_real, _msb_aux1,
       _next_pc_carry_value⟩ := cols
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
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_a
      { prev_value := cols.op_a_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.op_a_memory.access_timestamp.prev_low,
            diff_low_limb := cols.op_a_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_b
      { prev_value := cols.op_b_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.op_b_memory.access_timestamp.prev_low,
            diff_low_limb := cols.op_b_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 2
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_c
      { prev_value := cols.op_c_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.op_c_memory.access_timestamp.prev_low,
            diff_low_limb := cols.op_c_memory.access_timestamp.diff_low_limb } }) ∧
  cols.is_signed * (cols.is_signed - 1) = 0 ∧
  cols.is_w * (cols.is_w - 1) = 0 ∧
  cols.is_rem * (cols.is_rem - 1) = 0 ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.op_a_0 = 0 ∧
  divRemSpec cols

/-- Project a raw SP1 row into the structured `DivRemCols` view.
246 columns; `aux : Vector T 209` packed from Main[32..240] via
`Vector.ofFn` to avoid 209 hand-written entries. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 246) : DivRemCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      Main[6],
   ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩, Main[13],
   Main[14],
   ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
   Main[21],
   ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩,
   #v[Main[28], Main[29], Main[30], Main[31]],
   Vector.ofFn (fun (i : Fin 209) => Main[32 + i.val]'(by have := i.isLt; omega)),
   Main[241], Main[242], Main[243], Main[244], Main[245],
   #v[0, 0, 0]⟩

/-- The chip-level half-iff bridge (DivRem). **Proof body sorry'd**. -/
theorem spec_implies_allHold (Main : Vector (ZMod p) 246)
    (h_is_real : Main[244] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : Spec (fromMain Main)) :
    (_root_.DivRem.constraints Main).allHold := by
  sorry

/-- Clean-side `correct_div`: 64-bit signed division. -/
theorem correct_div [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 246) (s : SailState)
    (h_is_div : Main[201] = 1) (h_is_real : Main[244] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Div.spec_div (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_div Main s
    (spec_implies_allHold Main h_is_real h_op_a_0 h_spec)
    h_is_real h_is_div state_cstrs

/-! ## Phase 1c interim consistency: 3-flag ↔ 8-flag projection

Lean `DivRemCols` carries three boolean flags `(is_signed, is_w, is_rem)`
at Main[241..243], where upstream `DivRemCols<T, M>` has eight one-hot
mode flags `is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw,
is_remuw` (alu/divrem/mod.rs:120-141). The audit (2026-05-23) flagged
this as DIVERGENT — the encoding scheme differs.

This lemma is the **interim consistency proof**: under any three booleans
the eight upstream-style one-hot flags can be reconstructed as products
of `(is_signed, 1-is_signed) × (is_w, 1-is_w) × (is_rem, 1-is_rem)`,
they are each boolean, and they sum to 1. Strategy C Phase 4d will
replace the 3-flag encoding with the 8-flag one directly; this lemma
exists to make the projection explicit in the meantime and to support
re-tagging the audit doc's DivRem DIVERGENT row from "encoding scheme
differs" to "encoding scheme differs but projection consistency proved".

The reconstructed-flag order matches upstream's struct declaration
order: `is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw,
is_remuw`.

Note: this lemma intentionally does not reference the actual aux:209
block at Main[32..240], where the upstream 8-flag columns physically
live (Main[201..208] per the bridge `SP1Chips/DivRem/Constraints.lean`).
The lemma proves a pure arithmetic identity on the Lean 3-flag values
— constraint-equivalence to upstream's 8-flag layout is the broader
Phase 4d work. -/

omit [Fact (2 ^ 17 < p)] in
private lemma bool_mul3 {x y z : ZMod p}
    (hx : x * (x - 1) = 0) (hy : y * (y - 1) = 0) (hz : z * (z - 1) = 0) :
    (x * y * z) * (x * y * z - 1) = 0 := by
  linear_combination (y * z)^2 * hx + (x * z^2) * hy + (x * y) * hz

omit [Fact (2 ^ 17 < p)] in
private lemma bool_comp {x : ZMod p} (hx : x * (x - 1) = 0) :
    (1 - x) * ((1 - x) - 1) = 0 := by
  linear_combination hx

omit [Fact (2 ^ 17 < p)] in
theorem divrem_flag_projection
    (is_signed is_w is_rem : ZMod p)
    (h_signed : is_signed * (is_signed - 1) = 0)
    (h_w : is_w * (is_w - 1) = 0)
    (h_rem : is_rem * (is_rem - 1) = 0) :
    let r_is_div   : ZMod p := is_signed       * (1 - is_w) * (1 - is_rem)
    let r_is_divu  : ZMod p := (1 - is_signed) * (1 - is_w) * (1 - is_rem)
    let r_is_rem'  : ZMod p := is_signed       * (1 - is_w) * is_rem
    let r_is_remu  : ZMod p := (1 - is_signed) * (1 - is_w) * is_rem
    let r_is_divw  : ZMod p := is_signed       * is_w       * (1 - is_rem)
    let r_is_remw  : ZMod p := is_signed       * is_w       * is_rem
    let r_is_divuw : ZMod p := (1 - is_signed) * is_w       * (1 - is_rem)
    let r_is_remuw : ZMod p := (1 - is_signed) * is_w       * is_rem
    -- Each reconstructed flag is boolean.
    r_is_div   * (r_is_div   - 1) = 0 ∧
    r_is_divu  * (r_is_divu  - 1) = 0 ∧
    r_is_rem'  * (r_is_rem'  - 1) = 0 ∧
    r_is_remu  * (r_is_remu  - 1) = 0 ∧
    r_is_divw  * (r_is_divw  - 1) = 0 ∧
    r_is_remw  * (r_is_remw  - 1) = 0 ∧
    r_is_divuw * (r_is_divuw - 1) = 0 ∧
    r_is_remuw * (r_is_remuw - 1) = 0 ∧
    -- The eight reconstructed flags sum to 1 (one-hot encoding under any
    -- assignment to the three booleans).
    r_is_div + r_is_divu + r_is_rem' + r_is_remu +
      r_is_divw + r_is_remw + r_is_divuw + r_is_remuw = 1 := by
  simp only
  have h_neg_s := bool_comp h_signed
  have h_neg_w := bool_comp h_w
  have h_neg_r := bool_comp h_rem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bool_mul3 h_signed h_neg_w h_neg_r
  · exact bool_mul3 h_neg_s h_neg_w h_neg_r
  · exact bool_mul3 h_signed h_neg_w h_rem
  · exact bool_mul3 h_neg_s h_neg_w h_rem
  · exact bool_mul3 h_signed h_w h_neg_r
  · exact bool_mul3 h_signed h_w h_rem
  · exact bool_mul3 h_neg_s h_w h_neg_r
  · exact bool_mul3 h_neg_s h_w h_rem
  · ring

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
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩, op_a,
       op_a_memory,
       op_a_0, op_b, op_b_memory, op_c, op_c_memory, _op_a_write_value,
       _aux, is_signed, is_w, is_rem, is_real, _msb_aux1,
       next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc,
      (15 : Expression (ZMod p)) + is_signed * 0 + is_rem * 2 + is_w * 10,
      op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_signed * (is_signed - 1) === 0
  is_w * (is_w - 1) === 0
  is_rem * (is_rem - 1) === 0
  is_real * (is_real - 1) === 0
  op_a_0 === 0
  -- Iter-8 sub-task E: per-operand memory-bus byte content.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 2, op_c_memory.access_timestamp.prev_low, op_c_memory.access_timestamp.diff_low_limb,
       op_c_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

set_option maxHeartbeats 800000 in
-- Higher heartbeats: 25 input fields + 4 subcircuit calls + 3 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) DivRemCols unit where
  name := "SP1Clean.DivRem"
  main := main
  localLength _ := 0

def Assumptions (_ : DivRemCols (ZMod p)) : Prop := True

def FormalSpec (cols : DivRemCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := (15 : ZMod p) + cols.is_signed * 0 + cols.is_rem * 2 +
                  cols.is_w * 10,
      op_a := cols.op_a, op_b := #v[cols.op_b, 0, 0, 0],
      op_c := #v[cols.op_c, 0, 0, 0],
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 0 } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_signed * (cols.is_signed - 1) = 0 ∧
  cols.is_w * (cols.is_w - 1) = 0 ∧
  cols.is_rem * (cols.is_rem - 1) = 0 ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.op_a_memory.access_timestamp.prev_low, cols.op_a_memory.access_timestamp.diff_low_limb,
     cols.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.op_b_memory.access_timestamp.prev_low, cols.op_b_memory.access_timestamp.diff_low_limb,
     cols.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.op_c_memory.access_timestamp.prev_low, cols.op_c_memory.access_timestamp.diff_low_limb,
     cols.op_c_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_signed, h_w, h_rem, h_real,
          h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_signed
  · linear_combination h_w
  · linear_combination h_rem
  · linear_combination h_real
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_signed, h_w, h_rem, h_real, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · linear_combination h_signed
  · linear_combination h_w
  · linear_combination h_rem
  · linear_combination h_real
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩

end Assertion

def assertion : FormalAssertion (ZMod p) DivRemCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.DivRem
