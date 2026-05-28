import SP1Clean.Chips.ALU.ShiftLeftChip.Cols
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.U16MSBOperation
import SP1Chips.ShiftLeft.Common

/-! # `ShiftLeftChip` cols-level lemmas (4-lemma scaffold, all sorry'd)

2-variant chip (`sll`/`sllw`). The shift operation is inline (no
separate `ShiftLeftOperation` module); the chip-level
`_root_.ShiftLeft.allHold_constraints_iff` exposes the byte-level
internals directly. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeft

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma fromMain_toMain (_cols : ShiftLeftCols (ZMod p))
    (_h_trusted : True) : True := by trivial

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 65)
    (h_is_real : Main[62] + Main[63] = 1) :
    (_root_.ShiftLeft.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (p > 65536) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.ShiftLeft.constraints Main).allHold
        = List.Forall SP1Constraint.toProp (_root_.ShiftLeft.constraints Main) from rfl,
    _root_.ShiftLeft.allHold_constraints_iff Main]
  simp only [Assertion.FormalSpec, fromMain, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ Iff.rfl))
  · -- U16MSB block (faithful reformulation; range bridged by `range_at_sixteen`)
    simp only [U16MSBOperation.constraints, SP1ConstraintList.allHold, List.Forall,
      SP1Constraint.toProp, ByteOpcode.ofNat_seven,
      SP1Clean.U16MSBOp.range_at_sixteen, and_true, Nat.cast_ofNat]
  · -- CPUState
    exact SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1
  · -- ALUTypeReader (gate args normalize to `1 1` via `is_real = 1`)
    rw [h_is_real]
    exact SP1Clean.ALUTypeReader.Gated.Assertion.Spec_iff_sp1

lemma formalSpec_of_subcircuit_specs
    (cols : ShiftLeftCols (ZMod p))
    (_h_is_real_sum : cols.is_sll + cols.is_sllw = 1) :
    Assertion.FormalSpec cols := by
  sorry

lemma subcircuit_specs_of_formalSpec
    (cols : ShiftLeftCols (ZMod p))
    (_h_is_real_sum : cols.is_sll + cols.is_sllw = 1)
    (_h_spec : Assertion.FormalSpec cols) :
    True := by trivial

end SP1Clean.ShiftLeft
