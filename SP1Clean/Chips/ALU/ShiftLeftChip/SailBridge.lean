import SP1Clean.Chips.ALU.ShiftLeftChip.Circuit
import SP1Chips.ShiftLeft.ShiftLeftChip
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridges for `ShiftLeftChip` variants
(`sll`, `sllw`).

Mirrors `SP1Clean/Chips/ALU/LtChip/SailBridge.lean`. The chip's
`Assertion.FormalSpec` (`Chips/Spec.lean`) carries the structural
sub-circuit bundle + inline shift gates; the per-row monadic Sail
equivalence to `_root_.Sll.Poly.spec_sll` / `_root_.Sllw.Poly.spec_sllw`
is recovered on demand here. Each bridge composes:
- `fromMain_toMain` (round-trip on the cols struct, conditional on the
  UserMode TrustMode marker from `Assumptions`),
- `allHold_iff_structural` (reconstruct `(ShiftLeft.constraints (toMain cols)).allHold`
  from the chip's `FormalSpec`),
- `_root_.Sll.Poly.correct_sll` / `_root_.Sllw.Poly.correct_sllw` (the
  Main-level Sail-equivalence proofs in `SP1Chips/ShiftLeft/ShiftLeftChip.lean`).

The `imm_c = 0` hypothesis selects the R-type variant: the chip bundles
I-type `slli`/`slliw` (imm_c = 1) into the same trace, so `imm_c` is the
column that distinguishes `sll` from `slli`. `Sll.Poly.correct_sll`
requires `is_sll Main = (Main[62] = 1 ∧ Main[31] = 0)`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeft

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Sail-monadic equivalence to `_root_.Sll.Poly.spec_sll` under the chip's
FormalSpec, on the R-type row (`imm_c = 0`). -/
theorem sail_correct_sll_of_formalSpec
    (cols : ShiftLeftCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_sll : cols.is_sll = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : shiftLeftInitialState_cols cols s) :
    (sp1_shift_left_cols cols).run s =
      (_root_.Sll.Poly.spec_sll (.Regidx (sp1_op_c_cols cols))
                                (.Regidx (sp1_op_b_cols cols))
                                (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_trusted, h_is_real_sum⟩ := h_assumptions
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_sum' : (toMain cols)[62] + (toMain cols)[63] = 1 := h_is_real_sum
  have h_is_sll' : (toMain cols)[62] = 1 := h_is_sll
  have h_imm_c' : (toMain cols)[31] = 0 := h_imm_c
  have h_spec' : Assertion.FormalSpec (fromMain (toMain cols)) := by
    rw [h_round_trip]; exact h_spec
  have h_allHold : (_root_.ShiftLeft.constraints (toMain cols)).allHold :=
    (allHold_iff_structural (toMain cols) h_sum').mpr h_spec'
  have h_correct := _root_.Sll.Poly.correct_sll (toMain cols) s h_allHold
    ⟨h_is_sll', h_imm_c'⟩ h_state
  rw [show sp1_shift_left_cols cols = _root_.ShiftLeft.sp1_shift_left (toMain cols) from rfl]
  exact h_correct.symm

/-- Sail-monadic equivalence to `_root_.Sllw.Poly.spec_sllw` under the chip's
FormalSpec, on the R-type row (`imm_c = 0`). -/
theorem sail_correct_sllw_of_formalSpec
    (cols : ShiftLeftCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_sllw : cols.is_sllw = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : shiftLeftInitialState_cols cols s) :
    (sp1_shift_left_cols cols).run s =
      (_root_.Sllw.Poly.spec_sllw (.Regidx (sp1_op_c_cols cols))
                                  (.Regidx (sp1_op_b_cols cols))
                                  (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_trusted, h_is_real_sum⟩ := h_assumptions
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_sum' : (toMain cols)[62] + (toMain cols)[63] = 1 := h_is_real_sum
  have h_is_sllw' : (toMain cols)[63] = 1 := h_is_sllw
  have h_imm_c' : (toMain cols)[31] = 0 := h_imm_c
  have h_spec' : Assertion.FormalSpec (fromMain (toMain cols)) := by
    rw [h_round_trip]; exact h_spec
  have h_allHold : (_root_.ShiftLeft.constraints (toMain cols)).allHold :=
    (allHold_iff_structural (toMain cols) h_sum').mpr h_spec'
  have h_correct := _root_.Sllw.Poly.correct_sllw (toMain cols) s h_allHold
    ⟨h_is_sllw', h_imm_c'⟩ h_state
  rw [show sp1_shift_left_cols cols = _root_.ShiftLeft.sp1_shift_left (toMain cols) from rfl]
  exact h_correct.symm

end SP1Clean.ShiftLeft
