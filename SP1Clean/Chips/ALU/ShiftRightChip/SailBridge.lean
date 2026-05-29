import SP1Clean.Chips.ALU.ShiftRightChip.Circuit
import SP1Chips.ShiftRight.ShiftRightChip
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridges for `ShiftRightChip` variants
(`srl`, `sra`, `srlw`, `sraw`).

Mirrors `SP1Clean/Chips/ALU/ShiftLeftChip/SailBridge.lean`. The chip's
`Assertion.FormalSpec` (`Chips/Spec.lean`) carries the structural sub-circuit
bundle + inline shift gates; the per-row monadic Sail equivalence to
`_root_.Srl.Poly.spec_srl` etc. is recovered on demand here. Each bridge composes
`fromMain_toMain` (round-trip on the cols struct, conditional on the UserMode
TrustMode marker), `allHold_iff_structural` (reconstruct
`(ShiftRight.constraints (toMain cols)).allHold` from the chip's `FormalSpec`),
and `_root_.Sxx.Poly.correct_*` (the Main-level Sail-equivalence proofs).

The `imm_c = 0` hypothesis selects the R-type variant (vs the I-type
`srli`/`srai`/… which the chip bundles into the same trace). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRight

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Sail-monadic equivalence to `_root_.Srl.Poly.spec_srl` under the chip's
FormalSpec, on the R-type row (`imm_c = 0`). -/
theorem sail_correct_srl_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_srl : cols.is_srl = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : shiftRightInitialState_cols cols s) :
    (sp1_shift_right_cols cols).run s =
      (_root_.Srl.Poly.spec_srl (.Regidx (sp1_op_c_cols cols))
                                (.Regidx (sp1_op_b_cols cols))
                                (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_trusted, h_is_real_sum⟩ := h_assumptions
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_sum' : (toMain cols)[64] + (toMain cols)[65] + (toMain cols)[66] + (toMain cols)[67] = 1 :=
    h_is_real_sum
  have h_is_srl' : (toMain cols)[64] = 1 := h_is_srl
  have h_imm_c' : (toMain cols)[31] = 0 := h_imm_c
  have h_spec' : Assertion.FormalSpec (fromMain (toMain cols)) := by
    rw [h_round_trip]; exact h_spec
  have h_allHold : (_root_.ShiftRight.constraints (toMain cols)).allHold :=
    (allHold_iff_structural (toMain cols) h_sum').mpr h_spec'
  have h_correct := _root_.Srl.Poly.correct_srl (toMain cols) s h_allHold
    ⟨h_is_srl', h_imm_c'⟩ h_state
  rw [show sp1_shift_right_cols cols = _root_.ShiftRight.sp1_shift_right (toMain cols) from rfl]
  exact h_correct.symm

/-- Sail-monadic equivalence to `_root_.Sra.Poly.spec_sra`. -/
theorem sail_correct_sra_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_sra : cols.is_sra = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : shiftRightInitialState_cols cols s) :
    (sp1_shift_right_cols cols).run s =
      (_root_.Sra.Poly.spec_sra (.Regidx (sp1_op_c_cols cols))
                                (.Regidx (sp1_op_b_cols cols))
                                (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_trusted, h_is_real_sum⟩ := h_assumptions
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_sum' : (toMain cols)[64] + (toMain cols)[65] + (toMain cols)[66] + (toMain cols)[67] = 1 :=
    h_is_real_sum
  have h_is_sra' : (toMain cols)[65] = 1 := h_is_sra
  have h_imm_c' : (toMain cols)[31] = 0 := h_imm_c
  have h_spec' : Assertion.FormalSpec (fromMain (toMain cols)) := by
    rw [h_round_trip]; exact h_spec
  have h_allHold : (_root_.ShiftRight.constraints (toMain cols)).allHold :=
    (allHold_iff_structural (toMain cols) h_sum').mpr h_spec'
  have h_correct := _root_.Sra.Poly.correct_sra (toMain cols) s h_allHold
    ⟨h_is_sra', h_imm_c'⟩ h_state
  rw [show sp1_shift_right_cols cols = _root_.ShiftRight.sp1_shift_right (toMain cols) from rfl]
  exact h_correct.symm

/-- Sail-monadic equivalence to `_root_.Srlw.Poly.spec_srlw`. -/
theorem sail_correct_srlw_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_srlw : cols.is_srlw = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : shiftRightInitialState_cols cols s) :
    (sp1_shift_right_cols cols).run s =
      (_root_.Srlw.Poly.spec_srlw (.Regidx (sp1_op_c_cols cols))
                                  (.Regidx (sp1_op_b_cols cols))
                                  (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_trusted, h_is_real_sum⟩ := h_assumptions
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_sum' : (toMain cols)[64] + (toMain cols)[65] + (toMain cols)[66] + (toMain cols)[67] = 1 :=
    h_is_real_sum
  have h_is_srlw' : (toMain cols)[66] = 1 := h_is_srlw
  have h_imm_c' : (toMain cols)[31] = 0 := h_imm_c
  have h_spec' : Assertion.FormalSpec (fromMain (toMain cols)) := by
    rw [h_round_trip]; exact h_spec
  have h_allHold : (_root_.ShiftRight.constraints (toMain cols)).allHold :=
    (allHold_iff_structural (toMain cols) h_sum').mpr h_spec'
  have h_correct := _root_.Srlw.Poly.correct_srlw (toMain cols) s h_allHold
    ⟨h_is_srlw', h_imm_c'⟩ h_state
  rw [show sp1_shift_right_cols cols = _root_.ShiftRight.sp1_shift_right (toMain cols) from rfl]
  exact h_correct.symm

/-- Sail-monadic equivalence to `_root_.Sraw.Poly.spec_sraw`. -/
theorem sail_correct_sraw_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_sraw : cols.is_sraw = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : shiftRightInitialState_cols cols s) :
    (sp1_shift_right_cols cols).run s =
      (_root_.Sraw.Poly.spec_sraw (.Regidx (sp1_op_c_cols cols))
                                  (.Regidx (sp1_op_b_cols cols))
                                  (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_trusted, h_is_real_sum⟩ := h_assumptions
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_sum' : (toMain cols)[64] + (toMain cols)[65] + (toMain cols)[66] + (toMain cols)[67] = 1 :=
    h_is_real_sum
  have h_is_sraw' : (toMain cols)[67] = 1 := h_is_sraw
  have h_imm_c' : (toMain cols)[31] = 0 := h_imm_c
  have h_spec' : Assertion.FormalSpec (fromMain (toMain cols)) := by
    rw [h_round_trip]; exact h_spec
  have h_allHold : (_root_.ShiftRight.constraints (toMain cols)).allHold :=
    (allHold_iff_structural (toMain cols) h_sum').mpr h_spec'
  have h_correct := _root_.Sraw.Poly.correct_sraw (toMain cols) s h_allHold
    ⟨h_is_sraw', h_imm_c'⟩ h_state
  rw [show sp1_shift_right_cols cols = _root_.ShiftRight.sp1_shift_right (toMain cols) from rfl]
  exact h_correct.symm

end SP1Clean.ShiftRight
