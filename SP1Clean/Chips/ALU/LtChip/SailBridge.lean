import SP1Clean.Chips.ALU.LtChip.Circuit
import SP1Chips.Lt.LtChip
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridge for `LtChip`

Mirrors `SP1Clean/Chips/ALU/AddChip/SailBridge.lean` for the 2-variant
case (`slt` + `sltu`).

The chip's `Assertion.FormalSpec` (`Chips/Spec.lean`) carries the
structural sub-circuit bundle; the per-row monadic Sail equivalence to
`_root_.Slt.spec_slt` / `_root_.Sltu.spec_sltu` is recovered on demand
here. Each bridge composes:
- `fromMain_toMain` (round-trip on the cols struct, conditional on the
  UserMode TrustMode marker from `Assumptions`),
- `allHold_iff_structural` (reconstruct `(Lt.constraints (toMain cols)).allHold`
  from the chip's `FormalSpec`),
- `_root_.Slt.correct_slt` / `_root_.Sltu.correct_sltu` (the Main-level
  Sail-equivalence proofs in `SP1Chips/Lt/LtChip.lean`).

The `imm_c = 0` hypothesis selects the R-type variant: the Lt chip
bundles I-type `slti`/`sltiu` (imm_c = 1) into the same trace, so
`imm_c` is the column that distinguishes `slt` from `slti`. The
underlying `Slt.correct_slt` requires `is_slt Main = (Main[32] = 1 ∧
Main[31] = 0)`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Lt

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Sail-monadic equivalence to `_root_.Slt.spec_slt` under the chip's
FormalSpec, on the R-type row (`imm_c = 0`). -/
theorem sail_correct_slt_of_formalSpec
    (cols : LtCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_slt : cols.is_slt = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : ltInitialState_cols cols s) :
    (sp1_lt_cols cols).run s =
      (_root_.Slt.spec_slt (.Regidx (sp1_op_c_cols cols))
                           (.Regidx (sp1_op_b_cols cols))
                           (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_trusted, h_is_real_sum⟩ := h_assumptions
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  -- `(toMain cols)[32] = cols.is_slt`, `(toMain cols)[33] = cols.is_sltu`,
  -- `(toMain cols)[31] = cols.adapter.imm_c` reduce by `@[reducible]` toMain.
  have h_sum' : (toMain cols)[32] + (toMain cols)[33] = 1 := h_is_real_sum
  have h_is_slt' : (toMain cols)[32] = 1 := h_is_slt
  have h_imm_c' : (toMain cols)[31] = 0 := h_imm_c
  -- Reconstruct SP1's `allHold` on `toMain cols` from the `FormalSpec`,
  -- re-stated through `fromMain (toMain cols) ≡ cols`.
  have h_spec' : Assertion.FormalSpec (fromMain (toMain cols)) := by
    rw [h_round_trip]; exact h_spec
  have h_allHold : (_root_.Lt.constraints (toMain cols)).allHold :=
    (allHold_iff_structural (toMain cols) h_sum').mpr h_spec'
  -- Apply Main-level `Slt.correct_slt`; the result reads `Slt.sp1_X (toMain cols)`,
  -- which is definitionally `sp1_X_cols cols` after the round-trip.
  have h_correct := _root_.Slt.correct_slt (toMain cols) s h_allHold
    ⟨h_is_slt', h_imm_c'⟩ h_state
  -- `sp1_lt_cols cols = Lt.sp1_lt (toMain cols)` and `sp1_op_X_cols cols =
  -- Slt.sp1_op_X (toMain cols)` by `@[reducible]` defeq.
  rw [show sp1_lt_cols cols = _root_.Lt.sp1_lt (toMain cols) from rfl]
  exact h_correct.symm

/-- Sail-monadic equivalence to `_root_.Sltu.spec_sltu` under the chip's
FormalSpec, on the R-type row (`imm_c = 0`). -/
theorem sail_correct_sltu_of_formalSpec
    (cols : LtCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_sltu : cols.is_sltu = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : ltInitialState_cols cols s) :
    (sp1_lt_cols cols).run s =
      (_root_.Sltu.spec_sltu (.Regidx (sp1_op_c_cols cols))
                             (.Regidx (sp1_op_b_cols cols))
                             (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_trusted, h_is_real_sum⟩ := h_assumptions
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_sum' : (toMain cols)[32] + (toMain cols)[33] = 1 := h_is_real_sum
  have h_is_sltu' : (toMain cols)[33] = 1 := h_is_sltu
  have h_imm_c' : (toMain cols)[31] = 0 := h_imm_c
  have h_spec' : Assertion.FormalSpec (fromMain (toMain cols)) := by
    rw [h_round_trip]; exact h_spec
  have h_allHold : (_root_.Lt.constraints (toMain cols)).allHold :=
    (allHold_iff_structural (toMain cols) h_sum').mpr h_spec'
  have h_correct := _root_.Sltu.correct_sltu (toMain cols) s h_allHold
    ⟨h_is_sltu', h_imm_c'⟩ h_state
  rw [show sp1_lt_cols cols = _root_.Lt.sp1_lt (toMain cols) from rfl]
  exact h_correct.symm

end SP1Clean.Lt
