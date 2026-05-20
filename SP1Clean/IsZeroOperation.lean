import Clean.Gadgets.IsZeroField
import Clean.Utils.Field
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Compare.IsZeroOperation.Operation
import SP1Operations.Compare.IsZeroOperation.Constraints

/-! # Tier 1 pilot: `IsZeroOperation` mirror — full `FormalCircuit` form

SP1's `IsZeroOperation` is a 3-constraint, no-interaction fragment. Clean's
upstream `Gadgets.IsZeroField` (`clean/Clean/Gadgets/IsZeroField.lean:7-46`)
is a direct match in both shape and Spec, so we **re-export the upstream
circuit** as the canonical Clean side and only contribute the bridge.

Deliverables for the pilot:
- `circuit : FormalCircuit (ZMod p) field field` — Clean-side soundness +
  completeness, inherited from upstream.
- `iff_sp1` — the equivalence between SP1's `allHold_poly` and the
  Clean Spec, witnessed by an inverse column.
-/

namespace SP1Clean.IsZeroOp

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- Clean `FormalCircuit` for `IsZeroOperation`, re-exported from
`Gadgets.IsZeroField`. Spec: `output = 1 ⟺ a = 0`. -/
def circuit : FormalCircuit (ZMod p) field field :=
  Gadgets.IsZeroField.circuit

/-- Pilot Spec mirroring `Gadgets.IsZeroField.Spec`. -/
def Spec (a result : ZMod p) : Prop :=
  result = if a = 0 then 1 else 0

omit [Fact (p > 512)] in
/-- The bridge to SP1.

Reads: "for the prover to satisfy SP1's IsZero constraints with output column
`result`, there must exist an inverse column witnessing `a`'s (non-)zeroness,
exactly when the result column matches the Clean spec." -/
theorem iff_sp1 (a result : ZMod p) :
    (∃ inverse : ZMod p,
      (IsZeroOperation.constraints (F := ZMod p) a ⟨inverse, result⟩ 1).allHold_poly) ↔
    Spec a result := by
  simp only [IsZeroOperation.constraints, SP1ConstraintList.allHold_poly, List.Forall,
    SP1Constraint.toProp_poly, Spec]
  constructor
  · rintro ⟨inv, hr, _hbool, hra⟩
    have hr' : 1 - inv * a - result = 0 := by linear_combination hr
    have hra' : result * a = 0 := by linear_combination hra
    by_cases ha : a = 0
    · simp [ha] at hr'
      simp [ha]
      linear_combination -hr'
    · simp [ha]
      rcases mul_eq_zero.mp hra' with h | h
      · exact h
      · exact absurd h ha
  · intro hspec
    by_cases ha : a = 0
    · refine ⟨0, ?_, ?_, ?_⟩ <;> simp [ha, hspec]
    · refine ⟨a⁻¹, ?_, ?_, ?_⟩
      · have hr0 : result = 0 := by simp [hspec, ha]
        rw [hr0]
        field_simp
        ring
      · simp [hspec, ha]
      · have : result = 0 := by simp [hspec, ha]
        rw [this]; ring

omit [Fact (p > 512)] in
/-- Verifies that the Clean circuit's `Spec` matches our pilot `Spec`. This
ties the inherited soundness/completeness from `Gadgets.IsZeroField` to the
naming we use throughout `SP1Clean`. -/
theorem circuit_Spec_eq_Spec :
    (circuit (p := p)).Spec = Spec :=
  rfl

end SP1Clean.IsZeroOp
