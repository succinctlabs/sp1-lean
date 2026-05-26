import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Subcircuit
import Clean.Gadgets.IsZeroField
import Clean.Utils.Field
import Clean.Utils.Tactics.ProvableStructDeriving
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
- `iff_sp1` — the equivalence between SP1's `allHold` and the
  Clean Spec, witnessed by an inverse column.
- `Assertion.{Inputs, main, Spec, assertion}` — verification form mirroring
  `IsZeroWordOp.assertion` shape: inputs `{a, inverse, result}` with 3 gates
  matching `IsZeroOperation.constraints` under `is_real = 1`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

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
      (IsZeroOperation.constraints (F := ZMod p) a ⟨inverse, result⟩ 1).allHold) ↔
    Spec a result := by
  simp only [IsZeroOperation.constraints, SP1ConstraintList.allHold, List.Forall,
    SP1Constraint.toProp, Spec]
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

/-! ## `Assertion` form — verification-style `FormalAssertion`

The witness-form `FormalCircuit` above synthesizes `result` from an inverse;
this `Assertion` form takes a pre-witnessed `(inverse, result)` pair and
verifies the 3-gate IsZero contract holds. Used by chip-level `main`s that
allocate the IsZero columns themselves (e.g. `MemoryGlobalChip`). -/

namespace Assertion

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled FormalAssertion input: input `a`, witnessed `inverse` and
`result`. Mirrors SP1's `IsZeroOperation.constraints (F := F) a ⟨inverse,
result⟩ is_real` calling convention with `is_real` baked in as 1. -/
structure Inputs (F : Type) where
  a : F
  inverse : F
  result : F
deriving ProvableStruct

/-- Clean-side circuit. Emits the 3 IsZero contract gates un-gated (i.e.,
the caller is responsible for `is_real = 1` composition). Matches
`IsZeroOperation.constraints` from SP1 verbatim under `is_real = 1`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let one_expr : Expression (ZMod p) := 1
  (one_expr - input.inverse * input.a - input.result) === 0
  input.result * (input.result - 1) === 0
  input.result * input.a === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.IsZeroOp"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Spec: the 3-gate IsZero contract. `result = 1` iff `a = 0` is implied
but not stated explicitly — derive via `IsZeroOperation.spec` when needed. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  ((1 : ZMod p) - input.inverse * input.a - input.result = 0) ∧
  (input.result * (input.result - 1) = (0 : ZMod p)) ∧
  (input.result * input.a = (0 : ZMod p))

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a, h_inv, h_res⟩ := h_input
  subst_eqs
  simp only [Spec, sub_eq_add_neg]
  exact h_holds

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a, h_inv, h_res⟩ := h_input
  subst_eqs
  simp only [Spec, sub_eq_add_neg] at h_spec
  exact h_spec

end Assertion

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The full Clean `FormalAssertion` for `IsZeroOperation`. -/
def assertion : FormalAssertion (ZMod p) Assertion.Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.IsZeroOp
