import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Clean.AddOperation
import SP1Clean.Gated

/-! # `GatedAddOp` — gated form of `AddOp.assertion`

First concrete instance of the gating pattern documented in
`SP1Clean/Gated.lean`. Takes the same `(a, b, result)` triple as
`SP1Clean.AddOp.assertion`, plus an extra `gate : F` field, and emits
the four carry-boolean asserts **multiplied by `gate`**. The four
`Range(16)` result-limb lookups that the ungated `AddOp.assertion`
emits are **dropped here** — gating a lookup by field multiplication is
not sound (see `SP1Clean/Gated.lean` for the lookup-restriction
discussion). Range checks on the result limbs live in the consuming
chip's legacy `Spec`.

The `FormalSpec` is `gate = 0 ∨ <carry-only Spec>`. On padding rows
where the chip's gate evaluates to 0, the disjunction's left branch
fires vacuously; on real rows, the inner carry-boolean spec holds.

Used by `SP1Clean.Jalr.Assertion.main` for the `is_real`-gated
jump-target sum.
-/

namespace SP1Clean.GatedAddOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Carry-only Spec for a 4-limb gated add. Same shape as
`SP1Clean.AddOp.Spec` minus the four result-limb range bounds. The
range bounds belong to the consuming chip's legacy `Spec` (carried by
the chip's `iff_sp1` or a separate trace-level constraint). -/
def Spec (a b result : Word (ZMod p)) : Prop :=
  let c0 : ZMod p := (a[0] + b[0] - result[0]) * 65536⁻¹
  let c1 : ZMod p := (a[1] + b[1] - result[1] + c0) * 65536⁻¹
  let c2 : ZMod p := (a[2] + b[2] - result[2] + c1) * 65536⁻¹
  let c3 : ZMod p := (a[3] + b[3] - result[3] + c2) * 65536⁻¹
  (c0 = 0 ∨ c0 = 1) ∧
  (c1 = 0 ∨ c1 = 1) ∧
  (c2 = 0 ∨ c2 = 1) ∧
  (c3 = 0 ∨ c3 = 1)

/-- Bundled input to the gated FormalAssertion: the two operand words,
the result word, and the gate scalar. -/
structure Inputs (F : Type) where
  a : fields 4 F
  b : fields 4 F
  result : fields 4 F
  gate : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Gated `main`: emits `gate * (c_k * (c_k - 1)) === 0` for each of the
four carries. **No lookups** — see the file docstring. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let b := input.b
  let result := input.result
  let gate := input.gate
  let c0 := (a[0] + b[0] - result[0]) * (65536 : ZMod p)⁻¹
  let c1 := (a[1] + b[1] - result[1] + c0) * (65536 : ZMod p)⁻¹
  let c2 := (a[2] + b[2] - result[2] + c1) * (65536 : ZMod p)⁻¹
  let c3 := (a[3] + b[3] - result[3] + c2) * (65536 : ZMod p)⁻¹
  gate * (c0 * (c0 - 1)) === 0
  gate * (c1 * (c1 - 1)) === 0
  gate * (c2 * (c2 - 1)) === 0
  gate * (c3 * (c3 - 1)) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.GatedAddOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec: either the gate is zero (vacuous), or
the underlying carry-only `Spec` holds. -/
def FormalSpec (input : Inputs (ZMod p)) : Prop :=
  input.gate = 0 ∨ SP1Clean.GatedAddOp.Spec input.a input.b input.result

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_g_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  subst h_g_eq
  obtain ⟨h_c0, h_c1, h_c2, h_c3⟩ := h_holds
  simp only [FormalSpec, SP1Clean.GatedAddOp.Spec, Vector.getElem_map]
  unfold id at *
  -- For each gated carry: either the gate is zero (propagate via Or.inl), or
  -- the inner carry equation holds.
  obtain h_g | h_c0' := mul_eq_zero.mp h_c0
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_c1' := mul_eq_zero.mp h_c1
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_c2' := mul_eq_zero.mp h_c2
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_c3' := mul_eq_zero.mp h_c3
  · exact Or.inl (by linear_combination h_g)
  -- All four gate factors were nonzero, so each inner `c_k * (c_k - 1) = 0`
  -- holds — conclude the inner carry-Spec.
  refine Or.inr ⟨?_, ?_, ?_, ?_⟩
  · obtain h | h := mul_eq_zero.mp h_c0'
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_c1'
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_c2'
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_c3'
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_g_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  subst h_g_eq
  unfold id at *
  rcases h_spec with h_gate | h_spec'
  · -- gate = 0: every `gate * _ = 0` trivially. `dsimp only at h_gate` reduces
    -- the `{record}.gate` projection introduced by `circuit_proof_start`'s
    -- substitution into the eval form, so `rw [h_gate]` matches the goal.
    dsimp only at h_gate
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals (rw [h_gate]; ring)
  · -- inner Spec holds: each `c_k * (c_k - 1) = 0`, multiply by gate
    dsimp only at h_spec'
    simp only [SP1Clean.GatedAddOp.Spec, Vector.getElem_map, sub_eq_add_neg] at h_spec'
    obtain ⟨hb0, hb1, hb2, hb3⟩ := h_spec'
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hb0 with h | h <;> rw [h] <;> ring
    · rcases hb1 with h | h <;> rw [h] <;> ring
    · rcases hb2 with h | h <;> rw [h] <;> ring
    · rcases hb3 with h | h <;> rw [h] <;> ring

end Assertion

/-- The gated `FormalAssertion`. Compose into a chip's `Assertion.main`
via `SP1Clean.GatedAddOp.assertion ⟨a, b, result, gate⟩`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.GatedAddOp
