module

public import SP1Clean.Semantics.Specs.IsZero
public import SP1Clean.Math.Word
public import ToClean.Circuit.IteDecide
public import Clean.Gadgets.Equality
import Clean.Utils.Tactics.CircuitProofStart

/-! # Field zero-test gadget

Native witness generation, arithmetic lemmas and the bundled `FormalAssertion` live together.
The semantic contract is in `Semantics/Specs/IsZero`. `AssertSpec` is the structural relation
used by the transitional Rust-faithfulness proofs; it is distinct from the public semantic `Spec`.
-/

@[expose] public section

namespace SP1Clean.IsZeroOperation

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- The inverse and zero-indicator witness, with zero inverse when the input is zero. -/
def populate (a : ZMod p) : Circuits.Types.IsZeroOperation (ZMod p) :=
  if a = 0 then ⟨0, 1⟩ else ⟨a⁻¹, 0⟩

section FE

/-- The witness-IR twin of `populate`: `⟨x⁻¹, if x = 0 then 1 else 0⟩` (the IR's `.inv` shares
the `0⁻¹ = 0` convention, so the inverse cell needs no dispatch). -/
def populateFE (x : Witgen.FExpr (ZMod p)) : Circuits.Types.IsZeroOperation (Witgen.FExpr (ZMod p)) :=
  ⟨.inv x, .ite (x =? (0 : ZMod p)) 1 0⟩

/-- Evaluating the twin is `populate` on the evaluated operand. -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p)) (x : Witgen.FExpr (ZMod p))
    (v : ZMod p) (hx : Witgen.FExpr.eval { env := env } x = v) :
    Witgen.eval { env := env } (populateFE x) = populate v := by
  by_cases hv : v = 0 <;>
    simp [populateFE, populate, circuit_norm, explicit_provable_type, hx, hv,
      Witgen.StructEval.eval.go, ProvableStruct.toComponents, ProvableStruct.fromComponents]

/-- Environment-locality of the twin. -/
theorem populateFE_congr (env env' : ProverEnvironment (ZMod p)) (x : Witgen.FExpr (ZMod p))
    (hx : Witgen.FExpr.eval { env := env } x = Witgen.FExpr.eval { env := env' } x) :
    Witgen.eval { env := env } (populateFE x) = Witgen.eval { env := env' } (populateFE x) := by
  simp [populateFE, circuit_norm, explicit_provable_type, hx,
    Witgen.StructEval.eval.go, ProvableStruct.toComponents, ProvableStruct.fromComponents]

end FE

/-- **Assertion half** — the literal meaning of SP1's `IsZeroOperation` `asserts` list at
`is_real = 1`, stated against the result columns: `result = 1 - inverse*a`, `result` boolean, and
`result * a = 0`. (`IsZero` has no bus interactions, so this is the whole structural spec.) -/
def AssertSpec (a : ZMod p) (cols : Circuits.Types.IsZeroOperation (ZMod p)) : Prop :=
  ((1 - cols.inverse * a) - cols.result = 0) ∧
  (cols.result = 0 ∨ cols.result = 1) ∧
  (cols.result * a = 0)

/-- Soundness core: `AssertSpec` forces `result` to be the zero indicator of `a`. On `a = 0` the
defining equation gives `result = 1`; on `a ≠ 0` the `result * a = 0` constraint forces `result = 0`
(via `mul_inv_cancel₀`, since `mul_eq_zero` won't fire on `ZMod p`). -/
theorem isZero_of_assert {a : ZMod p} {cols : Circuits.Types.IsZeroOperation (ZMod p)}
    (h_assert : AssertSpec a cols) :
    cols.result = if a = 0 then 1 else 0 := by
  obtain ⟨h_eq, _, h_mul⟩ := h_assert
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    linear_combination -h_eq
  · rw [if_neg ha]
    calc cols.result = cols.result * (a * a⁻¹) := by rw [mul_inv_cancel₀ ha, mul_one]
      _ = cols.result * a * a⁻¹ := by ring
      _ = 0 := by rw [h_mul, zero_mul]

/-- On `a ≠ 0`, `AssertSpec` pins `inverse` to `a⁻¹` (the defining equation with `result = 0`). The
composing word-level completeness needs this to reconstruct the gated inverse column. -/
theorem inverse_of_assert {a : ZMod p} {cols : Circuits.Types.IsZeroOperation (ZMod p)}
    (h_assert : AssertSpec a cols) (ha : a ≠ 0) : cols.inverse * a = 1 := by
  have hr : cols.result = 0 := by
    have := isZero_of_assert h_assert; rwa [if_neg ha] at this
  obtain ⟨h_eq, _, _⟩ := h_assert
  rw [hr] at h_eq
  linear_combination -h_eq
/-- Assert the inverse relation, binary result and zero product, gated by the activity flag. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let cols := input.cols
  let is_real := input.is_real
  let E0 := cols.inverse * a
  let E1 := 1 - E0
  let E2 := E1 - cols.result
  let E3 := is_real * E2
  let E4 := cols.result - 1
  let E5 := cols.result * E4
  let E6 := is_real * E5
  let E7 := cols.result * a
  let E8 := is_real * E7
  E3 === 0
  E6 === 0
  E8 === 0

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := []
  }

@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [] := rfl
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  intro hr1
  simp only [circuit_norm, hr1, one_mul] at h_holds
  obtain ⟨h_eq, h_bool, h_mul⟩ := h_holds
  have hA : AssertSpec input_a ⟨input_cols_inverse, input_cols_result⟩ :=
    ⟨by simpa [sub_eq_add_neg] using h_eq,
      bool_of_mul_pred (by simpa only [sub_eq_add_neg] using h_bool), h_mul⟩
  exact ⟨isZero_of_assert hA, inverse_of_assert hA⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  rcases h_assumptions with h0 | h1
  · simp [circuit_norm, h0]
  · obtain ⟨hres, hinv⟩ := h_spec h1
    simp only [circuit_norm, h1, one_mul]
    refine ⟨?_, ?_, ?_⟩
    · by_cases ha : input_a = 0
      · simp [hres, ha]
      · rw [hres, if_neg ha, hinv ha]; simp
    all_goals (rw [hres]; by_cases ha : input_a = 0 <;> simp [ha])

/-- The result `populate a` satisfies the gadget `Spec` for any `is_real`. The composing word-level
op uses this (per limb) to discharge the `assertion IsZeroOperation.circuit` prover obligation. -/
theorem spec_populate (a is_real : ZMod p) :
    Spec (⟨a, populate a, is_real⟩ : Inputs (ZMod p)) := by
  intro _
  by_cases ha : a = 0
  · subst ha; exact ⟨by simp [populate], fun hne => absurd rfl hne⟩
  · refine ⟨by simp [populate, ha], fun _ => ?_⟩
    simp only [populate, if_neg ha]; exact inv_mul_cancel₀ ha

/-- SP1's `IsZeroOperation::eval` as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.IsZeroOperation
