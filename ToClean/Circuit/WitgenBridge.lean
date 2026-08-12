import Clean.Circuit.WitnessGeneration
import Clean.Circuit.Subcircuit

/-! # Composition lemmas for `ComputableWitnesses`

A circuit's `completeness` field says "*any* environment consistent with my witness generators
satisfies my constraints"; it never exhibits such an environment. Clean's array-backed interpreter
`Circuit.witgen` does exhibit one, and `Circuit.witgen_usesLocalWitnesses` proves it honest — but
only for circuits satisfying `Circuit.ComputableWitnesses`, i.e. whose generators read the
environment strictly below the circuit's starting offset.

Clean supplies `FormalCircuitBase.compose_computableWitnesses` for children that *carry* a
`ComputableWitnesses` field, but a `FormalAssertion` or `GeneralFormalCircuit` child carries no such
field. The lemmas here close that hole for the common case — a child that witnesses **no cells at
all** satisfies any witness-congruence condition vacuously, and can therefore be dispatched by its
`localLength` alone, with no unfolding of its operations. Unfolding composed children is precisely
the elaboration blow-up that makes these proofs intractable at scale, so avoiding it is the point.

## Upstream

Destined for `Clean/Circuit/Subcircuit.lean`, beside `compose_computableWitnesses`. Clean has
exactly one `ComputableWitnesses` instance in tree (`Gadgets/Addition8/Addition8FullCarry.lean`),
which has no subcircuits and so never needs this; any composed circuit does. -/

namespace FlatOperation

open Circuit

variable {F : Type} [FiniteField F]

/-- A zero-witness operation list satisfies any witness-*congruence* condition vacuously: each of its
witness operations produces a `Vector F 0`, and all of those are equal.

This is the lemma that keeps a chip's `ComputableWitnesses` proof proportional to the witnesses the
chip actually declares: the composed readers and gadgets contribute no cells, so their flattened
operation lists are dispatched by their `localLength`, with no unfolding.

The two premise families `P`/`Q` are left abstract so the statement matches
`FormalCircuitBase.ComputableWitnesses`'s condition (an offset-indexed environment-agreement premise,
then a closed input-agreement premise) without naming it. -/
theorem forAll_witnessCongr_of_localLength_zero {env env' : ProverEnvironment F}
    {P : ℕ → Prop} {Q : Prop} :
    ∀ (ops : List (FlatOperation F)) (n : ℕ), localLength ops = 0 →
      forAll n
        { witness := fun offset _ compute => P offset → Q → compute.eval env = compute.eval env' }
        ops := by
  intro ops
  induction ops with
  | nil => intro n _; trivial
  | cons op ops ih =>
    intro n h
    cases op with
    | witness m c =>
      simp only [localLength, Nat.add_eq_zero_iff] at h
      obtain ⟨hm, hops⟩ := h
      subst hm
      refine ⟨fun _ _ => ?_, ih _ hops⟩
      apply Vector.ext
      omega
    | assert e => exact ⟨trivial, ih _ h⟩
    | lookup l => exact ⟨trivial, ih _ h⟩
    | interact i => exact ⟨trivial, ih _ h⟩

/-- The same, for a composed subcircuit: read its cell count off `localLength` (which `circuit_norm`
computes from the child's own `localLength_eq`) instead of unfolding its operations. -/
theorem forAll_witnessCongr_of_subcircuit {env env' : ProverEnvironment F}
    {P : ℕ → Prop} {Q : Prop} {m : ℕ} (s : Subcircuit F m) (n : ℕ) (h : s.localLength = 0) :
    forAll n
      { witness := fun offset _ compute => P offset → Q → compute.eval env = compute.eval env' }
      s.ops.toFlat :=
  forAll_witnessCongr_of_localLength_zero _ _ (by rw [← s.localLength_eq, h])

end FlatOperation
