import Clean.Circuit.WitnessGeneration
import Clean.Circuit.Subcircuit

/-! # The witgen bridge: honest witness generation for chip rows

Phase 0 of the completeness programme. A chip's `completeness` field says "*any* environment
consistent with my witness generators satisfies my constraints"; it never exhibits such an
environment. Clean's array-backed interpreter `Circuit.witgen` does exhibit one, and
`Circuit.witgen_usesLocalWitnesses` proves it honest — but only for circuits satisfying
`Circuit.ComputableWitnesses`, i.e. whose generators read the environment strictly below the row's
starting offset.

This module holds the shared machinery for discharging that obligation chip by chip. The only real
content per chip is its own witness payload; every composed reader and arithmetic gadget is
zero-witness, and `forAll_witnessCongr_of_localLength_zero` dispatches those without unfolding them
(which matters: unfolding the reader subcircuits is exactly the elaboration blow-up the repo's
folding doctrine exists to avoid).

**Scope note.** `ProverEnvironment.fromArray` hard-codes empty committed `ProverData`
(`Clean/Circuit/WitnessGeneration.lean`, which defers the data-carrying variant to "a later phase").
SP1's chips read no `env.data`, so their honesty proofs are unaffected; transferring the resulting
`ConstraintsHold` to a *table* environment (`Environment.fromArray row data`, which carries real
data) is the step that wants Clean's data-carrying `witgen`, and is drafted as an upstream patch. -/

namespace SP1Clean.Witgen

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
    ∀ (ops : List (FlatOperation F)) (n : ℕ), FlatOperation.localLength ops = 0 →
      FlatOperation.forAll n
        { witness := fun offset _ compute => P offset → Q → compute.eval env = compute.eval env' }
        ops := by
  intro ops
  induction ops with
  | nil => intro n _; trivial
  | cons op ops ih =>
    intro n h
    cases op with
    | witness m c =>
      simp only [FlatOperation.localLength, Nat.add_eq_zero_iff] at h
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
    FlatOperation.forAll n
      { witness := fun offset _ compute => P offset → Q → compute.eval env = compute.eval env' }
      s.ops.toFlat :=
  forAll_witnessCongr_of_localLength_zero _ _ (by rw [← s.localLength_eq, h])

end SP1Clean.Witgen
