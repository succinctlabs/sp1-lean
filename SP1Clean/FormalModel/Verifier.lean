import SP1Clean.FormalModel.Relations

/-! # The proof-system boundary

AIR soundness and verifier knowledge soundness are different theorems.  The former is a deterministic
refinement between witness relations; the latter says that an accepting (possibly probabilistic and
oracle-using) proof admits extraction.  ArkLib owns the second notion.  This dependency-free file
isolates the deterministic facts an ArkLib adapter needs. Existential extraction can be
post-processed through a witness-producing refinement. ArkLib's current straight-line
knowledge-soundness game instead keeps the input-witness type fixed, so its direct adapter widens the
AIR relation to `FunctionalRefinement.targetPreimage` and maps the extracted witness afterward.

The eventual ArkLib module should instantiate its input relation with `WitnessRelation.asSet`, prove
the generic relation-monotonicity lemma shown below, and use
`FunctionalRefinement.source_subset_targetPreimage`. It should name the resulting SP1-specific
knowledge/execution theorem `sp1_verifier_sound`; that name is intentionally not used for the AIR
theorem. Existential `WitnessRelation.Sound` remains useful as a propositional corollary, but it is
not a sufficient extraction API.

Everything here (`PerfectExtraction` and its `refine`/`refineFunctional` lemmas) is reserved
API for that ArkLib adapter — unreferenced in-tree by design until it exists. -/

namespace SP1Clean.VerifierBoundary

/-- A deterministic, perfect-extraction analogue of ArkLib knowledge soundness.  It is useful for
testing relation composition locally, but is not a replacement for ArkLib's probabilistic definition. -/
def PerfectExtraction {Statement Certificate Witness : Type}
    (accepts : Statement → Certificate → Prop)
    (relation : WitnessRelation.Relation Statement Witness) : Prop :=
  ∀ statement certificate, accepts statement certificate →
    ∃ witness, relation statement witness

/-- Post-process an existentially extracted AIR witness into a semantic execution witness. ArkLib's
knowledge-soundness game has a more structured witness-typed interface; its corresponding adapter is
the target-preimage construction described below. -/
theorem PerfectExtraction.refine {Statement Certificate Witness₁ Witness₂ : Type}
    {accepts : Statement → Certificate → Prop}
    {relation₁ : WitnessRelation.Relation Statement Witness₁}
    {relation₂ : WitnessRelation.Relation Statement Witness₂}
    (extracts : PerfectExtraction accepts relation₁)
    (sound : WitnessRelation.Sound relation₁ relation₂) :
    PerfectExtraction accepts relation₂ := by
  intro statement certificate accepted
  obtain ⟨witness₁, valid₁⟩ := extracts statement certificate accepted
  exact sound statement witness₁ valid₁

/-- Post-process an existentially extracted witness through the constructive AIR-refinement map. No
witness is selected with choice, and the same validity proof both computes and authenticates the
resulting execution witness. -/
theorem PerfectExtraction.refineFunctional {Statement Certificate Witness₁ Witness₂ : Type}
    {accepts : Statement → Certificate → Prop}
    {relation₁ : WitnessRelation.Relation Statement Witness₁}
    {relation₂ : WitnessRelation.Relation Statement Witness₂}
    (extracts : PerfectExtraction accepts relation₁)
    (refinement : WitnessRelation.FunctionalRefinement relation₁ relation₂) :
    PerfectExtraction accepts relation₂ := by
  intro statement certificate accepted
  obtain ⟨witness₁, valid₁⟩ := extracts statement certificate accepted
  exact ⟨refinement.map statement witness₁,
    refinement.map_valid statement witness₁ valid₁⟩

/-! ## ArkLib instantiation target

At the audited ArkLib revision, `knowledgeSoundness` uses `WitIn` both as the extractor's result and
as the malicious prover's private-input type. Therefore changing from an AIR witness to a semantic
witness is not definitionally just post-composing the extractor. The direct, error-preserving adapter
keeps the AIR-witness type and widens its relation to the semantic target's preimage:

```lean
theorem sp1_verifier_sound
    (airRefinement : WitnessRelation.FunctionalRefinement
      (CoreAIR.Current.Relation preprocessedBinding .execution)
      (Execution.SP1CoreShardExecutionRelation .base handler programBinding))
    (hVerifier : verifier.knowledgeSoundness init impl
      (WitnessRelation.asSet (CoreAIR.Current.Relation preprocessedBinding .execution))
      acceptRejectRel knowledgeError) :
    verifier.knowledgeSoundness init impl
      (WitnessRelation.asSet
        airRefinement.targetPreimage)
      acceptRejectRel knowledgeError := by
  exact knowledgeSoundness_relIn_mono
    airRefinement.source_subset_targetPreimage hVerifier
```

Here `knowledgeSoundness_relIn_mono` is the small ArkLib-side theorem that a straight-line extractor
remains sound when its input relation is widened; its proof reuses the same extractor and applies
`probEvent_mono`, so the knowledge error is unchanged. A consumer maps a successfully extracted AIR
witness with `airRefinement.map`, and target-preimage membership authenticates that semantic witness.

This belongs in the ArkLib integration layer, not in `sp1_air_sound`: the latter proves the
deterministic refinement premise and says nothing about Fiat–Shamir, commitments, query soundness, or
the probability of extractor failure. -/

end SP1Clean.VerifierBoundary
