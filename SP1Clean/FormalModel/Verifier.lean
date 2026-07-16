import SP1Clean.FormalModel.Relations

/-! # The proof-system boundary

AIR soundness and verifier knowledge soundness are different theorems.  The former is a deterministic
refinement between witness relations; the latter says that an accepting (possibly probabilistic and
oracle-using) proof admits extraction.  ArkLib owns the second notion.  This dependency-free file
isolates the only deterministic fact an ArkLib adapter needs: extraction into a stronger relation can
be post-processed through a witness-producing refinement.

The eventual ArkLib module should instantiate its input relation with `WitnessRelation.asSet`, then
post-compose ArkLib's straight-line extractor with `WitnessRelation.Sound.extract`.  It should name the
result `sp1_verifier_sound`; that name is intentionally not used for the AIR theorem. -/

namespace SP1Clean.VerifierBoundary

/-- A deterministic, perfect-extraction analogue of ArkLib knowledge soundness.  It is useful for
testing relation composition locally, but is not a replacement for ArkLib's probabilistic definition. -/
def PerfectExtraction {Statement Certificate Witness : Type}
    (accepts : Statement → Certificate → Prop)
    (relation : WitnessRelation.Relation Statement Witness) : Prop :=
  ∀ statement certificate, accepts statement certificate →
    ∃ witness, relation statement witness

/-- Post-process an extracted AIR witness into a semantic execution witness.  ArkLib's probabilistic
lifting should prove the corresponding theorem without changing its knowledge error. -/
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

/-! ## ArkLib instantiation target

Once ArkLib is on Lean 4.31 and the full AIR relation exists, the proof-system theorem should be an
ArkLib theorem of the following form (names abbreviated only for its oracle/protocol parameters):

```lean
theorem sp1_verifier_sound
    (airSound : WitnessRelation.Sound SP1AIRRelation
      (Execution.SP1ShardExecutionRelation layout model programBinding))
    (hVerifier : verifier.knowledgeSoundness init impl
      (WitnessRelation.asSet SP1AIRRelation) acceptRejectRel knowledgeError) :
    verifier.knowledgeSoundness init impl
      (WitnessRelation.asSet
        (Execution.SP1ShardExecutionRelation layout model programBinding))
      acceptRejectRel knowledgeError := by
  -- post-compose the ArkLib straight-line extractor with `airSound.extract`;
  -- extraction failure and the knowledge error are otherwise unchanged.
  -- proof deferred to the ArkLib integration layer
```

This belongs in the ArkLib integration layer, not in `sp1_air_sound`: the latter proves the
deterministic `airSound` premise and says nothing about Fiat–Shamir, commitments, query soundness, or
the probability of extractor failure. -/

end SP1Clean.VerifierBoundary
