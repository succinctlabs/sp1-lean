module

public import Clean.Circuit.Verifier

/-! # Certified interaction lists in a public verifier

Clean's verifier accepts one interaction at a time together with its unconditional opposite-side
proof. This adapter imports an existing circuit's literal interaction list using the same proof
obligation. It preserves order, repeated messages and zero multiplicities; no new operation format
or extraction path is introduced. Move it upstream beside `Verifier.addOperation`.
-/

@[expose] public section

namespace Verifier

variable {F : Type} [FiniteField F]

/-- Import existing interactions only when each satisfies Clean's verifier admission rule. -/
def ofInteractions (interactions : List (AbstractInteraction F))
    (valid : ∀ interaction ∈ interactions, ∀ env,
      if interaction.assumeGuarantees then interaction.Requirements env else interaction.Guarantees env) :
    Verifier F Unit :=
  ((), interactions.attach.map fun interaction =>
    .interact interaction.val (valid interaction.val interaction.property))

/-- Importing certified operations retains the literal source interaction list. -/
theorem ofInteractions_interactions (interactions : List (AbstractInteraction F)) (valid) :
    (ofInteractions interactions valid).circuitOperations.interactions = interactions := by
  simp [circuitOperations, Operations.circuitOperations_interactions, ofInteractions,
    operations, Operations.interactions, Operation.interaction]

/-- Every selected channel keeps all of its evaluated occurrences. -/
theorem ofInteractions_values (ops : _root_.Operations F) (valid)
    (channel : RawChannel F) (env : Environment F) :
    (ofInteractions ops.interactions valid).circuitOperations.interactionValuesWith channel env =
      ops.interactionValuesWith channel env := by
  simp only [_root_.Operations.interactionValuesWith, _root_.Operations.interactionsWith,
    ofInteractions_interactions]

end Verifier
