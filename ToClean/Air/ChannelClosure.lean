module

public import Clean.Air.FlatEnsemble

/-! # Closing a channel from its actual provider requirements

Clean supplies channel consistency and an ordered-table induction, but no direct ensemble rule
for a channel whose provider requirements are already proved. Such a channel needs no table
ordering: consistency applies to the actual balanced ledger, and each table inherits the result.
The component-level corollary keeps these static proofs independent of witness layout. A companion
closes universally true structural-channel guarantees, including the dependent arity transport
otherwise repeated at each call site. These additions are intended for `Clean/Air/FlatEnsemble.lean`;
they use no application-specific messages or tables.
-/

@[expose] public section

namespace Circuit.Operations

variable {F : Type} [FiniteField F]

/-- A structural channel with a universally true guarantee needs no provider hypothesis.
This also transports the dependent message arity when selecting the channel of an interaction. -/
theorem channelGuarantees_of_trivial (selected : RawChannel F)
    (guaranteed : ∀ mult message data, selected.Guarantees mult message data)
    (ops : Operations F) (env : Environment F) : ops.ChannelGuarantees selected env := by
  have transport : ∀ channel : RawChannel F, channel = selected →
      ∀ mult message data, channel.Guarantees mult message data := by
    rintro _ rfl
    exact guaranteed
  intro interaction _ same _
  exact transport interaction.channel same _ _ _

end Circuit.Operations

namespace Air.Flat

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO] {ens : Ensemble F PublicIO}

/-- A component with no incoming guarantees proves its contract and outgoing requirements
directly from constraints and its local assumptions. -/
theorem Component.weakSoundness_of_no_guarantees (component : Component F)
    (noGuarantees : component.circuit.channelsWithGuarantees = [])
    {env : Environment F} (assumptions : component.CircuitAssumptions env)
    (constraints : component.operations.ConstraintsHold env) :
    component.Spec env ∧ component.operations.FullRequirements env := by
  have interface := component.inChannelsOrGuarantees env
  rw [noGuarantees] at interface
  exact Component.weakSoundness assumptions constraints
    ((Operations.guarantees_iff component.operations [] env interface).mpr (by simp))

/-- Channel consistency closes every pull when the actual balanced ledger's pushes satisfy
their requirements. This covers the separate verifier as well as every physical table, in any
order, all evaluated at the canonical data derived from the witness's physical rows. -/
theorem EnsembleWitness.channelGuarantees_of_requirements (witness : EnsembleWitness ens)
    (channel : RawChannel F) [channel.Consistent]
    (balanced : witness.BalancedChannel channel)
    (verifier : ens.VerifierChannelRequirements witness.publicInput witness.data channel)
    (requirements : ∀ table ∈ witness.tables, table.ChannelRequirements witness.data channel) :
    ens.VerifierChannelGuarantees witness.publicInput witness.data channel ∧
      ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data channel := by
  have allRequirements : ∀ interaction ∈ witness.interactionsWith channel,
      interaction.channel = channel ∧ interaction.Requirements witness.data := by
    intro interaction member
    refine ⟨EnsembleWitness.channel_eq_of_mem_interactionsWith member, ?_⟩
    rcases EnsembleWitness.mem_interactionsWith.mp member with emitted | ⟨table, member, emitted⟩
    · exact EnsembleWitness.verifierChannelRequirements_iff_forall.mp verifier interaction emitted
    · exact (table.channelRequirements_iff_forall witness.data channel).mp
        (requirements table member) interaction emitted
  have guarantees := (inferInstance : channel.Consistent).consistent
    (witness.interactionsWith channel) witness.data balanced allRequirements
  constructor
  · rw [EnsembleWitness.verifierChannelGuarantees_iff_forall]
    intro interaction emitted
    exact guarantees interaction (EnsembleWitness.mem_interactionsWith.mpr (Or.inl emitted))
  · intro table member
    rw [table.channelGuarantees_iff_forall witness.data channel]
    intro interaction emitted
    exact guarantees interaction
      (EnsembleWitness.mem_interactionsWith.mpr (Or.inr ⟨table, member, emitted⟩))

/-- Proved component-local requirements and raw constraints suffice to close a channel.
No witness-specific provider validity or positional consumer/provider partition is needed. -/
theorem EnsembleWitness.channelGuarantees_of_component_requirements (witness : EnsembleWitness ens)
    (channel : RawChannel F) [channel.Consistent]
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel channel)
    (verifier : ∀ input data, ens.VerifierChannelRequirements input data channel)
    (requirements : ∀ component ∈ ens.tables, ∀ env,
      component.operations.ConstraintsHold env → component.operations.ChannelRequirements channel env) :
    ens.VerifierChannelGuarantees witness.publicInput witness.data channel ∧
      ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data channel := by
  apply witness.channelGuarantees_of_requirements channel balanced (verifier _ _)
  intro table member row rowMember
  apply requirements table.component (EnsembleWitness.mem_component_of_mem member)
  exact constraints table member row rowMember

end Air.Flat
