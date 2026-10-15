module

public import ToClean.Air.ChannelClosure
public import ToClean.Circuit.InteractionRecovery

/-! # Authenticating typed records through the complete interaction ledger

Clean's balance theorem finds a matching nonzero, non-pull interaction for each unit pull.
It does not package the component-local provenance of that matching record. `Authenticates`
supplies this interface without strengthening channel guarantees: a property of actual source
records transports through the witness's count-bounded ledger to every requested record.
The physical-table interface can consume prior grounding facts for dynamic providers. Consumers
and silent components satisfy the interface without authenticating any source.
This addition belongs beside Clean's flat ensemble channel-closure rules.
-/

@[expose] public section

namespace Air.Flat

open Circuit

variable {F : Type} [FiniteField F] {Record : TypeMap} [ProvableType Record]

/-- Every active non-pull emission has the stated typed meaning, as a consequence of raw constraints. -/
def Component.Authenticates (component : Component F) (channel : Channel F Record)
    (property : Record F → Prop) : Prop :=
  ∀ env, component.operations.ConstraintsHold env →
    ∀ interaction ∈ component.operations.interactionValuesWith channel.toRaw env,
      interaction.mult ≠ 0 → interaction.mult ≠ -1 →
        ∃ record, interaction.msg = (toElements record).toArray ∧ property record

theorem Component.Authenticates.of_pulls (component : Component F) (channel : Channel F Record)
    (property : Record F → Prop)
    (pulls : ∀ env, component.operations.ConstraintsHold env →
      ∀ interaction ∈ component.operations.interactionValuesWith channel.toRaw env,
        interaction.mult = 0 ∨ interaction.mult = -1) :
    component.Authenticates channel property := by
  intro env checked interaction member nonzero notPull
  exact ((pulls env checked interaction member).elim nonzero notPull).elim

theorem Component.Authenticates.of_silent (component : Component F) (channel : Channel F Record)
    (property : Record F → Prop) (silent : channel.toRaw ∉ component.circuit.channels) :
    component.Authenticates channel property := by
  intro env _ interaction member
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((component.circuit.main (varFromOffset component.Input 0)).operations
    (size component.Input)).interactionsWith channel.toRaw).map _ at member
  rw [InteractionRecovery.interactionsWith_main_eq_nil component.circuit.base _ _ _ silent] at member
  contradiction

theorem Component.Authenticates.mono {component : Component F} {channel : Channel F Record}
    {property next : Record F → Prop} (authenticated : component.Authenticates channel property)
    (implies : ∀ record, property record → next record) : component.Authenticates channel next := by
  intro env checked interaction member nonzero notPull
  obtain ⟨record, payload, valid⟩ := authenticated env checked interaction member nonzero notPull
  exact ⟨record, payload, implies record valid⟩

/-- Authentication of actual physical sources may depend on facts established elsewhere in the
ensemble, such as an earlier state or memory transition. It does not quantify over unused rows. -/
def Table.Authenticates (table : Table F) (data : ProverData F) (channel : Channel F Record)
    (property : Record F → Prop) : Prop :=
  ∀ physical ∈ table.table,
    ∀ interaction ∈ table.component.operations.interactionValuesWith channel.toRaw (Environment.fromArray physical data),
      interaction.mult ≠ 0 → interaction.mult ≠ -1 →
        ∃ record, interaction.msg = (toElements record).toArray ∧ property record

/-- Unconditional component-local source proofs authenticate every constrained row of a table. -/
theorem Table.Authenticates.of_component (table : Table F) (data : ProverData F) (channel : Channel F Record)
    (property : Record F → Prop) (source : table.component.Authenticates channel property)
    (constraints : table.Constraints data) : table.Authenticates data channel property :=
  fun physical member => source (Environment.fromArray physical data) (constraints physical member)

/-- A complete physical ledger transports source meaning to each unit consumer. -/
theorem authenticated_pull_of_tables (tables : List (Table F)) (data : ProverData F)
    (channel : Channel F Record) (property : Record F → Prop)
    (sources : ∀ table ∈ tables, table.Authenticates data channel property)
    (balanced : BalancedInteractions (tables.flatMap (·.interactionsWith data channel.toRaw))) (record : Record F)
    (member : channel.pulledValue record ∈ tables.flatMap (·.interactionsWith data channel.toRaw)) : property record := by
  obtain ⟨provider, providerMem, samePayload, nonzero, notPull⟩ :=
    exists_push_of_pull _ balanced (channel.pulledValue record) member rfl
  obtain ⟨table, tableMem, providerMem⟩ := List.mem_flatMap.mp providerMem
  obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp providerMem
  obtain ⟨actual, payload, valid⟩ := sources table tableMem physical physicalMem provider emitted nonzero notPull
  have equal := congrArg (fromElements (M := Record))
    (Vector.toArray_inj.mp (payload.symm.trans samePayload))
  simp only [ProvableType.fromElements_toElements] at equal
  rwa [equal] at valid

variable {Public : TypeMap} [ProvableType Public] {assembly : Ensemble F Public}

/-- Authentication accounts for both public verifier emissions and physical table sources,
retaining the count bound of the complete ledger. -/
theorem EnsembleWitness.authenticated_pull (witness : EnsembleWitness assembly)
    (channel : Channel F Record) (property : Record F → Prop)
    (verifier : ∀ interaction ∈ witness.verifierInteractionsWith channel.toRaw,
      interaction.mult ≠ 0 → interaction.mult ≠ -1 →
        ∃ record, interaction.msg = (toElements record).toArray ∧ property record)
    (sources : ∀ component ∈ assembly.tables, component.Authenticates channel property)
    (constraints : witness.Constraints)
    (balanced : witness.BalancedChannel channel.toRaw) (record : Record F)
    (member : channel.pulledValue record ∈ witness.interactionsWith channel.toRaw) : property record := by
  obtain ⟨provider, providerMem, samePayload, nonzero, notPull⟩ :=
    exists_push_of_pull _ balanced (channel.pulledValue record) member rfl
  have authenticated : ∃ actual, provider.msg = (toElements actual).toArray ∧ property actual := by
    rcases EnsembleWitness.mem_interactionsWith.mp providerMem with emitted | ⟨table, tableMem, emitted⟩
    · exact verifier provider emitted nonzero notPull
    · obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp emitted
      exact Table.Authenticates.of_component table witness.data channel property
        (sources _ (EnsembleWitness.mem_component_of_mem tableMem)) (constraints table tableMem)
        physical physicalMem provider emitted nonzero notPull
  obtain ⟨actual, payload, valid⟩ := authenticated
  have equal := congrArg (fromElements (M := Record))
    (Vector.toArray_inj.mp (payload.symm.trans samePayload))
  simp only [ProvableType.fromElements_toElements] at equal
  rwa [equal] at valid

private theorem guarantees_of_authenticated_pull (channel : Channel F Record)
    (interaction : Interaction F) (same : interaction.channel = channel.toRaw) (data : ProverData F)
    (authenticated : ∀ record, interaction = channel.pulledValue record → channel.Guarantees record data) :
    interaction.Guarantees data := by
  rcases interaction with ⟨raw, mult, message, width, assume⟩
  dsimp only at same
  cases same
  intro assumed pulled
  change mult = -1 at pulled
  change assume = true at assumed
  subst mult
  cases assume
  · contradiction
  · apply authenticated (fromElements (M := Record) ⟨message, width⟩)
    simp only [Channel.pulledValue, ProvableType.toElements_fromElements]

/-- Typed pull authentication discharges guarantees of the public verifier and every
physical table against the same canonical prover data. -/
theorem EnsembleWitness.channelGuarantees_of_authenticated_pulls (witness : EnsembleWitness assembly)
    (channel : Channel F Record)
    (authenticated : ∀ record, channel.pulledValue record ∈ witness.interactionsWith channel.toRaw →
      channel.Guarantees record witness.data) :
    assembly.VerifierChannelGuarantees witness.publicInput witness.data channel.toRaw ∧
      ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data channel.toRaw := by
  have guarantees : ∀ interaction ∈ witness.interactionsWith channel.toRaw,
      interaction.Guarantees witness.data := by
    intro interaction emitted
    apply guarantees_of_authenticated_pull channel interaction
      (EnsembleWitness.channel_eq_of_mem_interactionsWith emitted) witness.data
    intro record equal
    exact authenticated record (equal ▸ emitted)
  constructor
  · rw [EnsembleWitness.verifierChannelGuarantees_iff_forall]
    intro interaction emitted
    exact guarantees interaction (EnsembleWitness.mem_interactionsWith.mpr (Or.inl emitted))
  · intro table member
    rw [table.channelGuarantees_iff_forall witness.data channel.toRaw]
    intro interaction emitted
    exact guarantees interaction
      (EnsembleWitness.mem_interactionsWith.mpr (Or.inr ⟨table, member, emitted⟩))

end Air.Flat
