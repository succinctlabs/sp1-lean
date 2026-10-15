module

public import ToClean.Air.EnsembleBuild
public import ToClean.Circuit.VerifierAssertions

/-! # Fresh verifier channels

Clean has no channel allocator for verifier extensions. This addition derives a name from both
registered channels and every actual verifier/table interaction, then proves the original ledger
is empty on that channel. It belongs beside Clean's ensemble verifier composition API; remove it
when upstream provides automatic channel separation.
-/

@[expose] public section

namespace Air.Flat.VerifierChannel
open Circuit
variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Registered channel names and every literal verifier/component interaction name. -/
def channelNames (ens : Ensemble F PublicIO) : List String :=
  ens.channels.map (·.name) ++ ens.verifierOperations.interactions.map (·.channel.name) ++
    ens.tables.flatMap (fun component => component.operations.interactions.map (·.channel.name))

private theorem length_le_nameBound {names : List String} {name : String} (member : name ∈ names) :
    name.length ≤ names.foldr (fun name bound => max name.length bound) 0 := by
  induction names with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left ..
    · exact le_trans (ih member) (Nat.le_max_right ..)

/-- A name longer than every registered or actually used name, preserving the check's stem. -/
def channelName (stem : String) (ens : Ensemble F PublicIO) : String :=
  stem ++ String.ofList
    (List.replicate ((channelNames ens).foldr (fun name bound => max name.length bound) 0 + 1) '_')

/-- The dedicated channel enforcing zero values, fresh for the entire original ensemble. -/
def channel (stem : String) (ens : Ensemble F PublicIO) : RawChannel F :=
  (Verifier.zeroChannel (F := F) (channelName stem ens)).toRaw

private theorem channel_ne (stem : String) (ens : Ensemble F PublicIO) (other : RawChannel F)
    (member : other.name ∈ channelNames ens) : channel stem ens ≠ other := by
  intro same
  have bound := length_le_nameBound member
  have lengths := congrArg (fun channel : RawChannel F => channel.name.length) same
  simp only [channel, Verifier.zeroChannel, Channel.toRaw, channelName,
    String.length_append, String.length_ofList, List.length_replicate] at lengths
  omega

/-- Static evidence that the check channel has no pre-existing producer or consumer. -/
structure Fresh (stem : String) (ens : Ensemble F PublicIO) : Prop where
  /-- The channel is newly registered by installation. -/
  unregistered : channel stem ens ∉ ens.channels
  /-- The original verifier emits no occurrence on the new channel. -/
  verifier : ∀ env, ens.verifierOperations.interactionValuesWith (channel stem ens) env = []
  /-- No physical component emits an occurrence on the new channel. -/
  tables : ∀ component ∈ ens.tables, ∀ env,
    component.operations.interactionValuesWith (channel stem ens) env = []

theorem fresh (stem : String) (ens : Ensemble F PublicIO) : Fresh stem ens := by
  classical
  have absent (ops : Operations F)
      (included : ∀ interaction ∈ ops.interactions, interaction.channel.name ∈ channelNames ens)
      (env : Environment F) : ops.interactionValuesWith (channel stem ens) env = [] := by
    have empty : ops.interactionsWith (channel stem ens) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro interaction member
      simpa using (channel_ne stem ens interaction.channel (included interaction member)).symm
    simp only [Operations.interactionValuesWith, empty, List.map_nil]
  refine ⟨?_, ?_, ?_⟩
  · intro member
    exact channel_ne stem ens (channel stem ens)
      (by simp only [channelNames, List.mem_append]; exact Or.inl (Or.inl (List.mem_map.mpr ⟨_, member, rfl⟩))) rfl
  · apply absent
    intro interaction member
    simp only [channelNames, List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.mpr ⟨_, member, rfl⟩))
  · intro component member
    apply absent
    intro interaction occurrence
    simp only [channelNames, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨component, member,
      List.mem_map.mpr ⟨interaction, occurrence, rfl⟩⟩)

/-- Static separation makes the original witness's entire check-channel ledger empty. -/
theorem Fresh.empty_ledger (stem : String) {ens : Ensemble F PublicIO} (fresh : Fresh stem ens)
    (witness : EnsembleWitness ens) : witness.interactionsWith (channel stem ens) = [] := by
  change ens.verifierOperations.interactionValuesWith (channel stem ens)
    (Environment.fromInput witness.publicInput witness.data) ++
      witness.tables.flatMap (fun table => table.interactionsWith witness.data (channel stem ens)) = []
  rw [fresh.verifier, List.nil_append]
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply List.flatMap_eq_nil_iff.mpr
  intro row _
  exact fresh.tables table.component (EnsembleWitness.mem_component_of_mem member) _

end Air.Flat.VerifierChannel
