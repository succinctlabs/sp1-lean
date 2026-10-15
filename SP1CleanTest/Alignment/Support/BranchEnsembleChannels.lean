import SP1CleanTest.Alignment.Support.BranchEnsembleFixture

/-! # Exact channel inventory for the branch ensemble

The registry transport retains complete raw channel identities and every physical occurrence.
-/

namespace SP1Clean.Audit.BranchEnsemble

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Channels

/-- Original protocol channels; public assertion channels are allocated separately. -/
def originalChannels (target : MemorySnapshot) : List (RawChannel Fp) :=
  [HostCallChip.channel.toRaw, WritePermissionProvider.channel.toRaw,
    (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
    stateChannel.toRaw, byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
    exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw,
    HintReadWordChip.stateChannel.toRaw, HostHintQueue.wordChannel.toRaw,
    HostHintQueue.nodeChannel.toRaw, HostHintQueue.stateChannel.toRaw, HostExitBoundary.channel.toRaw,
    (HostCommitChip.stateChannel false).toRaw, (HostCommitChip.stateChannel true).toRaw,
    HostRamAccessChip.channel.toRaw, (FinalMemoryValue.channel false).toRaw,
    FinalMemoryChange.channel.toRaw, (FinalMemoryValue.channel true).toRaw,
    source.sail.memorySnapshot.registerTable.channel.toRaw,
    (FinalRegisterValue.membership target).channel.toRaw,
    (InitialMemoryLookup.membership source.sail.memory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw,
    (InitialMemoryLookup.membership target.memory (2 ^ 48) "sp1.native.target_memory").channel.toRaw]

/-- The full physical inventory and protocol registry before source assertions are installed. -/
def rawAssembly (target : MemorySnapshot) : Ensemble Fp SP1PublicIO :=
  let resources := HostHintReadLocal.sourceResources (p := SP1Prime) [] ++
    FinalMemoryChecks.checkTables target
  let auxiliary := (HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
    (HostHintReadHandoff.wordResources ++ resources)
  HostLocalCore.baseEnsemble image source auxiliary
    ((HintReadWordChip.stateChannel.toRaw :: auxiliary.flatMap (·.circuit.channels)) ++ [])
    (HostFinalMemory.source_unique_names image source target)

/-- Source checks installed on the complete inventory, before host endpoints. -/
def beforeBoundary (target : MemorySnapshot) : Ensemble Fp SP1PublicIO :=
  HostHintReadLocal.ensemble image source HostCallReceivers.available
    (HostHintReadLocal.sourceResources [] ++ FinalMemoryChecks.checkTables target) []
    (HostFinalMemory.source_unique_names image source target)

/-- The original assembly before adding the target-dependent change verifier. -/
def baseAssembly (target : MemorySnapshot) :=
  HostFinalMemory.withReceipts (p := SP1Prime) image source target
    (HostHintQueueBoundary.initial []) source.host HostCallReceivers.available
    (HostHintReadLocal.sourceResources []) [] (HostFinalMemory.source_unique_names image source target)

/-- Source and host assertion channels are retained alongside every protocol channel. -/
def baseChannels (target : MemorySnapshot) : List (RawChannel Fp) :=
  originalChannels target ++
    [(LocalSourceBoundary.checker image source).channel (rawAssembly target),
     (HostHintQueueBoundary.boundary source (HostHintQueueBoundary.initial []) source.host).channel
       (beforeBoundary target)]

/-- The complete unique registry includes the target-change verifier's assertion channel. -/
def channels (target : MemorySnapshot) : List (RawChannel Fp) :=
  baseChannels target ++
    [(FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).channel (baseAssembly target)]

/-- Registry occurrence indices before the change verifier, checked by full raw records. -/
def channelOccurrences : List (Fin 28) :=
  [0, 1, 2, 3, 22, 24, 4, 5, 6, 7, 8, 9, 10, 11, 5, 5, 12, 5, 5, 13, 0, 14, 11, 13, 12, 0, 14, 11, 5, 0, 0, 15, 0, 0, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 13, 0, 14, 0, 14, 13, 0, 14, 0, 14, 5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11, 5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11, 13, 12, 16, 16, 17, 17, 23, 19, 19, 20, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 21, 21, 20, 23, 25, 26, 14, 16, 17, 15, 14, 16, 17, 15, 27, 19, 21]

/-- The original registration list repeats precisely these full raw channels. -/
theorem channel_expansion (target : MemorySnapshot) :
    (baseAssembly target).channels = channelOccurrences.map (fun index => (baseChannels target)[index.val]'(by
      change index.val < 28
      exact index.isLt)) := by
  repeat' first
    | apply congrArg₂ (@List.cons (RawChannel Fp))
    | rfl

/-- Every canonical channel has an original registration. -/
theorem channelOccurrences_complete (index : Fin 28) : index ∈ channelOccurrences := by
  fin_cases index <;> decide

/-- Full raw membership includes each channel's arity and predicate. -/
private theorem base_channels_membership (target : MemorySnapshot) (channel : RawChannel Fp) :
    channel ∈ baseChannels target ↔ channel ∈ (baseAssembly target).channels := by
  rw [channel_expansion]
  constructor
  · intro member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have small : index < 28 := bound
    exact List.mem_map.mpr ⟨⟨index, small⟩, channelOccurrences_complete _, equal⟩
  · intro member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact List.getElem_mem _

/-- Exact declared channel indices for every installed physical table, including empty tables. -/
def componentChannelIndices : List (List (Fin 26)) :=
  [[22, 5, 2, 5, 5, 5, 5, 7, 2], [24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 2, 5, 5, 5, 5, 7, 2], [5, 2, 2], [5, 3, 5, 5, 5, 5, 7, 3, 19], [5, 5, 3, 5, 5, 5, 5, 7, 3, 21], [5, 3, 3], [6], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 7], [5, 4, 6, 7, 7], [5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 5, 4, 7], [5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 5, 4, 7], [5, 5, 4, 5, 6, 7, 5, 5, 5, 7], [5, 4, 5, 5, 5, 5, 5, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 5, 5, 7, 5, 6, 7, 4, 7], [5, 4, 5, 5, 7, 5, 6, 7, 5, 5, 1, 4, 7], [5, 4, 6, 7, 1, 1, 4, 7], [5, 4, 6, 7, 1, 1, 1, 1, 4, 7], [5, 4, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5, 7, 7], [5, 4], [5, 4, 6, 7, 8, 7], [5, 4, 6, 7, 8, 9, 10, 5, 7, 7, 0], [22], [24], [1], [5, 5, 12, 5, 5, 13, 0, 14, 11, 13, 12, 0, 14, 11], [5, 0, 0, 15], [0, 0], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [13, 0, 14, 0, 14, 13], [0, 14, 0, 14], [5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11], [5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11], [13], [12], [16, 16], [17, 17], [23, 19, 19, 20], [25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 21, 21, 20], [23], [25]]

private theorem change_channels_membership (keys : List (FinalMemoryChange.Key Fp))
    (channel : RawChannel Fp) :
    channel ∈ (FinalMemoryChangeBoundary.circuit keys).channels ↔
      channel = FinalMemoryChange.channel.toRaw := by
  simp only [FinalMemoryChangeBoundary.circuit, circuit_norm,
    List.mem_append, List.mem_ofFn, List.mem_singleton]
  constructor
  · rintro (⟨_, rfl⟩ | rfl) <;> rfl
  · intro same
    exact Or.inr same

/-- Registry reindexing retains every protocol and assertion channel by full raw identity. -/
theorem channels_membership (target : MemorySnapshot) (channel : RawChannel Fp) :
    channel ∈ channels target ↔ channel ∈ (assembly target).channels := by
  change channel ∈ baseChannels target ++ [_] ↔
    channel ∈ ((baseAssembly target).channels ++
      (FinalMemoryChangeBoundary.circuit ((source.sail.memorySnapshot.changes target).map
        FinalMemoryChange.encode)).channels) ++ [_]
  simp only [List.mem_append, change_channels_membership, ← base_channels_membership]
  have registered : (FinalMemoryChange.channel (p := SP1Prime)).toRaw ∈ baseChannels target := by
    apply List.mem_append_left
    simp [originalChannels]
  constructor
  · rintro (member | member)
    · exact Or.inl (Or.inl member)
    · exact Or.inr member
  · rintro ((member | same) | member)
    · exact Or.inl member
    · exact Or.inl (same.symm ▸ registered)
    · exact Or.inr member

/-- Every physical table retains its exact full declared channels, including empty tables. -/
theorem table_channels (target : MemorySnapshot) :
    (assembly target).tables.map (fun component => component.circuit.channels) =
      componentChannelIndices.map (fun indices => indices.map (fun index =>
        (originalChannels target)[index.val]'(by change index.val < 26; exact index.isLt))) := by
  repeat' first
    | apply congrArg₂ List.cons
    | rfl

/-- Every installed physical component uses only the original protocol channels. -/
theorem component_channels_subset (target : MemorySnapshot) (component : Component Fp)
    (member : component ∈ (assembly target).tables) : component.circuit.channels ⊆ originalChannels target := by
  have present := List.mem_map_of_mem
    (f := fun component : Component Fp => component.circuit.channels) member
  rw [table_channels] at present
  obtain ⟨indices, _, equal⟩ := List.mem_map.mp present
  rw [← equal]
  intro channel used
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp used
  exact List.getElem_mem _

/-- Every physical interaction has its full raw channel in the authenticated registry. -/
theorem channels_complete (target : MemorySnapshot) (component : Component Fp)
    (member : component ∈ (assembly target).tables) (interaction : AbstractInteraction Fp)
    (used : interaction ∈ component.operations.interactions) : interaction.channel ∈ channels target := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply component_channels_subset target component member
  apply component.circuit.channels_subset component.rowInputVar component.rowOffset
  rw [Component.interactions_eq] at used
  exact List.mem_map_of_mem (f := fun interaction : AbstractInteraction Fp => interaction.channel) used


/-- Distinct stems separate the three check names without evaluating the dynamic target inventory. -/
private theorem check_name_prefixes (target : MemorySnapshot) :
    ([(LocalSourceBoundary.checker image source).channel (rawAssembly target),
      (HostHintQueueBoundary.boundary source (HostHintQueueBoundary.initial []) source.host).channel
        (beforeBoundary target),
      (FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).channel (baseAssembly target)].map
        (fun channel => channel.name.toList.take 8)) =
      ["sp1.loca".toList, "host-bou".toList, "final-me".toList] := by
  simp only [List.map_cons, List.map_nil, PublicVerifier.channel, ClosedVerifier.channel,
    VerifierChannel.channel, Verifier.zeroChannel, Channel.toRaw, VerifierChannel.channelName,
    LocalSourceBoundary.checker, HostHintQueueBoundary.boundary, HostBoundary.closed,
    FinalMemoryChangeBoundary.closed, String.toList_append]
  rfl

/-- Protocol and check channels have distinct names as well as distinct raw records. -/
theorem channels_unique (target : MemorySnapshot) : ((channels target).map RawChannel.name).Nodup := by
  simp only [channels, baseChannels, List.map_append, List.append_assoc, List.map_cons, List.map_nil]
  rw [List.nodup_append]
  have prefixes := check_name_prefixes target
  simp only [List.map_cons, List.map_nil] at prefixes
  refine ⟨?_, List.Nodup.of_map (fun name : String => name.toList.take 8) ?_, ?_⟩
  · simp only [originalChannels, List.map_cons, List.map_nil, Channel.toRaw,
      StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable, StaticTable.ofRows, FinalRegisterValue.membership]
    decide
  · change ([_, _, _].map (fun name : String => name.toList.take 8)).Nodup
    simpa only [List.map_cons, List.map_nil, prefixes] using
      (show ["sp1.loca".toList, "host-bou".toList, "final-me".toList].Nodup from by decide)
  · intro a old b added same
    have present := List.mem_map_of_mem (f := fun name : String => name.toList.take 8) added
    change b.toList.take 8 ∈ [_, _, _] at present
    rw [prefixes] at present
    have separate : ∀ name ∈ (originalChannels target).map RawChannel.name,
        name.toList.take 8 ∉ ["sp1.loca".toList, "host-bou".toList, "final-me".toList] := by
      simp only [originalChannels, List.map_cons, List.map_nil, Channel.toRaw,
        StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable, StaticTable.ofRows, FinalRegisterValue.membership]
      decide
    exact separate a old (same.symm ▸ present)

private theorem checkZeros_channel (name : String) (values : List (Expression Fp))
    (interaction : AbstractInteraction Fp)
    (used : interaction ∈ (Verifier.checkZeros name values).circuitOperations.interactions) :
    interaction.channel = (Verifier.zeroChannel name).toRaw := by
  simp only [Verifier.circuitOperations, Verifier.checkZeros_operations,
    Verifier.Operations.circuitOperations_interactions, Verifier.Operations.interactions,
    List.mem_map, List.mem_flatMap] at used
  obtain ⟨operation, ⟨value, _, member⟩, rfl⟩ := used
  simp only [Verifier.checkZero, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

private theorem andThen_channels (first second : Verifier.Program Fp SP1PublicIO)
    (registry : List (RawChannel Fp))
    (left : ∀ interaction ∈ first.circuitOperations.interactions, interaction.channel ∈ registry)
    (right : ∀ interaction ∈ second.circuitOperations.interactions, interaction.channel ∈ registry) :
    ∀ interaction ∈ (first.andThen second).circuitOperations.interactions,
      interaction.channel ∈ registry := by
  intro interaction used
  simp only [Verifier.Program.andThen, Verifier.Program.circuitOperations, Verifier.Program.operations,
    Verifier.operations_bind, Verifier.Operations.circuitOperations, Verifier.Operations.interactions,
    List.map_append, Operations.interactions_append, List.mem_append] at used
  rcases used with used | used
  · exact left interaction used
  · exact right interaction used

private theorem closed_program_channels (closed : ClosedVerifier Fp) (ens : Ensemble Fp SP1PublicIO)
    (interaction : AbstractInteraction Fp)
    (used : interaction ∈ (closed.program ens).circuitOperations.interactions) :
    interaction.channel ∈ closed.circuit.channels ∨ interaction.channel = closed.channel ens := by
  change interaction ∈ (closed.emit >>= fun _ =>
    Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactions at used
  simp only [Verifier.circuitOperations, Verifier.operations_bind, Verifier.Operations.circuitOperations,
    Verifier.Operations.interactions, List.map_append, Operations.interactions_append, List.mem_append] at used
  rcases used with original | check
  · left
    have member : interaction ∈ closed.operations.interactions := by
      rw [← closed.emit_interactions]
      exact original
    exact closed.circuit.channels_subset () 0 (List.mem_map_of_mem (f := AbstractInteraction.channel) member)
  · exact Or.inr (checkZeros_channel _ _ interaction check)


private theorem raw_verifier_channels (target : MemorySnapshot) (interaction : AbstractInteraction Fp)
    (used : interaction ∈ (rawAssembly target).verifierOperations.interactions) :
    interaction.channel ∈ originalChannels target := by
  have inventory : ((rawAssembly target).verifierOperations.interactions.map (·.channel)) =
      ([4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 8, 2, 2, 3, 3] : List (Fin 26)).map
        (fun index => (originalChannels target)[index.val]'(by change index.val < 26; exact index.isLt)) := by rfl
  have member := List.mem_map_of_mem (f := AbstractInteraction.channel) used
  rw [inventory] at member
  obtain ⟨index, _, equal⟩ := List.mem_map.mp member
  exact equal ▸ List.getElem_mem _

private theorem host_boundary_channels (target : MemorySnapshot) (channel : RawChannel Fp)
    (used : channel ∈ (HostHintQueueBoundary.boundary (p := SP1Prime) source
      (HostHintQueueBoundary.initial []) source.host).circuit.channels) : channel ∈ originalChannels target := by
  have inventory : (HostHintQueueBoundary.boundary (p := SP1Prime) source
      (HostHintQueueBoundary.initial []) source.host).circuit.channels =
      ([14, 16, 17, 15, 14, 16, 17, 15] : List (Fin 26)).map
        (fun index => (originalChannels target)[index.val]'(by change index.val < 26; exact index.isLt)) := by rfl
  rw [inventory] at used
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp used
  exact List.getElem_mem _

private theorem base_verifier_channels (target : MemorySnapshot) :
    ∀ interaction ∈ (baseAssembly target).verifierOperations.interactions,
      interaction.channel ∈ baseChannels target := by
  have sourceChannels : ∀ interaction ∈ (beforeBoundary target).verifierOperations.interactions,
      interaction.channel ∈ baseChannels target := by
    apply andThen_channels (rawAssembly target).verifier
      ((LocalSourceBoundary.checker image source).program (rawAssembly target))
    · intro interaction used
      exact List.mem_append_left _ (raw_verifier_channels target interaction used)
    · intro interaction used
      have same := checkZeros_channel
        ((LocalSourceBoundary.checker image source).channelName (rawAssembly target))
        ((LocalSourceBoundary.checker image source).assertions (varFromOffset SP1PublicIO 0)) interaction used
      rw [same]
      exact List.mem_append_right _ (List.mem_cons_self)
  apply andThen_channels (beforeBoundary target).verifier
    ((HostHintQueueBoundary.boundary source (HostHintQueueBoundary.initial []) source.host).program
      (beforeBoundary target))
  · exact sourceChannels
  · intro interaction used
    rcases closed_program_channels _ _ interaction used with original | check
    · exact List.mem_append_left _ (host_boundary_channels target _ original)
    · rw [check]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The separate verifier retains every original emission and every assertion-check occurrence. -/
theorem verifier_channels_complete (target : MemorySnapshot) :
    ∀ interaction ∈ (assembly target).verifierOperations.interactions,
      interaction.channel ∈ channels target := by
  apply andThen_channels (baseAssembly target).verifier
    ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).program (baseAssembly target))
  · intro interaction used
    exact List.mem_append_left _ (base_verifier_channels target interaction used)
  · intro interaction used
    rcases closed_program_channels _ _ interaction used with original | check
    · have same := (change_channels_membership _ _).mp original
      rw [same]
      apply List.mem_append_left
      apply List.mem_append_left
      simp [originalChannels]
    · rw [check]
      exact List.mem_append_right _ List.mem_cons_self

end SP1Clean.Audit.BranchEnsemble
