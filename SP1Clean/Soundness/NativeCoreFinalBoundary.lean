import SP1Clean.Soundness.NativeCoreBoundaries

/-! # Structural finalization from the combined native AIR

The final inventory consumes Memory records without assuming their values or clocks are valid.
Its canonical addresses and unique locations follow from Byte closure and its private ordering
ledger. These are the boundary facts needed before timed Memory grounding can establish currency.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Components following the final inventory in the physical native assembly. -/
def afterFinalTables (image : ProgramImage) : List (Component (ZMod p)) :=
  [{ circuit := DecodedProgramProvider.circuit image }] ++ sp1Tables ++
    (sp1ProviderTables.take 23 ++ sp1ProviderTables.drop 26)

theorem afterInitialTables_eq (image : ProgramImage) :
    afterInitialTables (p := p) image =
      FinalMemoryEnsemble.inventory.views.map (·.component) ++ afterFinalTables image := by
  simp only [afterInitialTables, afterFinalTables, List.append_assoc]

/-- The final proof inventory inherits distinct names from the complete physical assembly. -/
theorem final_unique_names (image : ProgramImage) :
    ((afterInitialTables (p := p) image ++ [ramMembership image]).map
      (fun component : Component (ZMod p) => component.circuit.name)).Nodup := by
  have names := (baseEnsemble (p := p) image).unique_names
  simp only [baseEnsemble, tables, List.map_append, List.nodup_append] at names
  simpa only [List.map_append, List.nodup_append] using names.2.1

/-- The unchanged physical suffix, with its own canonical data and fixed ordering verifier.
The omitted initialization tables are silent on the final ordering channel. -/
def finalWitness {image : ProgramImage} (witness : EnsembleWitness (ensemble (p := p) image)) :
    EnsembleWitness (FinalMemoryEnsemble.ensemble (p := p) (afterFinalTables image ++ [ramMembership image]) []
      (by simpa only [afterInitialTables_eq, List.append_assoc] using final_unique_names (p := p) image)) :=
  EnsembleWitness.ofTables _ (witness.tables.drop 3) () (by
    rw [List.map_drop, witness.tables_map_component]
    change (tables image).drop 3 =
      FinalMemoryEnsemble.inventory.views.map (·.component) ++ (afterFinalTables image ++ [ramMembership image])
    rw [tables]
    have length : ((InitialMemoryEnsemble.views (p := p) image).map (·.component)).length = 3 := rfl
    rw [List.drop_left' length, afterInitialTables_eq, List.append_assoc])

/-- Finalizer contracts follow before any Memory guarantees or execution facts are available. -/
theorem finalTables_spec {image : ProgramImage} (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ (finalWitness witness).tables.take (FinalMemoryEnsemble.inventory (p := p)).views.length,
      table.Spec (finalWitness witness).data := by
  intro table member row rowMem
  have componentMem : table.component ∈ (FinalMemoryEnsemble.inventory (p := p)).views.map (·.component) := by
    have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [List.map_take, (finalWitness witness).tables_map_component] at mapped
    simpa only [FinalMemoryEnsemble.ensemble, OrderedMemoryEnsemble.Inventory.ensemble,
      OrderedBoundaryEnsemble.ensemble, List.take_left', List.length_map] using mapped
  obtain ⟨view, viewMem, same⟩ := List.mem_map.mp componentMem
  have tableMem : table ∈ witness.tables := List.mem_of_mem_drop (List.mem_of_mem_take member)
  have byte := ((finishedChannel_guarantees image witness constraints balanced).2 table tableMem).1 row rowMem
  have checked := constraints table tableMem row rowMem
  rw [← same] at byte checked ⊢
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
  exact FinalMemoryEnsemble.view_spec_setData id row witness.data (finalWitness witness).data
    (FinalMemoryEnsemble.view_spec id _ checked byte)

/-- Every consumed final record has a canonical location, independently of its value and clock. -/
theorem final_records_canonical {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ record ∈ FinalMemoryEnsemble.records (finalWitness witness), MemoryBoundary.CanonicalSpec record :=
  FinalMemoryEnsemble.inventory.records_valid_of_tables (finalWitness witness)
    (finalTables_spec witness constraints balanced)

private theorem finalChannel_not_old :
    (OrderedBoundary.channel (p := p) OrderedFinalProvider.channelName).toRaw ∉
      (sp1Ensemble (p := p)).channels := by
  intro member
  have names := List.mem_map_of_mem (f := RawChannel.name) member
  simp [sp1Ensemble_channels, OrderedBoundary.channel, OrderedFinalProvider.channelName,
    stateChannel, memoryChannel, programChannel, byteChannel, exitChannel,
    syscallChannel, publicValuesChannel, Channel.toRaw_name] at names

theorem afterFinalTables_silent (image : ProgramImage) :
    ∀ component ∈ afterFinalTables (p := p) image,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉ component.circuit.channels := by
  intro component member
  have old (member : component ∈ (sp1Ensemble (p := p)).tables) :
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉ component.circuit.channels :=
    fun used => finalChannel_not_old (sp1Ensemble_tables_channels_subset component member used)
  simp only [afterFinalTables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | member) | member
  · change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉ [programChannel.toRaw]
    simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, programChannel, Channel.toRaw]
  · exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_left _ member)
  · have providerMem : component ∈ sp1ProviderTables (p := p) := by
      rcases member with member | member
      · exact List.mem_of_mem_take member
      · exact List.mem_of_mem_drop member
    exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_right _ providerMem)

private theorem initialTables_final_silent {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (witness.tables.take 3).flatMap
      (·.interactionsWith witness.data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply table.interactionsWith_nil_of_channel_not_mem
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [List.map_take, witness.tables_map_component] at mapped
  change table.component ∈ (tables image).take 3 at mapped
  have length : ((InitialMemoryEnsemble.views (p := p) image).map (·.component)).length = 3 := rfl
  rw [tables, List.take_left' length] at mapped
  obtain ⟨view, member, same⟩ := List.mem_map.mp mapped
  rw [← same]
  simp only [InitialMemoryEnsemble.views, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
        memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
      memoryChannel, byteChannel, Channel.toRaw]
  · change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
      ((InitialMemoryRead.circuit (p := p) image.initialMemory).channelsWithGuarantees ++
        List.replicate 2 byteChannel.toRaw ++
        [(OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw] ++
        List.replicate 4 byteChannel.toRaw ++
        [memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw])
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
      memoryChannel, byteChannel, InitialMemoryRead.circuit, InitialMemoryLookup.membership,
      StaticTable.channel, circuit_norm]
  · change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
      byteChannel, Channel.toRaw]

private theorem verifier_final_interactions (image : ProgramImage) (env : Environment (ZMod p)) :
    (verifierInteractions image).circuitOperations.interactionValuesWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw env =
      [(OrderedBoundary.channel OrderedFinalProvider.channelName).pushedValue OrderedMemoryEnsemble.startKey,
       (OrderedBoundary.channel OrderedFinalProvider.channelName).pulledValue OrderedMemoryEnsemble.endKey] := by
  have original : ((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).interactionsWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw =
      [((OrderedBoundary.channel OrderedFinalProvider.channelName).pushed (const (OrderedMemoryEnsemble.startKey (p := p)))).toRaw,
       ((OrderedBoundary.channel OrderedFinalProvider.channelName).pulled (const (OrderedMemoryEnsemble.endKey (p := p)))).toRaw] := by
    simp [Operations.interactionsWith, verifierMain, GeneralFormalCircuit.toSubcircuit_interactions,
      sp1StateVerifier, sp1StateVerifierMain, OrderedBoundaryVerifier.circuit, OrderedBoundaryVerifier.main,
      OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
      stateChannel, byteChannel, exitChannel, circuit_norm]
  simp only [Verifier.Program.circuitOperations, Verifier.Program.operations,
    Operations.interactionValuesWith, Operations.interactionsWith, verifierInteractions_interactions]
  change (((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).interactionsWith _).map _ = _
  rw [original]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pulled, ProvableType.eval_const]

/-- The final proof view preserves the actual private-channel ledger, including its verifier.
Interaction values depend only on the retained cells, even though canonical data changes. -/
theorem finalWitness_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (finalWitness witness).interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw =
      witness.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw := by
  have suffix : witness.tables.flatMap
      (·.interactionsWith witness.data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) =
      (witness.tables.drop 3).flatMap
        (·.interactionsWith witness.data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) := by
    conv_lhs => rw [← List.take_append_drop 3 witness.tables]
    rw [List.flatMap_append, initialTables_final_silent, List.nil_append]
  have cells : (witness.tables.drop 3).flatMap
      (·.interactionsWith (finalWitness witness).data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) =
      (witness.tables.drop 3).flatMap
        (·.interactionsWith witness.data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) :=
    congrArg List.flatten (List.map_congr_left fun table _ => table.interactionsWith_setData _ _ _)
  have different : bootChannel (p := p) image ≠
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw := by
    intro equal
    exact (VerifierChannel.fresh "sp1.native.boot" (baseEnsemble (p := p) image)).unregistered
      (show bootChannel image ∈ (baseEnsemble image).channels from
        equal.symm ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.verifierInteractionsWith,
    EnsembleWitness.tableContext, TableContext.interactionsWith]
  rw [show (finalWitness witness).tables = witness.tables.drop 3 from rfl, suffix, cells]
  dsimp only [Ensemble.verifierOperations, ensemble]
  rw [verifierProgram_values,
    Verifier.checkZeros_other_values _ _ _ _ different, List.append_nil, verifier_final_interactions]
  apply congrArg (fun front => front ++ (witness.tables.drop 3).flatMap
    (·.interactionsWith witness.data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw))
  change (OrderedBoundaryVerifier.verifierProgram _ _ _).circuitOperations.interactionValuesWith _ _ = _
  simp only [OrderedBoundaryVerifier.verifierProgram, Verifier.Program.circuitOperations,
    Verifier.Program.operations, Verifier.ofInteractions_values]
  exact OrderedBoundaryVerifier.interactionValues _ _ _ _ _ _

/-- The final inventory has one record per decoded location before any value is grounded.
This includes uniqueness across the register/RAM split and across duplicate physical rows. -/
theorem final_records_locations_nodup {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((FinalMemoryEnsemble.records (finalWitness witness)).map MemoryMsg.locOf).Nodup := by
  apply FinalMemoryEnsemble.inventory.records_locations_nodup_of_tables
    (finalWitness witness) (fun component member => ?_) (finalTables_spec witness constraints balanced)
  · change BalancedInteractions ((finalWitness witness).interactionsWith _)
    rw [finalWitness_interactions]
    exact balanced _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

  · rcases List.mem_append.mp member with native | fixed
    · exact afterFinalTables_silent image component native
    · obtain rfl := List.mem_singleton.mp fixed
      change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
        [(InitialMemoryLookup.membership image.initialMemory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw]
      simp [InitialMemoryLookup.membership, StaticTable.channel, OrderedBoundary.channel,
        OrderedFinalProvider.channelName, Channel.toRaw]

/-- The final inventory is precisely the negative Memory ledger of its three physical tables. -/
theorem final_memory_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    ((witness.tables.drop 3).take 3).flatMap (·.interactionsWith witness.data memoryChannel.toRaw) =
      (FinalMemoryEnsemble.records (finalWitness witness)).map (memoryChannel.emittedValue (-1)) :=
by
  have cells : ((witness.tables.drop 3).take 3).flatMap (·.interactionsWith witness.data memoryChannel.toRaw) =
      ((witness.tables.drop 3).take 3).flatMap (·.interactionsWith (finalWitness witness).data memoryChannel.toRaw) :=
    congrArg List.flatten (List.map_congr_left fun table _ => table.interactionsWith_setData _ _ _)
  exact cells.trans (FinalMemoryEnsemble.memory_interactions_eq (finalWitness witness))

end SP1Clean.Soundness.NativeCore
