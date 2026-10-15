import SP1Clean.Soundness.LocalCoreBoundaries
import SP1Clean.Soundness.NativeCoreFinalBoundary

/-! # Structural finalization from the local-shard AIR

The final inventory consumes Memory records without assuming their values or clocks are valid.
Its canonical addresses and unique locations follow from this assembly's own Byte closure and
private ordering ledger. The source prefix and public verifier are projected without changing rows.
These are the boundary facts needed before timed Memory grounding can establish currency.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The unchanged physical suffix, with its own canonical data and fixed ordering verifier.
The omitted initialization tables are silent on the final ordering channel. -/
def finalWitness {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    EnsembleWitness (FinalMemoryEnsemble.ensemble (p := p)
      (NativeCore.afterFinalTables image ++ [SnapshotMemoryEnsemble.registerMembership source.sail.memorySnapshot,
          SnapshotMemoryEnsemble.ramMembership source.sail.memorySnapshot]) []
      (by
        have unique := (baseEnsemble (p := p) image source).unique_names
        change ((tables image source).map (·.circuit.name)).Nodup at unique
        rw [tables, List.map_append] at unique
        simpa only [afterSourceTables, NativeCore.afterInitialTables_eq, List.append_assoc] using
          unique.of_append_right)) :=
  EnsembleWitness.ofTables _ (witness.tables.drop 3) () (by
    rw [List.map_drop, witness.tables_map_component]
    change (tables image source).drop 3 =
      FinalMemoryEnsemble.inventory.views.map (·.component) ++
        (NativeCore.afterFinalTables image ++ [SnapshotMemoryEnsemble.registerMembership source.sail.memorySnapshot,
          SnapshotMemoryEnsemble.ramMembership source.sail.memorySnapshot])
    rw [tables]
    have length : ((SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.map (·.component)).length = 3 := rfl
    rw [List.drop_left' length, afterSourceTables, NativeCore.afterInitialTables_eq, List.append_assoc])

/-- Finalizer contracts follow before any Memory guarantees or execution facts are available. -/
theorem finalTables_spec_of_byte {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw) :
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
  have byte := bytes table tableMem row rowMem
  have checked := constraints table tableMem row rowMem
  rw [← same] at byte checked ⊢
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
  exact FinalMemoryEnsemble.view_spec_setData id row witness.data (finalWitness witness).data
    (FinalMemoryEnsemble.view_spec id _ checked byte)

/-- The complete local AIR closes the finalizers' Byte requirements. -/
theorem finalTables_spec {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ (finalWitness witness).tables.take (FinalMemoryEnsemble.inventory (p := p)).views.length,
      table.Spec (finalWitness witness).data :=
  finalTables_spec_of_byte witness constraints
    (fun table member => ((finishedChannel_guarantees image source witness constraints balanced).2 table member).1)

/-- Every consumed final record has a canonical location, independently of its value and clock. -/
theorem final_records_canonical {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ record ∈ FinalMemoryEnsemble.records (finalWitness witness), MemoryBoundary.CanonicalSpec record :=
  FinalMemoryEnsemble.inventory.records_valid_of_tables (finalWitness witness)
    (finalTables_spec witness constraints balanced)

private theorem sourceTables_final_silent {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (witness.tables.take 3).flatMap
      (·.interactionsWith witness.data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply table.interactionsWith_nil_of_channel_not_mem
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [List.map_take, witness.tables_map_component] at mapped
  change table.component ∈ (tables image source).take 3 at mapped
  have length : ((SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.map (·.component)).length = 3 := rfl
  rw [tables, List.take_left' length] at mapped
  obtain ⟨view, member, same⟩ := List.mem_map.mp mapped
  rw [← same]
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp member
  have allowed := SnapshotMemoryEnsemble.view_channels_subset (p := p) source.sail.memorySnapshot id
  intro used
  simpa [OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
    memoryChannel, byteChannel, StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable,
    StaticTable.ofRows, Channel.toRaw] using allowed used

/-- The certified boundary program fixes the final inventory's two ordering endpoints. -/
theorem verifier_final_interactions (env : Environment (ZMod p)) :
    (boundaryVerifier (p := p)).circuitOperations.interactionValuesWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw env =
      [(OrderedBoundary.channel OrderedFinalProvider.channelName).pushedValue OrderedMemoryEnsemble.startKey,
       (OrderedBoundary.channel OrderedFinalProvider.channelName).pulledValue OrderedMemoryEnsemble.endKey] := by
  have original : (boundaryVerifier (p := p)).circuitOperations.interactionsWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw =
      [((OrderedBoundary.channel OrderedFinalProvider.channelName).pushed (const (OrderedMemoryEnsemble.startKey (p := p)))).toRaw,
       ((OrderedBoundary.channel OrderedFinalProvider.channelName).pulled (const (OrderedMemoryEnsemble.endKey (p := p)))).toRaw] := by
    simp [boundaryVerifier, sp1StateVerifierProgram, OrderedBoundaryVerifier.verifierProgram,
      Verifier.ofInteractions, sp1StateVerifierMain, OrderedBoundaryVerifier.main,
      Operations.interactionsWith, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
      OrderedFinalProvider.channelName, stateChannel, byteChannel, exitChannel, circuit_norm]
  rw [Operations.interactionValuesWith, original]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pulled, ProvableType.eval_const]

/-- The final proof view preserves the actual private-channel ledger, including its verifier.
Interaction values depend only on retained cells, even though canonical data changes. -/
theorem finalWitness_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (finalWitness witness).interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw =
      witness.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw := by
  have suffix : witness.tables.flatMap
      (·.interactionsWith witness.data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) =
      (witness.tables.drop 3).flatMap
        (·.interactionsWith witness.data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) := by
    conv_lhs => rw [← List.take_append_drop 3 witness.tables]
    rw [List.flatMap_append, sourceTables_final_silent, List.nil_append]
  have cells : (witness.tables.drop 3).flatMap
      (·.interactionsWith (finalWitness witness).data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) =
      (witness.tables.drop 3).flatMap
        (·.interactionsWith witness.data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) :=
    congrArg List.flatten (List.map_congr_left fun table _ => table.interactionsWith_setData _ _ _)
  have different : (LocalSourceBoundary.checker image source).channel (baseEnsemble (p := p) image source) ≠
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw := by
    intro equal
    apply (LocalSourceBoundary.checker image source).channel_not_mem (baseEnsemble (p := p) image source)
    rw [equal]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have projected := (LocalSourceBoundary.checker image source).project_interactions
    (ens := baseEnsemble image source) witness _ different
  apply Eq.trans ?_ projected
  change (OrderedBoundaryVerifier.verifierProgram OrderedFinalProvider.channelName
      OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).circuitOperations.interactionValuesWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw
      (Environment.fromInput (Input := unit) () (finalWitness witness).data) ++
        (witness.tables.drop 3).flatMap (·.interactionsWith (finalWitness witness).data
          (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) =
    boundaryVerifier.circuitOperations.interactionValuesWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw
      (Environment.fromInput witness.publicInput witness.data) ++
        witness.tables.flatMap (·.interactionsWith witness.data
          (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw)
  rw [suffix, cells, verifier_final_interactions]
  apply congrArg (fun front => front ++ (witness.tables.drop 3).flatMap
    (·.interactionsWith witness.data (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw))
  simp only [OrderedBoundaryVerifier.verifierProgram, Verifier.Program.circuitOperations,
    Verifier.Program.operations, Verifier.ofInteractions_values]
  exact OrderedBoundaryVerifier.interactionValues _ _ _ _ _ _

/-- The final ordering channel is absent from the execution suffix and source membership table. -/
theorem afterFinalTables_silent (image : ProgramImage) (source : ExecutionSnapshot) :
    ∀ component ∈ NativeCore.afterFinalTables (p := p) image ++
        [SnapshotMemoryEnsemble.registerMembership source.sail.memorySnapshot,
          SnapshotMemoryEnsemble.ramMembership source.sail.memorySnapshot],
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉ component.circuit.channels := by
  intro component member
  rcases List.mem_append.mp member with native | fixed
  · exact NativeCore.afterFinalTables_silent image component native
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl
    · change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
        [source.sail.memorySnapshot.registerTable.channel.toRaw]
      simp [StaticTable.channel, MemorySnapshot.registerTable, StaticTable.ofRows,
        OrderedBoundary.channel, OrderedFinalProvider.channelName, Channel.toRaw]
    · change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
        [(InitialMemoryLookup.membership source.sail.memorySnapshot.memory (2 ^ 48)
          "sp1.native.initial_memory").channel.toRaw]
      simp [StaticTable.channel, InitialMemoryLookup.membership,
        OrderedBoundary.channel, OrderedFinalProvider.channelName, Channel.toRaw]

/-- The final inventory has one record per decoded location before any value is grounded.
This includes uniqueness across the register/RAM split and across duplicate physical rows. -/
theorem final_records_locations_nodup {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((FinalMemoryEnsemble.records (finalWitness witness)).map MemoryMsg.locOf).Nodup := by
  apply FinalMemoryEnsemble.inventory.records_locations_nodup_of_tables
    (finalWitness witness) (afterFinalTables_silent image source) (finalTables_spec witness constraints balanced)
  change BalancedInteractions ((finalWitness witness).interactionsWith _)
  rw [finalWitness_interactions]
  exact balanced _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- The final inventory is precisely the negative Memory ledger of its three physical tables. -/
theorem final_memory_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    ((witness.tables.drop 3).take 3).flatMap (·.interactionsWith witness.data memoryChannel.toRaw) =
      (FinalMemoryEnsemble.records (finalWitness witness)).map (memoryChannel.emittedValue (-1)) :=
by
  have cells : ((witness.tables.drop 3).take 3).flatMap (·.interactionsWith witness.data memoryChannel.toRaw) =
      ((witness.tables.drop 3).take 3).flatMap (·.interactionsWith (finalWitness witness).data memoryChannel.toRaw) :=
    congrArg List.flatten (List.map_congr_left fun table _ => table.interactionsWith_setData _ _ _)
  exact cells.trans (FinalMemoryEnsemble.memory_interactions_eq (finalWitness witness))

end SP1Clean.Soundness.LocalCore
