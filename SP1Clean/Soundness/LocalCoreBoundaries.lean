import SP1Clean.Soundness.LocalCoreEnsemble
import SP1Clean.Soundness.NativeCoreBoundaries

/-! # Source-boundary facts from the actual local-shard AIR

The proof projection retains every physical table and the common prover data. It only restricts
the verifier to the source ordering channel. Raw constraints and the assembly's own balance prove
source-value authentication, distinct locations, the exact Memory ledger, and canonical public
endpoints. No provider-specification or source-memory-truth premise is accepted by these results.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The source inventory is a proof view of the physical assembly, with no replaced rows. -/
def sourceWitness {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    EnsembleWitness ((SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).ensemble
      (afterSourceTables image source) [] (baseEnsemble image source).unique_names) :=
  EnsembleWitness.ofTables _ witness.tables () witness.tables_map_component

/-- Source records use Byte guarantees and fixed-register membership, independently of Memory balance. -/
theorem sourceTables_spec_of_channels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (membership : ∀ channel ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot,
      witness.BalancedChannel channel) :
    ∀ table ∈ (sourceWitness witness).tables.take (SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.length,
      table.Spec witness.data := by
  intro table member row rowMem
  have componentMem : table.component ∈ (SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.map (·.component) := by
    have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [List.map_take, (sourceWitness witness).tables_map_component] at mapped
    simpa only [OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
      List.take_left', List.length_map] using mapped
  obtain ⟨view, viewMem, same⟩ := List.mem_map.mp componentMem
  have tableMem : table ∈ witness.tables := List.mem_of_mem_take member
  have byte := bytes table tableMem row rowMem
  have register := (membership_guarantees_of_balance image source witness constraints _
    (List.mem_cons_self ..) (membership _ (List.mem_cons_self ..))).2 table tableMem row rowMem
  have ram := (membership_guarantees_of_balance image source witness constraints _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (membership _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))).2 table tableMem row rowMem
  have checked := constraints table tableMem row rowMem
  rw [← same] at byte register ram checked ⊢
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
  exact SnapshotMemoryEnsemble.view_spec source.sail.memorySnapshot id _ checked byte register ram

theorem sourceTables_spec {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ (sourceWitness witness).tables.take (SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.length,
      table.Spec witness.data :=
  sourceTables_spec_of_channels witness constraints
    (fun table member => ((finishedChannel_guarantees image source witness constraints balanced).2 table member).1)
    (fun channel known => balanced channel (by
      simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons,
        List.not_mem_nil, or_false] at known
      rcases known with rfl | rfl <;> simp [ensemble, PublicVerifier.install, baseEnsemble]))

/-- Every physical source record authenticates its complete value against the fixed source. -/
theorem source_records_authentic {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ record ∈ (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness),
      MemoryBoundary.SnapshotSpec source.sail.memorySnapshot record :=
  (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records_valid_of_tables (sourceWitness witness)
    (sourceTables_spec witness constraints balanced)

/-- The interaction-only boundary program has exactly the fixed source-order endpoints. -/
theorem verifier_source_interactions (env : Environment (ZMod p)) :
    (boundaryVerifier (p := p)).circuitOperations.interactionValuesWith
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw env =
      [(OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).pushedValue OrderedMemoryEnsemble.startKey,
       (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).pulledValue OrderedMemoryEnsemble.endKey] := by
  have original : (boundaryVerifier (p := p)).circuitOperations.interactionsWith
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw =
      [((OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).pushed
        (const (OrderedMemoryEnsemble.startKey (p := p)))).toRaw,
       ((OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).pulled
        (const (OrderedMemoryEnsemble.endKey (p := p)))).toRaw] := by
    simp [boundaryVerifier, sp1StateVerifierProgram, OrderedBoundaryVerifier.verifierProgram,
      Verifier.ofInteractions, sp1StateVerifierMain, OrderedBoundaryVerifier.main,
      Operations.interactionsWith, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
      OrderedFinalProvider.channelName, stateChannel, byteChannel, exitChannel, circuit_norm]
  rw [Operations.interactionValuesWith, original]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pulled, ProvableType.eval_const]

theorem sourceWitness_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (sourceWitness witness).interactionsWith (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw =
      witness.interactionsWith (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw := by
  have different : (LocalSourceBoundary.checker image source).channel (baseEnsemble (p := p) image source) ≠
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw := by
    intro equal
    apply (LocalSourceBoundary.checker image source).channel_not_mem (baseEnsemble (p := p) image source)
    rw [equal]
    exact List.mem_cons_self ..
  have projected := (LocalSourceBoundary.checker image source).project_interactions
    (ens := baseEnsemble image source) witness _ different
  apply Eq.trans ?_ projected
  change _ = boundaryVerifier.circuitOperations.interactionValuesWith _
    (Environment.fromInput witness.publicInput witness.data) ++ witness.tableContext.interactionsWith _
  rw [verifier_source_interactions]
  apply congrArg (fun front => front ++ witness.tableContext.interactionsWith
    (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw)
  change (OrderedBoundaryVerifier.verifierProgram _ _ _).circuitOperations.interactionValuesWith _ _ = _
  simp only [OrderedBoundaryVerifier.verifierProgram, Verifier.Program.circuitOperations,
    Verifier.Program.operations, Verifier.ofInteractions_values]
  exact OrderedBoundaryVerifier.interactionValues _ _ _ _ _ _

/-- The source ordering channel is absent from both the native suffix and fixed membership rows. -/
theorem afterSourceTables_silent (image : ProgramImage) (source : ExecutionSnapshot) :
    ∀ component ∈ afterSourceTables (p := p) image source,
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ∉ component.circuit.channels := by
  intro component member
  rcases List.mem_append.mp member with native | fixed
  · exact NativeCore.afterInitialTables_silent image component native
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl
    · change (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ∉
        [source.sail.memorySnapshot.registerTable.channel.toRaw]
      simp [StaticTable.channel, MemorySnapshot.registerTable, StaticTable.ofRows,
        OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName, Channel.toRaw]
    · change (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ∉
        [(InitialMemoryLookup.membership source.sail.memorySnapshot.memory (2 ^ 48)
          "sp1.native.initial_memory").channel.toRaw]
      simp [StaticTable.channel, InitialMemoryLookup.membership,
        OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName, Channel.toRaw]

/-- Distinct source locations follow from the combined AIR, including across register/RAM tables. -/
theorem source_records_locations_nodup {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness)).map MemoryMsg.locOf).Nodup := by
  apply (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records_locations_nodup_of_tables
    (sourceWitness witness) (afterSourceTables_silent image source) (sourceTables_spec witness constraints balanced)
  change BalancedInteractions ((sourceWitness witness).interactionsWith _)
  rw [sourceWitness_interactions]
  exact balanced _ (List.mem_append_left _ (List.mem_cons_self ..))

/-- The source tables emit exactly the decoded records, preserving every physical occurrence. -/
theorem source_memory_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (witness.tables.take (SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.length).flatMap
        (·.interactionsWith witness.data memoryChannel.toRaw) =
      ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness)).map memoryChannel.pushedValue :=
  (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).memory_interactions_eq (sourceWitness witness)
    memoryChannel.pushedValue (SnapshotMemoryEnsemble.recordFor_interactions source.sail.memorySnapshot)

/-- Public endpoints are canonical, the incoming token matches the full source, and its finite
program, platform, initialization, ROM, and range checks pass without caller-supplied truth. -/
theorem public_contract_of_byte {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (sourceChecks : witness.BalancedChannel (sourceChannel image source))
    (byte : (ensemble image source).VerifierChannelGuarantees witness.publicInput witness.data byteChannel.toRaw) :
    witness.publicInput.LimbBounds ∧ ExecutionSourceValid image source ∧
      witness.publicInput.SourceFor source ∧ witness.publicInput.PreservesStoppedClock source := by
  have boundaryByte := (Verifier.Program.andThen_channelGuarantees boundaryVerifier
    ((LocalSourceBoundary.checker image source).program (baseEnsemble image source))
    byteChannel.toRaw (Environment.fromInput witness.publicInput witness.data)).mp byte
  exact ⟨boundaryVerifier_limbBounds _ _ boundaryByte.1, (source_balanced_iff witness).mp sourceChecks⟩

/-- The complete witness supplies the verifier's Byte guarantees. -/
theorem public_contract {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    witness.publicInput.LimbBounds ∧ ExecutionSourceValid image source ∧
      witness.publicInput.SourceFor source ∧ witness.publicInput.PreservesStoppedClock source :=
  public_contract_of_byte witness
    (balanced _ (List.mem_append_right _ (List.mem_singleton_self _)))
    (finishedChannel_guarantees image source witness constraints balanced).1.1

/-- Canonical public endpoints, complete source validity, and incoming-state binding. -/
theorem public_boundary {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    witness.publicInput.LimbBounds ∧ ExecutionSourceValid image source ∧ witness.publicInput.SourceFor source := by
  have checked := public_contract witness constraints balanced
  exact ⟨checked.1, checked.2.1, checked.2.2.1⟩

/-- A stopped source cannot advance the natural State clock. -/
theorem stopped_clock {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (stopped : source.host.exitCode ≠ none) :
    clkNat witness.publicInput.final_clk_high witness.publicInput.final_clk_low =
      clkNat witness.publicInput.init_clk_high witness.publicInput.init_clk_low := by
  have same := (public_contract witness constraints balanced).2.2.2 stopped
  rw [same.1, same.2]

end SP1Clean.Soundness.LocalCore
