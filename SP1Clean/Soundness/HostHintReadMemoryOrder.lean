import SP1Clean.Soundness.HostHintReadExecutionRows
import SP1Clean.Soundness.LocalCoreMemoryOrder

/-! # Clock bounds and refresh chronology with host RAM accesses retained

The complete source/push/final/pull balance transfers produced-clock bounds to every consumed
record. The original State walk supplies time windows, while the enlarged CPU rows retain all
host RAM touches. No Memory balance is projected to the smaller instruction-only assembly.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance chronologyClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance chronologyLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

private theorem source_ordering
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    LocalCore.OrderingChannels (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) :=
  HostHintQueueBoundary.projected_orderingChannels witness (source_interface source.host.io.hints) constraints balanced

private theorem source_public
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))) :
    (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).publicInput = witness.publicInput := by
  rw [HostLocalCore.localWitness_publicInput, HostHintQueueBoundary.projected_publicInput]

private theorem aligned_push_bounds
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (ordered : List (ExecutionRow p))
    (exhaustive : ordered.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered)
    (rows : List (RowFacts p))
    (alignment : List.Forall₂ AlignedFacts rows (ordered.map (eventFacts witness.data
      (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables (HostHintQueueBoundary.projected witness)) witness.data)))) :
    ∀ row ∈ rows, ∀ message ∈ row.memPushes, MemoryClockBounds message := by
  have checked := HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints witness constraints)
  have ordering := source_ordering witness constraints balanced
  have contract := LocalCore.public_contract_of_byte _ ordering.sourceChecks ordering.verifierByte
  rw [source_public] at contract
  have finalBounds := finalBoundaryStateMessage_bounds _ contract.1
  have finalTime : StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) < 2 ^ 48 :=
    clkNat_lt_of_limbs finalBounds.1 finalBounds.2.1
  have window := LocalCore.ordered_rows_window_bound_of_orderingChannels _ checked ordering ordered exhaustive
  have edges : ExecutionRow.canonEdge (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data =
      ExecutionRow.canonEdge witness.data := funext fun row => row.canonEdge_setData _ _
  rw [edges, source_public] at window
  have windows := window walk
  simp_rw [ExecutionRow.facts_setData _ (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data] at windows
  intro row rowMem message messageMem
  obtain ⟨original, originalMem, aligned⟩ := forall₂_exists_right alignment row rowMem
  obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp originalMem
  obtain ⟨pull, _, touch⟩ := forall₂_exists_left aligned.touches message messageMem
  have pushHi := touch.push_hi
  rw [aligned.statePull, (eventFacts_state_fetch _ _ _).1] at pushHi
  have upper := windows event eventMem
  exact ⟨aligned.pushBound message messageMem, clkHigh_lt_of_timeNat_le (by omega) finalTime⟩

private theorem source_record_bounds
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ record ∈ (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records
      (LocalCore.sourceWitness (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))),
      MemoryClockBounds record := by
  have specs := LocalCore.sourceTables_spec_of_channels _
    (HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints witness constraints))
    (source_ordering witness constraints balanced).byte
    (source_membership_balance witness balanced)
  have authentic := (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records_valid_of_tables _ specs
  intro record member
  have facts := authentic record member
  exact ⟨facts.2.1, clkHigh_lt_of_timeNat_le (le_of_eq facts.2.2.1) (by norm_num)⟩

private theorem refresh_push_bounds
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ pair ∈ LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)),
      MemoryClockBounds pair.2 :=
  LocalCore.memoryRefreshes_push_bounds_of_byte _
    (HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints witness constraints))
    (source_ordering witness constraints balanced).byte

private theorem consumed_bounds
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (rows : List (RowFacts p))
    (pushBounds : ∀ row ∈ rows, ∀ message ∈ row.memPushes, MemoryClockBounds message)
    (projection : ∀ loc, pushesAt rows loc = pushesAt (sourceExecutionRows witness) loc ∧
      pullsAt rows loc = pullsAt (sourceExecutionRows witness) loc) :
    ∀ loc message, message ∈
      Multiset.filter (fun m => MemoryMsg.locOf m = loc)
        (↑(FinalMemoryEnsemble.records (LocalCore.finalWitness
          (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))) : Multiset _) +
      pullsAt rows loc + Multiset.filter (fun m => MemoryMsg.locOf m = loc)
        (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map Prod.fst) : Multiset _) →
      MemoryClockBounds message := by
  have initialBounds := source_record_bounds witness constraints balanced
  have refreshBounds := refresh_push_bounds witness constraints balanced
  intro loc
  have balance := source_execution_memory_balance witness constraints balanced loc
  rw [← (projection loc).1, ← (projection loc).2] at balance
  refine forall_mem_of_balance balance ?_
  intro message member
  rcases Multiset.mem_add.mp member with member | refresh
  · rcases Multiset.mem_add.mp member with initial | push
    · exact initialBounds message (Multiset.mem_coe.mp (Multiset.mem_filter.mp initial).1)
    · obtain ⟨row, rowMem, messageMem, _⟩ := mem_pushesAt.mp push
      exact pushBounds row rowMem message messageMem
  · obtain ⟨pair, pairMem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp (Multiset.mem_filter.mp refresh).1)
    exact refreshBounds pair pairMem

/-- The full host ledger bounds every prior/final record and orders every physical refresh.
It closes the existing engine's row conditions for the enlarged register/RAM footprints. -/
theorem source_memory_chronology
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (ordered : List (ExecutionRow p))
    (exhaustive : ordered.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered)
    (rows : List (RowFacts p))
    (alignment : List.Forall₂ AlignedFacts rows (ordered.map (eventFacts witness.data
      (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables (HostHintQueueBoundary.projected witness)) witness.data))))
    (projection : ∀ loc, pushesAt rows loc = pushesAt (sourceExecutionRows witness) loc ∧
      pullsAt rows loc = pullsAt (sourceExecutionRows witness) loc) :
    LocalCore.MemoryChronology (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) rows := by
  have consumed := consumed_bounds witness constraints balanced rows
    (aligned_push_bounds witness constraints balanced ordered exhaustive walk rows alignment) projection
  have prior : ∀ row ∈ rows, ∀ pull ∈ row.memPulls, MemoryClockBounds pull.1 := by
    intro row rowMem pull pullMem
    exact consumed (MemoryMsg.locOf pull.1) pull.1 (Multiset.mem_add.mpr (Or.inl
      (Multiset.mem_add.mpr (Or.inr (mem_pullsAt.mpr ⟨⟨row, rowMem, pull, pullMem, rfl⟩, rfl⟩)))))
  have refreshPrior : ∀ pair ∈ LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)),
      MemoryClockBounds pair.1 := by
    intro pair pairMem
    exact consumed (MemoryMsg.locOf pair.1) pair.1 (Multiset.mem_add.mpr (Or.inr
      (Multiset.mem_filter.mpr ⟨Multiset.mem_coe.mpr (List.mem_map_of_mem pairMem), rfl⟩)))
  have checked := HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints witness constraints)
  have ordering := source_ordering witness constraints balanced
  have timing := LocalCore.ordered_rows_timing_of_orderingChannels _ checked ordering ordered exhaustive
  have edges : ExecutionRow.canonEdge (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data =
      ExecutionRow.canonEdge witness.data := funext fun row => row.canonEdge_setData _ _
  rw [edges, source_public] at timing
  have times := timing walk
  simp_rw [ExecutionRow.edge_setData _ (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data] at times
  refine ⟨?_, prior, refreshPrior, ?_, LocalCore.memoryRefreshes_order_of_bounds _ checked ordering.byte refreshPrior⟩
  · intro row rowMem
    obtain ⟨original, originalMem, aligned⟩ := forall₂_exists_right alignment row rowMem
    obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp originalMem
    have time := times event eventMem
    have duration : 8 ≤ event.duration := by cases event <;> norm_num [ExecutionRow.duration]
    rw [ExecutionRow.edge_eq_facts] at time
    dsimp only at time
    apply aligned.rowOKCore
    · rw [(eventFacts_state_fetch _ _ _).1, (eventFacts_state_fetch _ _ _).2.1]
      omega
    · rw [(eventFacts_state_fetch _ _ _).1, source_public]
      exact time.1
    · intro access member
      exact (prior row rowMem access.1 (List.of_mem_zip member).1).2
  · intro loc message present
    have member := List.mem_filter.mp (List.mem_of_head? present)
    exact consumed loc message (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl
      (Multiset.mem_filter.mpr ⟨Multiset.mem_coe.mpr member.1, of_decide_eq_true member.2⟩)))))

/-- Constraints and balance construct the complete ordered host footprint and discharge all
Memory clock conditions, without caller-supplied chronology or prior Memory truth. -/
theorem source_ordered_memory_rows (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ (ordered : List (ExecutionRow p)) (rows : List (RowFacts p)),
      ordered.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered ∧
      List.Forall₂ AlignedFacts rows (ordered.map (eventFacts witness.data
        (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data))) ∧
      LocalCore.MemoryChronology (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) rows ∧
      ∀ loc, pushesAt rows loc = pushesAt (sourceExecutionRows witness) loc ∧
        pullsAt rows loc = pullsAt (sourceExecutionRows witness) loc := by
  obtain ⟨ordered, rows, exhaustive, walk, alignment, projection⟩ :=
    source_ordered_aligned_rows valid witness constraints balanced
  exact ⟨ordered, rows, exhaustive, walk, alignment,
    source_memory_chronology witness constraints balanced ordered exhaustive walk rows alignment projection,
    projection⟩

/-- The complete physical endpoints also balance any occurrence-preserving aligned row ledger. -/
theorem frontier_balance
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (rows : List (RowFacts p))
    (projection : ∀ loc, pushesAt rows loc = pushesAt (sourceExecutionRows witness) loc ∧
      pullsAt rows loc = pullsAt (sourceExecutionRows witness) loc) (loc : MemLoc) :
    optMS (LocalCore.memoryInitialFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc) +
      pushesAt rows loc + Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map Prod.snd) : Multiset _) =
    optMS (LocalCore.memoryFinalFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc) +
      pullsAt rows loc + Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map Prod.fst) : Multiset _) := by
  have ledger := source_execution_memory_projection witness constraints balanced loc
  rw [(projection loc).1, (projection loc).2, add_assoc, add_assoc, ledger.1, ledger.2]
  exact source_memory_frontier_balance witness constraints balanced loc

/-- The installed host AIR constructs an exhaustive Memory ledger with all refreshes removed.
Every CPU and host touch survives; rewritten priors and the final frontier preserve values and
locations and only move clocks earlier. Semantic step/frame facts remain separate obligations. -/
theorem source_memory_refresh_free (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ (ordered : List (ExecutionRow p)) (rows : List (RowFacts p))
      (touches : List (List (Touch p))) (frontier : MemLoc → Option (MemoryMsg (ZMod p))),
      ordered.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered ∧
      List.Forall₂ AlignedFacts rows (ordered.map (eventFacts witness.data
        (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data))) ∧
      LocalCore.MemoryChronology (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) rows ∧
      List.Forall₂ (List.Forall₂ PullRewrite) (rows.map rowTouches) touches ∧
      (∀ loc, optMS (LocalCore.memoryInitialFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc) +
          pushesAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc =
        optMS (frontier loc) + pullsAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc) ∧
      (rows.zip touches).map Prod.fst = rows ∧
      (∀ loc message, LocalCore.memoryFinalFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = some message →
        ∃ earlier, frontier loc = some earlier ∧ MemoryMsg.locOf earlier = MemoryMsg.locOf message ∧
          earlier.value = message.value ∧ MemoryMsg.timeNat earlier ≤ MemoryMsg.timeNat message) := by
  obtain ⟨ordered, rows, exhaustive, walk, alignment, chronology, projection⟩ :=
    source_ordered_memory_rows valid witness constraints balanced
  obtain ⟨touches, frontier, rewritten, balance, retained, finalRewrite⟩ := refresh_free_of_balance rows
    (LocalCore.memoryInitialFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (LocalCore.memoryFinalFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    _ chronology.rowOK (frontier_balance witness constraints balanced rows projection)
    (LocalCore.memoryRefreshes_preserve _) chronology.refreshOrder
  exact ⟨ordered, rows, touches, frontier, exhaustive, walk, alignment, chronology,
    rewritten, balance, retained, finalRewrite⟩

end SP1Clean.Soundness.HostHintReadCPU
