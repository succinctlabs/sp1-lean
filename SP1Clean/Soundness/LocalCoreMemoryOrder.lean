import SP1Clean.Soundness.LocalCoreTouches
import SP1Clean.Soundness.CoreMemoryChronology

/-! # Prior-record bounds and refresh chronology of a local shard

Every produced Memory record has two bounded clock limbs: initial records have time zero,
execution writes lie inside the State walk's bounded clock interval, and refresh writes carry
Byte-checked limbs. The exact Memory balance transfers those bounds to every consumed record,
including refresh priors and the final frontier. This closes the timestamp-comparison premises
without assuming Memory truth, and supplies refresh elimination with its complete chronology.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow AlignedFacts MemoryClockBounds rowTouches walk_rank_bound memoryBump_row_order)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Every active event's complete access window precedes the public final clock. -/
theorem ordered_rows_window_bound_of_orderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (ordering : OrderingChannels witness)
    (ordered : List (ExecutionRow p)) (exhaustive : ordered.Perm (executionRows witness))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered) :
    ∀ row ∈ ordered, StateMsg.timeNat (row.facts witness.data).statePull + 8 ≤
      StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) := by
  have bounded := (walk_rank_bound _ StateMsg.timeNat walk (by
    intro row member
    have good := executionRows_good_of_orderingChannels witness constraints ordering (exhaustive.mem_iff.mp member)
    dsimp only [ExecutionRow.canonEdge]
    rw [timeNat_canonState good.1.1, timeNat_canonState good.2.1]
    exact (executionRows_advancing_of_orderingChannels witness constraints ordering (exhaustive.mem_iff.mp member)).1.1.le)).2
  intro row member
  have upper := bounded row member
  have good := executionRows_good_of_orderingChannels witness constraints ordering (exhaustive.mem_iff.mp member)
  dsimp only [ExecutionRow.canonEdge] at upper
  rw [timeNat_canonState good.2.1] at upper
  have step := (executionRows_advancing_of_orderingChannels witness constraints ordering (exhaustive.mem_iff.mp member)).2
  have duration : 8 ≤ row.duration := by cases row <;> norm_num [ExecutionRow.duration]
  rw [ExecutionRow.edge_eq_facts] at step upper
  dsimp only at step upper
  omega

/-- The complete local AIR supplies the State/Byte inputs to the window bound. -/
theorem ordered_rows_window_bound {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (ordered : List (ExecutionRow p)) (exhaustive : ordered.Perm (executionRows witness))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered) :
    ∀ row ∈ ordered, StateMsg.timeNat (row.facts witness.data).statePull + 8 ≤
      StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) :=
  ordered_rows_window_bound_of_orderingChannels witness constraints
    (orderingChannels_of_balanced witness constraints balanced) ordered exhaustive walk

/-- Strict State progress and the stopped-source verifier condition exclude every active
ordinary, HALT, and syscall occurrence. Padding and administrative rows remain admissible. -/
theorem executionRows_nil_of_stopped {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (stopped : source.host.exitCode ≠ none) : executionRows witness = [] := by
  obtain ⟨ordered, exhaustive, walk⟩ := executionRows_ordered witness constraints balanced
  cases ordered with
  | nil => exact List.perm_nil.mp exhaustive.symm
  | cons event rest =>
    have upper := ordered_rows_window_bound witness constraints balanced (event :: rest)
      exhaustive walk event List.mem_cons_self
    have good := executionRows_good witness constraints balanced (exhaustive.mem_iff.mp List.mem_cons_self)
    have first := congrArg StateMsg.timeNat walk.1
    change StateMsg.timeNat (canonState (event.edge witness.data).1) = _ at first
    rw [timeNat_canonState good.1.1, ExecutionRow.edge_eq_facts] at first
    have same : StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) =
        StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) :=
      stopped_clock witness constraints balanced stopped
    dsimp only at first
    omega

/-- Every actual MemoryBump push has canonical clock limbs, before any received Memory fact. -/
theorem memoryRefreshes_push_bounds_of_byte {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw) :
    ∀ pair ∈ memoryRefreshes witness, MemoryClockBounds pair.2 := by
  intro pair member
  obtain ⟨row, rowMem, pairMem⟩ := List.mem_flatMap.mp member
  obtain rfl := List.mem_singleton.mp pairMem
  obtain ⟨mapped, real⟩ := List.mem_filter.mp rowMem
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  exact memoryBump_pushedMessage_clkFacts_of_component _ witness.data (systemTable_component witness 0)
    (systemTable_constraints witness constraints 0)
    (bytes _ (systemTable_mem witness 0))
    physicalMem (of_decide_eq_true real)

/-- The complete local AIR supplies the Byte bounds of all physical refresh pushes. -/
theorem memoryRefreshes_push_bounds {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ pair ∈ memoryRefreshes witness, MemoryClockBounds pair.2 :=
  memoryRefreshes_push_bounds_of_byte witness constraints
    (orderingChannels_of_balanced witness constraints balanced).byte

private theorem aligned_push_bounds {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (ordered : List (ExecutionRow p)) (exhaustive : ordered.Perm (executionRows witness))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered)
    (rows : List (RowFacts p))
    (alignment : List.Forall₂ AlignedFacts rows (ordered.map (ExecutionRow.facts witness.data))) :
    ∀ row ∈ rows, ∀ message ∈ row.memPushes, MemoryClockBounds message := by
  have finalBounds := finalBoundaryStateMessage_bounds _ (public_boundary witness constraints balanced).1
  have finalTime : StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) < 2 ^ 48 :=
    clkNat_lt_of_limbs finalBounds.1 finalBounds.2.1
  intro row rowMem message messageMem
  obtain ⟨original, originalMem, aligned⟩ := forall₂_exists_right alignment row rowMem
  obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp originalMem
  obtain ⟨pull, _, touch⟩ := forall₂_exists_left aligned.touches message messageMem
  have pushHi := touch.push_hi
  rw [aligned.statePull] at pushHi
  have window := ordered_rows_window_bound witness constraints balanced ordered exhaustive walk event eventMem
  exact ⟨aligned.pushBound message messageMem, clkHigh_lt_of_timeNat_le (by omega) finalTime⟩

/-- Clock bounds for every record consumed by the exact per-location ledger. In particular this
includes final records, although the final tables make no received Memory guarantee. -/
theorem memory_consumed_bounds {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (ordered : List (ExecutionRow p)) (exhaustive : ordered.Perm (executionRows witness))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered)
    (rows : List (RowFacts p))
    (alignment : List.Forall₂ AlignedFacts rows (ordered.map (ExecutionRow.facts witness.data))) :
    ∀ loc message, message ∈ optMS (memoryFinalFrontier witness loc) + pullsAt rows loc +
      Multiset.filter (fun m => MemoryMsg.locOf m = loc)
        (↑((memoryRefreshes witness).map Prod.fst) : Multiset _) → MemoryClockBounds message := by
  have pushBounds := aligned_push_bounds witness constraints balanced ordered exhaustive walk rows alignment
  have refreshBounds := memoryRefreshes_push_bounds witness constraints balanced
  intro loc
  refine forall_mem_of_balance (memory_balance_of_row_projection witness constraints balanced
    ordered exhaustive rows (alignment.imp (fun _ _ aligned => aligned.memory)) loc) ?_
  intro message member
  rcases Multiset.mem_add.mp member with member | refresh
  · rcases Multiset.mem_add.mp member with initial | push
    · have authentic := (memoryInitialFrontier_content witness constraints balanced (mem_optMS.mp initial)).2.1
      exact ⟨authentic.2.1, clkHigh_lt_of_timeNat_le (le_of_eq authentic.2.2.1) (by norm_num)⟩
    · obtain ⟨row, rowMem, messageMem, _⟩ := mem_pushesAt.mp push
      exact pushBounds row rowMem message messageMem
  · obtain ⟨pair, pairMem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp (Multiset.mem_filter.mp refresh).1)
    exact refreshBounds pair pairMem

-- Specialize at the physical table before introducing prior bounds; substituting a fully
-- decoded row through those bounds otherwise forces expensive circuit normalization.
private theorem active_refresh_order {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    {row : MemoryBumpChip.Inputs (ZMod p)}
    (member : row ∈ activeSystemRows (systemTable witness 0) (memoryBumpRow witness.data) (·.is_real)) :
    MemoryClockBounds (MemoryBumpChip.pulledMessage row) →
      MemoryMsg.timeNat (MemoryBumpChip.pulledMessage row) < MemoryMsg.timeNat (MemoryBumpChip.pushedMessage row) := by
  obtain ⟨mapped, real⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  exact memoryBump_row_order _ witness.data (systemTable_component witness 0)
    (systemTable_constraints witness constraints 0)
    (bytes _ (systemTable_mem witness 0))
    physicalMem (of_decide_eq_true real)

/-- Byte-checked refresh comparisons become strict natural-time order once the enclosing
Memory ledger bounds their actual prior records. -/
theorem memoryRefreshes_order_of_bounds {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (prior : ∀ pair ∈ memoryRefreshes witness, MemoryClockBounds pair.1) :
    ∀ pair ∈ memoryRefreshes witness, MemoryMsg.timeNat pair.1 < MemoryMsg.timeNat pair.2 := by
  intro pair member
  have bounds := prior pair member
  obtain ⟨row, rowMem, pairMem⟩ := List.mem_flatMap.mp member
  obtain rfl := List.mem_singleton.mp pairMem
  exact active_refresh_order witness constraints bytes rowMem bounds

/-- The complete local chronology supplied to the mixed-row grounding engine. Clock facts on
priors and final records are conclusions of balance, separate from their eventual value truth. -/
structure MemoryChronology {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (rows : List (RowFacts p)) : Prop where
  rowOK : ∀ row ∈ rows, RowOKCore (StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput)) row
  priorBounds : ∀ row ∈ rows, ∀ pull ∈ row.memPulls, MemoryClockBounds pull.1
  refreshBounds : ∀ pair ∈ memoryRefreshes witness, MemoryClockBounds pair.1
  finalBounds : ∀ loc message, memoryFinalFrontier witness loc = some message → MemoryClockBounds message
  refreshOrder : ∀ pair ∈ memoryRefreshes witness, MemoryMsg.timeNat pair.1 < MemoryMsg.timeNat pair.2

/-- Memory balance discharges the prior-record bounds and every actual refresh comparison,
completing the aligned rows' structural contract for timed grounding. -/
theorem ordered_rows_chronology {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (ordered : List (ExecutionRow p)) (exhaustive : ordered.Perm (executionRows witness))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered)
    (rows : List (RowFacts p))
    (alignment : List.Forall₂ AlignedFacts rows (ordered.map (ExecutionRow.facts witness.data))) :
    MemoryChronology witness rows := by
  have consumed := memory_consumed_bounds witness constraints balanced ordered exhaustive walk rows alignment
  have prior : ∀ row ∈ rows, ∀ pull ∈ row.memPulls, MemoryClockBounds pull.1 := by
    intro row rowMem pull pullMem
    exact consumed (MemoryMsg.locOf pull.1) pull.1 (Multiset.mem_add.mpr (Or.inl
      (Multiset.mem_add.mpr (Or.inr (mem_pullsAt.mpr ⟨⟨row, rowMem, pull, pullMem, rfl⟩, rfl⟩)))))
  have refreshPrior : ∀ pair ∈ memoryRefreshes witness, MemoryClockBounds pair.1 := by
    intro pair pairMem
    exact consumed (MemoryMsg.locOf pair.1) pair.1 (Multiset.mem_add.mpr (Or.inr
      (Multiset.mem_filter.mpr ⟨Multiset.mem_coe.mpr (List.mem_map_of_mem pairMem), rfl⟩)))
  refine ⟨?_, prior, refreshPrior, ?_, memoryRefreshes_order_of_bounds witness constraints
    (orderingChannels_of_balanced witness constraints balanced).byte refreshPrior⟩
  · intro row rowMem
    obtain ⟨original, originalMem, aligned⟩ := forall₂_exists_right alignment row rowMem
    obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp originalMem
    have timing := ordered_rows_timing witness constraints balanced ordered exhaustive walk event eventMem
    have duration : 8 ≤ event.duration := by cases event <;> norm_num [ExecutionRow.duration]
    rw [ExecutionRow.edge_eq_facts] at timing
    dsimp only at timing
    exact aligned.rowOKCore _ (by omega) timing.1 (fun touch member =>
      (prior row rowMem touch.1 (List.of_mem_zip member).1).2)
  · intro loc message present
    exact consumed loc message (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr
      (Or.inl (mem_optMS.mpr present)))))

/-- Raw constraints and balance construct an exhaustive State walk with aligned Memory rows and
complete chronology. All prior bounds and refresh comparisons are derived internally. -/
theorem ordered_memory_rows {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ (ordered : List (ExecutionRow p)) (rows : List (RowFacts p)),
      ordered.Perm (executionRows witness) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered ∧
      List.Forall₂ AlignedFacts rows (ordered.map (ExecutionRow.facts witness.data)) ∧
      MemoryChronology witness rows := by
  obtain ⟨ordered, rows, exhaustive, walk, alignment, _⟩ := ordered_aligned_rows valid witness constraints balanced
  exact ⟨ordered, rows, exhaustive, walk, alignment,
    ordered_rows_chronology witness constraints balanced ordered exhaustive walk rows alignment⟩

/-- The original physical execution rows' prior clocks are bounded, regardless of their touch
order or read currency points. This includes every active syscall row. -/
theorem executionRows_prior_bounds {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ event ∈ executionRows witness, ∀ pull ∈ (event.facts witness.data).memPulls,
      MemoryClockBounds pull.1 := by
  obtain ⟨ordered, rows, exhaustive, _, alignment, chronology⟩ := ordered_memory_rows valid witness constraints balanced
  intro event eventMem pull pullMem
  obtain ⟨row, rowMem, aligned⟩ := forall₂_exists_left alignment (event.facts witness.data)
    (List.mem_map_of_mem (exhaustive.mem_iff.mpr eventMem))
  have mapped := aligned.memory.pulls.mem_iff.mpr (List.mem_map_of_mem pullMem)
  obtain ⟨prior, priorMem, same⟩ := List.mem_map.mp mapped
  exact same ▸ chronology.priorBounds row rowMem prior priorMem

/-- Every actual refresh advances natural time, from the checked image and raw AIR alone. -/
theorem memoryRefreshes_ordered {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ pair ∈ memoryRefreshes witness, MemoryMsg.timeNat pair.1 < MemoryMsg.timeNat pair.2 := by
  obtain ⟨_, _, _, _, _, chronology⟩ := ordered_memory_rows valid witness constraints balanced
  exact chronology.refreshOrder

/-- The local AIR constructs a refresh-free Memory ledger in exhaustive execution order.
Rewrites retain each read time and pushed record, preserve prior/final values and locations,
and only move prior/final timestamps earlier. The execution step/frame and host proofs remain
separate consumers of this structural result. -/
theorem memory_refresh_free {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ (ordered : List (ExecutionRow p)) (rows : List (RowFacts p))
      (touches : List (List (Touch p))) (final : MemLoc → Option (MemoryMsg (ZMod p))),
      ordered.Perm (executionRows witness) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered ∧
      List.Forall₂ AlignedFacts rows (ordered.map (ExecutionRow.facts witness.data)) ∧
      MemoryChronology witness rows ∧
      List.Forall₂ (List.Forall₂ PullRewrite) (rows.map rowTouches) touches ∧
      (∀ loc, optMS (memoryInitialFrontier witness loc) +
          pushesAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc =
        optMS (final loc) + pullsAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc) ∧
      (rows.zip touches).map Prod.fst = rows ∧
      (∀ loc message, memoryFinalFrontier witness loc = some message →
        ∃ earlier, final loc = some earlier ∧ MemoryMsg.locOf earlier = MemoryMsg.locOf message ∧
          earlier.value = message.value ∧ MemoryMsg.timeNat earlier ≤ MemoryMsg.timeNat message) := by
  obtain ⟨ordered, rows, exhaustive, walk, alignment, chronology⟩ := ordered_memory_rows valid witness constraints balanced
  obtain ⟨touches, final, rewrite, balance, occurrences, finalRewrite⟩ := memory_refresh_free_of_chronology
    witness constraints balanced ordered exhaustive rows (alignment.imp (fun _ _ aligned => aligned.memory))
    _ chronology.rowOK chronology.refreshOrder
  exact ⟨ordered, rows, touches, final, exhaustive, walk, alignment, chronology,
    rewrite, balance, occurrences, finalRewrite⟩

end SP1Clean.Soundness.LocalCore
