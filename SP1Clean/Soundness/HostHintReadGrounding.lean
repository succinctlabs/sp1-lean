import SP1Clean.Soundness.HostHintReadMemoryOrder
import SP1Clean.Soundness.LocalCoreTransport

/-! # Grounding carrier for complete CPU and hint RAM footprints

The actual host AIR supplies read windows, prior bounds, canonical State endpoints, and the
refresh-free Memory balance. The shared execution carrier retains each event's full footprint;
its semantic premises concern those events, independently of alignment and refresh details.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance groundingClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance groundingLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

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

private theorem source_program
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (balanced : witness.BalancedChannels) :
    (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).BalancedChannel programChannel.toRaw := by
  change BalancedInteractions ((HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).interactionsWith _)
  rw [HostLocalCore.localWitness_program _ (source_program_silent source)]
  exact HostHintQueueBoundary.projected_core_balancedChannel witness balanced _
    (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])

private theorem source_event_readsInWindow (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) :
    ReadsInWindow (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) := by
  have original := LocalCore.executionRows_readsInWindow_of_program valid _
    (HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints witness constraints))
    (source_program witness balanced) member
  rw [event.facts_setData (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data] at original
  have words := source_touches_at valid witness constraints balanced event
  rw [ExecutionRow.edge_eq_facts] at words
  intro pull pullMem
  rcases List.mem_append.mp pullMem with old | added
  · exact original pull old
  · obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp added
    exact ⟨(words row rowMem).1.read_lo, (words row rowMem).1.read_hi⟩

private theorem canonical_times
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (words : List (HintReadCoverage.Row (p := p))) :
    StateMsg.timeNat (canonState (eventFacts witness.data words event).statePull) =
        StateMsg.timeNat (eventFacts witness.data words event).statePull ∧
    StateMsg.pcBits (canonState (eventFacts witness.data words event).statePull) =
        StateMsg.pcBits (eventFacts witness.data words event).statePull ∧
    StateMsg.timeNat (canonState (eventFacts witness.data words event).statePush) =
        StateMsg.timeNat (eventFacts witness.data words event).statePush ∧
    StateMsg.pcBits (canonState (eventFacts witness.data words event).statePush) =
        StateMsg.pcBits (eventFacts witness.data words event).statePush := by
  have good := LocalCore.executionRows_good_of_orderingChannels _
    (HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints witness constraints))
    (source_ordering witness constraints balanced) member
  rw [event.edge_setData (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data,
    ExecutionRow.edge_eq_facts] at good
  simp only [(eventFacts_state_fetch _ _ _).1, (eventFacts_state_fetch _ _ _).2.1]
  exact ⟨timeNat_canonState good.1.1, pcBits_canonState good.1.2.1 good.1.2.2,
    timeNat_canonState good.2.1, pcBits_canonState good.2.2.1 good.2.2.2⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem original_prior_bounds {aligned original : RowFacts p} (facts : AlignedFacts aligned original)
    (prior : ∀ pull ∈ aligned.memPulls, MemoryMsg.ClkBound pull.1) :
    ∀ pull ∈ original.memPulls, MemoryMsg.ClkBound pull.1 := by
  intro pull member
  have mapped := facts.memory.pulls.mem_iff.mpr (List.mem_map_of_mem member)
  obtain ⟨matched, matchedMem, same⟩ := List.mem_map.mp mapped
  exact same ▸ prior matched matchedMem

/-- The shared carrier specialized to the actual instruction and hint-word footprints. -/
abbrev GroundingCarrier
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))) :=
  NativeCore.ExecutionCarrier
    (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.projected witness)) witness.data))
    (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput)
    (LocalCore.memoryInitialFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (LocalCore.memoryFinalFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))

private theorem eventFacts_canonEdge (data : ProverData (ZMod p)) (words : List (HintReadCoverage.Row (p := p))) :
    (fun event => (canonState (eventFacts data words event).statePull,
      canonState (eventFacts data words event).statePush)) = ExecutionRow.canonEdge data := by
  simp only [(eventFacts_state_fetch _ _ _).1, (eventFacts_state_fetch _ _ _).2.1]
  exact ExecutionRow.canonEdge_facts data

/-- The same ordered CPU tape supplies both memory grounding and queue-prefix replay. -/
theorem GroundingCarrier.cpuWalk
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness) :
    Walk.IsWalk (ExecutionRow.canonEdge witness.data) (initialBoundaryStateMessage witness.publicInput)
      (finalBoundaryStateMessage witness.publicInput) carrier.ordered := by
  have walk := carrier.eventWalk
  rw [eventFacts_canonEdge] at walk
  exact walk

/-- The installed host AIR supplies the final carrier, with all host Memory accesses retained.
Ordering, read alignment, refresh elimination, and canonical State transport are internal. -/
theorem source_grounding_carrier (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    Nonempty (GroundingCarrier witness) := by
  obtain ⟨ordered, rows, touches, frontier, exhaustive, walk, alignment, chronology,
    rewrite, balance, _, finalRewrite⟩ := source_memory_refresh_free valid witness constraints balanced
  have paired : List.Forall₂ (fun newer original => WindowAligned newer original ∧
      RowOKCore (StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput)) newer ∧
      newer.statePull = canonState original.statePull ∧ newer.statePush = canonState original.statePush)
      (rewrittenRows rows touches) (ordered.map (eventFacts witness.data
        (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables (HostHintQueueBoundary.projected witness)) witness.data))) := by
    apply rewriteRows_forall₂ alignment rewrite
    intro row rowMem original originalMem ts localAlignment rewritten
    obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp originalMem
    have active := exhaustive.mem_iff.mp eventMem
    have ok := chronology.rowOK row rowMem
    rw [source_public] at ok
    have canon := canonical_times witness constraints balanced event active
      (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables (HostHintQueueBoundary.projected witness)) witness.data)
    rw [← localAlignment.statePull, ← localAlignment.statePush] at canon
    have prior := fun pull member => (chronology.priorBounds row rowMem pull member).1
    have semantic := localAlignment.windowAligned
      (source_event_readsInWindow valid witness constraints balanced event active)
      (original_prior_bounds localAlignment prior)
    have transported := semantic.pullRewrite ok.touches.length_eq rewritten
    refine ⟨transported.stateRespell canon.1 canon.2.1 canon.2.2.1 canon.2.2.2,
      rowOKCore_stateRespell canon.1 canon.2.2.1 (rewritten_core ok prior rewritten), ?_, ?_⟩
    · exact congrArg canonState localAlignment.statePull
    · exact congrArg canonState localAlignment.statePush
  refine ⟨⟨ordered, rewrittenRows rows touches, frontier, exhaustive,
    paired.imp (fun _ _ facts => facts.1), ?_, ?_, ?_, ?_, finalRewrite⟩⟩
  · intro row member
    obtain ⟨_, _, facts⟩ := forall₂_exists_right paired row member
    exact facts.2.1
  · have edges := List.forall₂_map_right_iff.mp (paired.imp (fun _ _ facts => facts.2.2))
    exact Walk.isWalk_forall₂ (ExecutionRow.canonEdge witness.data)
      (fun row : RowFacts p => (row.statePull, row.statePush))
      (fun event row => row.statePull = canonState (eventFacts witness.data
          (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).statePull ∧
        row.statePush = canonState (eventFacts witness.data
          (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).statePush)
      (fun related => by
        dsimp only [ExecutionRow.canonEdge]
        rw [ExecutionRow.edge_eq_facts]
        exact Prod.ext related.1.symm related.2.symm) edges.flip walk
  · rw [eventFacts_canonEdge]
    exact walk
  · intro loc
    rw [(rewritten_memory rows touches loc).1, (rewritten_memory rows touches loc).2]
    exact balance loc

/-- The checked source and complete host AIR supply genesis and all structural grounding facts.
The remaining semantic premises are step/frame facts for the original events' full footprints.
The result authenticates their original operands at read time, including every added RAM word;
alignment, canonicalization, and the rewritten prior records are internal to the proof. -/
theorem GroundingCarrier.ground_of_steps (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (initial : trajectory 0 = some source.sail.realize)
    (steps : ∀ event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)),
      LocalStepFactG (image.toGuestProgram valid) trajectory source.sail.realize carrier.timeline
          (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
            (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) ∧
      FrameFactG (image.toGuestProgram valid) trajectory source.sail.realize carrier.timeline
          (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
            (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event)) :
    (∀ event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)),
      LocalStateTruthG (image.toGuestProgram valid) trajectory carrier.timeline (event.facts witness.data).statePull ∧
      ∀ pull ∈ (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).memPulls,
        MemoryMsg.isU64 pull.1 ∧ MemoryMsg.ClkBound pull.1 ∧
          LocalValueAtG trajectory source.sail.realize carrier.timeline (MemoryMsg.locOf pull.1) pull.2 pull.1.value) ∧
      LocalStateTruthG (image.toGuestProgram valid) trajectory carrier.timeline (finalBoundaryStateMessage witness.publicInput) ∧
      (∀ loc message, LocalCore.memoryFinalFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = some message →
        LocalValueAtG trajectory source.sail.realize carrier.timeline loc
          (StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput)) message.value) := by
  have checked := HostLocalCore.localWitness_constraints _
    (HostHintQueueBoundary.projected_constraints witness constraints)
  have ordering := source_ordering witness constraints balanced
  have encoding := LocalCore.source_state_encoding_of_checks _ ordering.sourceChecks
  rw [source_public] at encoding
  have initialState := LocalCore.initialStateTruth_of_checks valid _ ordering.sourceChecks trajectory carrier.timeline initial
    (carrier.timeline_start.trans encoding.1)
  rw [source_public] at initialState
  have genesis := LocalCore.memoryInitialFrontier_liveOK_of_channels _ checked ordering.sourceChecks ordering.byte
    (source_membership_balance witness balanced)
    trajectory carrier.timeline initial
  rw [carrier.timeline_start] at genesis
  have grounded := NativeCore.ExecutionCarrier.ground carrier (image.toGuestProgram valid) trajectory source.sail.realize
    initialState genesis steps
  exact ⟨carrier.originalCurrency grounded.1, grounded.2⟩

end SP1Clean.Soundness.HostHintReadCPU
