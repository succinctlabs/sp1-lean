import SP1Clean.Soundness.LocalCoreGrounding
import SP1Clean.Soundness.CoreExecutionTrajectory

/-! # Stateful replay of the local AIR's ordered events

The carrier determines one event tape. Replay starts at the full checked source and threads the
actual host state, validating every claimed syscall against concrete host execution. Its Sail
projection is the trajectory used by grounding. Success is not assumed here: a forged host result
may make replay fail even when the current AIR accepts it. Successful replay has the exact derived
clock at every covered position; the extension past the tape contributes no semantic steps.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow ordered_at_of_alignment)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Every active occurrence is retained in the balance-derived order. -/
noncomputable def GroundingCarrier.events {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness) :
    List Machine.ExecutionEvent := carrier.ordered.map ExecutionRow.event

theorem GroundingCarrier.events_length {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness) :
    carrier.events.length = carrier.rows.length := NativeCore.ExecutionCarrier.events_length carrier

/-- The actual event occurrence is identified by its natural State clock. -/
theorem GroundingCarrier.ordered_at {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n) :
    carrier.ordered[n]? = some event := NativeCore.ExecutionCarrier.ordered_at carrier member atIndex

theorem GroundingCarrier.event_at {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n) :
    carrier.events[n]? = some event.event := NativeCore.ExecutionCarrier.event_at carrier member atIndex

/-- The full source, including its actual host queues and exit status, initializes replay. -/
noncomputable def GroundingCarrier.pairedTrajectory {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) : ℕ → Option ExecutionState :=
  executionTrajectory policy (image.toGuestProgram valid) source.realize carrier.events

/-- Grounding observes the Sail projection of that same evolving whole state. -/
noncomputable def GroundingCarrier.trajectory {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) : Trajectory :=
  fun n => (carrier.pairedTrajectory valid policy n).map ExecutionState.sail

theorem GroundingCarrier.pairedTrajectory_zero {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) :
    carrier.pairedTrajectory valid policy 0 = some source.realize := rfl

theorem GroundingCarrier.trajectory_zero {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) :
    carrier.trajectory valid policy 0 = some source.sail.realize := rfl

/-- No handler reset or row-chosen result occurs between events. -/
theorem GroundingCarrier.pairedTrajectory_succ {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n) :
    carrier.pairedTrajectory valid policy (n + 1) =
      (carrier.pairedTrajectory valid policy n).bind
        (fun state => replayStep? policy (image.toGuestProgram valid) state event.event) :=
  NativeCore.ExecutionCarrier.pairedTrajectory_succ carrier policy (image.toGuestProgram valid) source.realize member atIndex

/-- Original physical State successors occur at the next timeline position. -/
theorem GroundingCarrier.originalTimeStep {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) :
    ∀ n, StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n →
      StateMsg.timeNat (event.facts witness.data).statePush = carrier.timeline.start (n + 1) :=
  NativeCore.ExecutionCarrier.originalTimeStep carrier member

/-- The AIR timeline counts semantic event widths, without counting providers or inactive rows. -/
theorem GroundingCarrier.timeline_events {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (n : ℕ) (covered : n ≤ carrier.events.length) :
    carrier.timeline.start n = source.clock + ((carrier.events.take n).map Machine.ExecutionEvent.duration).sum := by
  have same := NativeCore.ExecutionCarrier.timeline_eq_events carrier source.clock
    (source_state_encoding witness balanced).1 (by
      intro event member
      have duration := (executionRows_advancing witness constraints balanced member).2
      rwa [ExecutionRow.edge_eq_facts] at duration)
  change (NativeCore.ExecutionCarrier.timeline carrier).start n = _
  rw [same]
  exact eventTimeline_start_le carrier.events source.clock n covered

/-- A successful paired prefix carries exactly the clock selected by the AIR walk. -/
theorem GroundingCarrier.pairedTrajectory_clock {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {n : ℕ} (covered : n ≤ carrier.events.length) {state : ExecutionState}
    (present : carrier.pairedTrajectory valid policy n = some state) :
    state.clock = carrier.timeline.start n := by
  rw [carrier.timeline_events constraints balanced n covered]
  exact replayEvents?_clock present

/-- A nonempty local AIR segment must start at a running host. -/
theorem source_running_of_event {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) : source.host.exitCode = none := by
  by_contra stopped
  rw [executionRows_nil_of_stopped witness constraints balanced stopped] at member
  exact List.not_mem_nil member

/-- At a replayed prefix with an authenticated code fetch, terminal status is impossible.
The claim uses the actual evolving host, not an assumed host-invariance property. -/
theorem GroundingCarrier.pairedTrajectory_running_of_fetch {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {event : ExecutionRow p} (member : event ∈ executionRows witness)
    {n : ℕ} {state : ExecutionState} (present : carrier.pairedTrajectory valid policy n = some state)
    {pc : BitVec 64} {word : BitVec 32}
    (atPc : state.sail.regs.get? LeanRV64D.Defs.Register.PC = some pc)
    (fetched : (image.toGuestProgram valid).fetchWord pc = some word) : state.host.exitCode = none := by
  exact replayEvents?_running_of_fetch (source_running_of_event witness constraints balanced member) present atPc fetched

/-- Final State truth recovers successful replay of the entire tape and its complete returned
state. Only PC/clock are bound to public fields here; full outgoing snapshot agreement is separate. -/
theorem GroundingCarrier.replay_of_finalTruth {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (final : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid policy) carrier.timeline
      (finalBoundaryStateMessage witness.publicInput)) :
    ∃ target, replayEvents? policy (image.toGuestProgram valid) source.realize carrier.events = some target ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) := by
  obtain ⟨n, state, present, time, pc, _, _⟩ := final
  have atEnd : n = carrier.rows.length := start_injective carrier.timeline (time.symm.trans carrier.finalClock.symm)
  change (carrier.pairedTrajectory valid policy n).map ExecutionState.sail = some state at present
  rw [atEnd, ← carrier.events_length] at present
  obtain ⟨target, paired, sail⟩ := Option.map_eq_some_iff.mp present
  refine ⟨target, ?_, ?_, ?_⟩
  · simpa only [pairedTrajectory, executionTrajectory, List.take_length] using paired
  · have clock := carrier.pairedTrajectory_clock valid policy constraints balanced le_rfl paired
    rwa [carrier.events_length, carrier.finalClock] at clock
  · rwa [sail]

end SP1Clean.Soundness.LocalCore
