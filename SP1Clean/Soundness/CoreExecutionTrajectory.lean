import SP1Clean.Soundness.CoreRowTransport
import SP1Clean.Soundness.CoreExecutionEvents
import SP1Clean.Model.Core.ExecutionReplay

/-! # Stateful replay shared by complete execution carriers

The physical event inventory determines a single tape. Its replay threads the complete Sail/host
state; alignment and additional host Memory touches leave the tape unchanged. The AIR timeline
agrees with the semantic event timeline, including the administrative extension beyond the tape.
These identities do not assume that replay succeeds.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat Channels Model.Core Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
  {facts : ExecutionRow p → RowFacts p} {inventory : List (ExecutionRow p)}
  {incoming outgoing : StateMsg (ZMod p)}
  {initialFrontier physicalFinal : MemLoc → Option (MemoryMsg (ZMod p))}

/-- The semantic labels of every actual event occurrence in the derived order. -/
noncomputable def ExecutionCarrier.events
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal) :
    List Machine.ExecutionEvent := carrier.ordered.map ExecutionRow.event

theorem ExecutionCarrier.events_length
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal) :
    carrier.events.length = carrier.rows.length := by
  simpa only [events, List.length_map] using carrier.aligned.length_eq.symm

/-- The incoming clock identifies the exact physical occurrence, even when values repeat. -/
theorem ExecutionCarrier.ordered_at
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal)
    {event : ExecutionRow p} (member : event ∈ inventory) {n : ℕ}
    (atIndex : StateMsg.timeNat (facts event).statePull = carrier.timeline.start n) :
    carrier.ordered[n]? = some event :=
  ordered_at_of_alignment facts carrier.aligned carrier.stateWalk
    (fun row member => (carrier.rowOK row member).timeGap) (carrier.exhaustive.mem_iff.mpr member) atIndex

theorem ExecutionCarrier.event_at
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal)
    {event : ExecutionRow p} (member : event ∈ inventory) {n : ℕ}
    (atIndex : StateMsg.timeNat (facts event).statePull = carrier.timeline.start n) :
    carrier.events[n]? = some event.event := by
  simp only [events, List.getElem?_map, carrier.ordered_at member atIndex, Option.map_some]

/-- An actual ordered occurrence has the incoming clock of that same trajectory position. -/
theorem ExecutionCarrier.time_of_ordered_at
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal)
    {event : ExecutionRow p} {n : ℕ} (present : carrier.ordered[n]? = some event) :
    StateMsg.timeNat (facts event).statePull = carrier.timeline.start n := by
  obtain ⟨bound, atEvent⟩ := List.getElem?_eq_some_iff.mp present
  have leftBound : n < carrier.rows.length := by
    have lengths := carrier.aligned.length_eq
    simp only [List.length_map] at lengths
    omega
  have related := carrier.aligned.get leftBound (by simpa only [List.length_map] using bound)
  simp only [List.get_eq_getElem, List.getElem_map, atEvent] at related
  exact related.pullTime.symm.trans (rowTimeline_pullTime_of_getElem? carrier.stateWalk
    (fun row member => (carrier.rowOK row member).timeGap) (List.getElem?_eq_getElem leftBound))

/-- The actual full source initializes replay; no intermediate host state is chosen by a row. -/
noncomputable def ExecutionCarrier.pairedTrajectory
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal)
    (policy : HostPolicy) (program : Target.GuestProgram) (source : ExecutionState) : ℕ → Option ExecutionState :=
  executionTrajectory policy program source carrier.events

noncomputable def ExecutionCarrier.trajectory
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal)
    (policy : HostPolicy) (program : Target.GuestProgram) (source : ExecutionState) : Trajectory :=
  fun n => (carrier.pairedTrajectory policy program source n).map ExecutionState.sail

theorem ExecutionCarrier.trajectory_zero
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal)
    (policy : HostPolicy) (program : Target.GuestProgram) (source : ExecutionState) :
    carrier.trajectory policy program source 0 = some source.sail := rfl

/-- At an authenticated event position, replay uses that event's complete claimed result. -/
theorem ExecutionCarrier.pairedTrajectory_succ
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal)
    (policy : HostPolicy) (program : Target.GuestProgram) (source : ExecutionState)
    {event : ExecutionRow p} (member : event ∈ inventory) {n : ℕ}
    (atIndex : StateMsg.timeNat (facts event).statePull = carrier.timeline.start n) :
    carrier.pairedTrajectory policy program source (n + 1) =
      (carrier.pairedTrajectory policy program source n).bind (fun state => replayStep? policy program state event.event) :=
  executionTrajectory_succ _ _ _ _ (carrier.event_at member atIndex)

theorem ExecutionCarrier.originalTimeStep
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal)
    {event : ExecutionRow p} (member : event ∈ inventory) :
    ∀ n, StateMsg.timeNat (facts event).statePull = carrier.timeline.start n →
      StateMsg.timeNat (facts event).statePush = carrier.timeline.start (n + 1) := by
  have originalMem := List.mem_map_of_mem (f := facts) (carrier.exhaustive.mem_iff.mpr member)
  obtain ⟨row, rowMem, aligned⟩ := forall₂_exists_right carrier.aligned.flip _ originalMem
  intro n time
  rw [← aligned.pushTime]
  exact carrier.timeStep row rowMem n (aligned.pullTime.trans time)

private theorem event_durations
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal)
    (duration : ∀ event ∈ inventory, StateMsg.timeNat (facts event).statePush =
      StateMsg.timeNat (facts event).statePull + event.duration) :
    carrier.rows.map rowDuration = carrier.events.map Machine.ExecutionEvent.duration := by
  rw [ExecutionCarrier.events, List.map_map]
  apply List.ext_getElem
  · simpa only [List.length_map] using carrier.aligned.length_eq
  · intro n left right
    have leftBound : n < carrier.rows.length := by simpa only [List.length_map] using left
    have rightBound : n < carrier.ordered.length := by simpa only [List.length_map] using right
    have aligned := carrier.aligned.get leftBound (by simpa only [List.length_map] using rightBound)
    simp only [List.get_eq_getElem, List.getElem_map, Function.comp_apply] at aligned ⊢
    rw [rowDuration, aligned.pushTime, aligned.pullTime,
      duration _ (carrier.exhaustive.mem_iff.mp (List.getElem_mem rightBound)),
      Nat.add_sub_cancel_left, ExecutionRow.event_duration]

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem duration_sum (events : List Machine.ExecutionEvent) (n : ℕ) :
    ((List.range n).map (durationAt events)).sum =
      ((events.map Machine.ExecutionEvent.duration).take n).sum + 8 * (n - events.length) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases inside : n < events.length
    · simp only [durationAt, List.getElem?_eq_getElem inside]
      rw [List.sum_take_succ _ _ (by simpa only [List.length_map] using inside), List.getElem_map]
      have prior : n - events.length = 0 := by omega
      have next : n + 1 - events.length = 0 := by omega
      rw [prior] at ih
      rw [next]
      omega
    · have bound : events.length ≤ n := by omega
      simp only [durationAt, List.getElem?_eq_none (by omega : events.length ≤ n)]
      rw [List.take_of_length_le (by simpa only [List.length_map] using bound)] at ih
      rw [List.take_of_length_le (by simp only [List.length_map]; omega)]
      omega

/-- Row and semantic timelines are identical, including their non-executing tails. -/
theorem ExecutionCarrier.timeline_eq_events
    (carrier : ExecutionCarrier facts inventory incoming outgoing initialFrontier physicalFinal)
    (initialClock : ℕ) (start : StateMsg.timeNat incoming = initialClock)
    (duration : ∀ event ∈ inventory, StateMsg.timeNat (facts event).statePush =
      StateMsg.timeNat (facts event).statePull + event.duration) :
    carrier.timeline = eventTimeline carrier.events initialClock := by
  have same : carrier.timeline.start = (eventTimeline carrier.events initialClock).start := by
    funext n
    simp only [timeline, rowTimeline, Timeline.ofDurations, eventTimeline, start,
      event_durations carrier duration, List.length_map, duration_sum, Nat.add_assoc]
  cases hleft : carrier.timeline
  cases hright : eventTimeline carrier.events initialClock
  simp only [Timeline.mk.injEq]
  simpa only [hleft, hright] using same

end SP1Clean.Soundness.NativeCore
