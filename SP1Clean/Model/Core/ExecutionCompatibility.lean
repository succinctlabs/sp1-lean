import SP1Clean.Model.Core.HostHalt
import SP1Clean.Model.Machine.Shard
import SP1Clean.Model.Semantics.EventTime

/-! # Whole-path compatibility for the ordinary/HALT fragment

The old event trace supplies one fixed executable host. The full native path instead threads the
complete host and clock. On the ordinary/HALT fragment their Sail projections agree, including
HALT's literal register-map effect. No equivalence with an arbitrary fixed host is claimed for
mixed calls. Normal retirement and the complete host endpoint remain properties of `ExecutionPath`.
-/

namespace SP1Clean.Model.Core
open SP1Clean.Machine SP1Clean.Soundness.Target LeanRV64D LeanRV64D.Defs
open SP1Clean.Semantics

/-- A real canonical HALT changes Sail only by parking PC; x5 was already zero. -/
theorem ExecutionStep.halt_effect {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : CoreSyscallEvent}
    (step : ExecutionStep policy program source (.syscall event) target)
    (halt : event.rawCode = 0) :
    target.sail = { source.sail with regs := source.sail.regs.insert Register.PC haltPc } := by
  cases step with
  | syscall success =>
    obtain ⟨pc, execution, _, _, ran, _, rfl, rfl⟩ := HostState.step_observations success
    have observed := (source.host.run_eq_some_iff policy (.ofSail source.sail) execution).mp ran
    have kind : execution.kind = .halt := by
      change execution.kind.code = 0 at halt
      cases h : execution.kind <;> simp_all [SyscallKind.code]
    have executed := observed.2.2.2.2.2
    rw [kind] at executed
    simp only [HostState.executeKind] at executed
    split_ifs at executed
    have effect := Option.some.inj executed
    have same : execution = source.host.haltExecution execution.arg1 execution.arg2 := by
      cases execution
      simp_all [HostState.haltExecution, HostState.result, SyscallKind.code]
    rw [same]
    exact source.host.haltExecution_apply source.sail pc _ _ (by simpa [kind, HostReadContext.ofSail, SyscallKind.code] using observed.2.1)

/-- The fragment on which a fixed legacy HALT handler agrees with stateful host execution. -/
def OrdinaryOrHalt : ExecutionEvent → Prop
  | .ordinary => True
  | .syscall event => event.rawCode = 0

/-- A fixed handler with canonical HALT recovers each projected step in this fragment. -/
theorem ExecutionStep.ordinaryHalt_event {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep policy program source event target) (fragment : OrdinaryOrHalt event)
    (handler : ExecutableSyscallHandler) :
    EventStep handler.withHalt.relation program source.sail event target.sail := by
  cases event with
  | ordinary =>
    cases step with
    | ordinary _ notEcall normal => exact .ordinary notEcall normal.sailStep
  | syscall call =>
    have effect := step.halt_effect fragment
    have projected := step.sailEvent
    cases projected with
    | syscall about transition =>
      refine .syscall about ⟨transition.1, transition.2.1, ?_⟩
      change handler.withHalt.run program call source.sail = some target.sail
      rw [ExecutableSyscallHandler.withHalt_run_zero _ _ _ _ fragment, effect]

/-- The legacy trace is reconstructed from the same tape, with its exact endpoint and clock.
The complete stateful path remains available; this projection does not forget its assumptions. -/
theorem ExecutionPath.ordinaryHalt_trace {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target)
    (fragment : ∀ event ∈ events, OrdinaryOrHalt event) (handler : ExecutableSyscallHandler) :
    ∃ trace : EventExecutionTrace,
      traceOfEvents? handler.withHalt program source.sail events = some trace ∧
      trace.Valid handler.withHalt.relation program ∧ trace.Clocked source.clock ∧
      trace.initialState = source.sail ∧ trace.events = events ∧ trace.finalState = target.sail ∧
      target.clock = source.clock + (trace.events.map ExecutionEvent.duration).sum := by
  suffices ∃ transitions, EventTransitionsValid handler.withHalt.relation program source.sail transitions ∧
      EventTransitionsClocked source.clock transitions ∧ transitions.map EventTransition.event = events ∧
      stateAfterTransitions source.sail transitions = target.sail by
    obtain ⟨transitions, valid, clocked, same, endpoint⟩ := this
    refine ⟨⟨source.sail, transitions⟩, ?_, valid, clocked, rfl, same, endpoint, ?_⟩
    · rw [← same]
      exact traceOfEvents?_of_valid handler.withHalt program ⟨source.sail, transitions⟩ valid
    · simpa only [EventExecutionTrace.events, same] using path.clock
  induction path with
  | nil source => exact ⟨[], .nil _, trivial, rfl, rfl⟩
  | @cons source middle target event events step tail ih =>
    obtain ⟨transitions, valid, clocked, same, endpoint⟩ :=
      ih (fun event member => fragment event (List.mem_cons_of_mem _ member))
    refine ⟨⟨event, middle.sail⟩ :: transitions,
      .cons _ (step.ordinaryHalt_event (fragment event (List.mem_cons_self)) handler) valid,
      ⟨step.startsAt, ?_⟩, ?_, endpoint⟩
    · rwa [← step.clock]
    · simp only [List.map_cons, same]

private theorem eventTrajectory_cons (handler : ExecutableSyscallHandler) (program : GuestProgram)
    (event : ExecutionEvent) (events : List ExecutionEvent) (source : SailState) (position : ℕ) :
    eventTrajectory handler program (event :: events) source (position + 1) =
      (executeEvent? handler program source event).bind fun next =>
        eventTrajectory handler program events next position := by
  induction position with
  | zero => simp [eventTrajectory]
  | succ position ih =>
    rw [eventTrajectory_succ, List.getElem?_cons_succ, ih]
    cases present : events[position]? <;>
      cases executeEvent? handler program source event <;>
      simp [eventTrajectory_succ, present]

/-- The same whole path supplies every covered legacy trajectory state. The bound matters:
legacy trajectories are undefined after the tape, whereas complete replay holds its endpoint. -/
theorem ExecutionPath.ordinaryHalt_trajectory {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target)
    (fragment : ∀ event ∈ events, OrdinaryOrHalt event) (handler : ExecutableSyscallHandler)
    (position : ℕ) (covered : position ≤ events.length) :
    eventTrajectory handler.withHalt program events source.sail position =
      (executionTrajectory policy program source events position).map ExecutionState.sail := by
  induction path generalizing position with
  | nil source =>
    have : position = 0 := by simpa using covered
    subst position
    rfl
  | @cons source middle target event events step tail ih =>
    cases position with
    | zero => rfl
    | succ position =>
      have executed : executeEvent? handler.withHalt program source.sail event = some middle.sail := by
        have projected := step.ordinaryHalt_event (fragment event List.mem_cons_self) handler
        cases projected with
        | ordinary _ sail =>
          obtain ⟨result, ran⟩ := sail
          simp only [executeEvent?, ran]
        | syscall _ transition => exact transition.2.2
      rw [eventTrajectory_cons, executed]
      simp only [Option.bind_some, executionTrajectory, List.take_succ_cons, replayEvents?,
        step.replay]
      exact ih (fun event member => fragment event (List.mem_cons_of_mem _ member))
        position (by simpa using covered)

end SP1Clean.Model.Core
