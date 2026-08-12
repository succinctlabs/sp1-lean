import PolyFun.PFunctor.Dynamical.Run
import SP1Clean.Model.Machine.Syscall

/-! # Eventful SP1 execution

Official Sail supplies ordinary instruction semantics, but it does not implement SP1's host ECALL
handler.  The full semantic machine must therefore walk between two explicit kinds of step:

* an ordinary successful Sail `try_step`, excluding an `ECALL` at the committed pc; or
* a raw syscall event satisfying the instruction-row laws and a named handler relation.

Directions of the dependent PolyFun interface are exactly proved next steps.  For extraction, the
public witness type is instead the proof-free `EventExecutionTrace`; its validity predicate checks
the same steps.  This separation lets an AIR postprocessor decode trace data without inspecting a
proof of AIR validity.  A certified PolyFun `Prefix` remains the convenient internal theorem view. -/

open LeanRV64D.Defs

namespace SP1Clean.Machine

open PFunctor
open SP1Clean.Soundness.Target

/-- Stable label of one semantic step. -/
inductive ExecutionEvent
  | ordinary
  | syscall (event : CoreSyscallEvent)
deriving DecidableEq, Repr

/-- The upstream clock window selected by an event. -/
def ExecutionEvent.schedule : ExecutionEvent → StepSchedule
  | .ordinary => ordinarySchedule
  | .syscall _ => syscallSchedule

/-- Width of an event's interaction-clock window. -/
def ExecutionEvent.duration (event : ExecutionEvent) : ℕ :=
  event.schedule.duration

/-- The event's own timestamp, when it carries one, agrees with the beginning of its schedule
window.  Ordinary events obtain their clock from ordered State rows and therefore carry no duplicate
field here. -/
def ExecutionEvent.StartsAt (clock : ℕ) : ExecutionEvent → Prop
  | .ordinary => True
  | .syscall event => event.clock = clock

@[simp] theorem ExecutionEvent.duration_ordinary : ExecutionEvent.ordinary.duration = 8 := rfl

@[simp] theorem ExecutionEvent.duration_syscall (event : CoreSyscallEvent) :
    (ExecutionEvent.syscall event).duration = 264 := rfl

/-- One honest SP1 semantic step.  The syscall case does not claim to be a Sail step: SP1 replaces
the architectural ECALL trap with its own handler protocol. -/
inductive EventStep (handler : SyscallHandler) (program : GuestProgram) :
    SailState → ExecutionEvent → SailState → Prop
  | ordinary {source target : SailState} :
      ¬ AboutToExecuteEcall program source →
      SailStep source target →
      EventStep handler program source .ordinary target
  | syscall {source target : SailState} {event : CoreSyscallEvent} :
      AboutToExecuteEcall program source →
      SyscallTransition handler program event source target →
      EventStep handler program source (.syscall event) target

/-- Proof-free data for one transition in an extracted semantic trace. -/
structure EventTransition where
  event : ExecutionEvent
  target : SailState

/-- Proof-free execution witness.  Its statement supplies the program and syscall handler; validity
below authenticates every transition. -/
structure EventExecutionTrace where
  initialState : SailState
  transitions : List EventTransition

/-- Apply a proof-free transition list to a source state.  Each item stores its target, so this
operation is executable and independent of validity evidence. -/
def stateAfterTransitions (initialState : SailState)
    (transitions : List EventTransition) : SailState :=
  transitions.foldl (fun _ transition => transition.target) initialState

/-- Step-by-step validity of a raw transition list from a given source state. -/
inductive EventTransitionsValid (handler : SyscallHandler) (program : GuestProgram) :
    SailState → List EventTransition → Prop
  | nil (state : SailState) : EventTransitionsValid handler program state []
  | cons {source : SailState} (transition : EventTransition)
      {rest : List EventTransition} :
      EventStep handler program source transition.event transition.target →
      EventTransitionsValid handler program transition.target rest →
      EventTransitionsValid handler program source (transition :: rest)

/-- A raw trace represents an honest eventful execution. -/
def EventExecutionTrace.Valid (handler : SyscallHandler) (program : GuestProgram)
    (execution : EventExecutionTrace) : Prop :=
  EventTransitionsValid handler program execution.initialState execution.transitions

/-- Endpoint of a raw trace. -/
def EventExecutionTrace.finalState (execution : EventExecutionTrace) : SailState :=
  stateAfterTransitions execution.initialState execution.transitions

/-- Source state of the final transition (or the initial state for an empty trace). -/
def EventExecutionTrace.stateBeforeFinal (execution : EventExecutionTrace) : SailState :=
  stateAfterTransitions execution.initialState execution.transitions.dropLast

/-- Stable event transcript of a raw execution. -/
def EventExecutionTrace.events (execution : EventExecutionTrace) : List ExecutionEvent :=
  execution.transitions.map EventTransition.event

/-- Raw syscall rows in execution order. -/
def EventExecutionTrace.syscallEvents (execution : EventExecutionTrace) : List CoreSyscallEvent :=
  execution.events.filterMap fun
    | .ordinary => none
    | .syscall event => some event

/-- The timestamp carried by every raw event agrees with its prefix-sum schedule position. -/
def EventTransitionsClocked : ℕ → List EventTransition → Prop
  | _, [] => True
  | clock, transition :: rest =>
      transition.event.StartsAt clock ∧
        EventTransitionsClocked (clock + transition.event.duration) rest

/-- Schedule consistency of a proof-free trace beginning at `initialClock`. -/
def EventExecutionTrace.Clocked (initialClock : ℕ) (execution : EventExecutionTrace) : Prop :=
  EventTransitionsClocked initialClock execution.transitions

/-- Number of semantic steps in a raw execution. -/
def EventExecutionTrace.steps (execution : EventExecutionTrace) : ℕ :=
  execution.transitions.length

/-- A direction offered at `source`: its observable event, target state, and proof that taking it is
a valid step.  This makes invalid transitions unrepresentable in a PolyFun execution prefix. -/
structure EventDirection (handler : SyscallHandler) (program : GuestProgram)
    (source : SailState) where
  event : ExecutionEvent
  target : SailState
  valid : EventStep handler program source event target

/-- Dependent interface whose directions at a state are exactly valid next steps from that state. -/
-- PolyFun dropped `PFunctor.ofFn` (it was just the two-field constructor with `A` implicit);
-- spell the positions/directions out directly.
def eventInterface (handler : SyscallHandler) (program : GuestProgram) : PFunctor where
  A := SailState
  B := fun source => EventDirection handler program source

/-- Nondeterministic eventful SP1 machine.  Nondeterminism is confined to the explicit syscall
handler relation; ordinary Sail execution remains deterministic. -/
def eventSystem (handler : SyscallHandler) (program : GuestProgram) :
    PFunctor.DynSystem SailState (eventInterface handler program) :=
  PFunctor.DynSystem.mk' id fun _ direction => direction.target

/-- Read the stable event label from a proved transition direction. -/
def eventMap (handler : SyscallHandler) (program : GuestProgram) :
    (eventSystem handler program).EventMap ExecutionEvent :=
  fun _ direction => direction.event

/-- A finite eventful execution beginning at an explicit state. -/
structure EventExecutionPrefix (handler : SyscallHandler) (program : GuestProgram)
    (initialState : SailState) where
  steps : ℕ
  path : PFunctor.DynSystem.Prefix (eventSystem handler program) initialState steps

/-- The endpoint reached by an eventful execution prefix. -/
def EventExecutionPrefix.finalState {handler : SyscallHandler} {program : GuestProgram}
    {initialState : SailState} (execution : EventExecutionPrefix handler program initialState) :
    SailState :=
  execution.path.last

/-- The event transcript of a finite execution prefix. -/
def EventExecutionPrefix.events {handler : SyscallHandler} {program : GuestProgram}
    {initialState : SailState} (execution : EventExecutionPrefix handler program initialState) :
    List ExecutionEvent :=
  execution.path.events (eventMap handler program)

/-- Advance an interaction clock through an event transcript. -/
def clockAfterEvents (initialClock : ℕ) (events : List ExecutionEvent) : ℕ :=
  events.foldl (fun clock event => clock + ExecutionEvent.duration event) initialClock

/-- Final interaction clock of an eventful execution. -/
def EventExecutionPrefix.finalClock {handler : SyscallHandler} {program : GuestProgram}
    {initialState : SailState} (execution : EventExecutionPrefix handler program initialState)
    (initialClock : ℕ) : ℕ :=
  clockAfterEvents initialClock execution.events

/-- Final interaction clock of a proof-free execution witness. -/
def EventExecutionTrace.finalClock (execution : EventExecutionTrace)
    (initialClock : ℕ) : ℕ :=
  clockAfterEvents initialClock execution.events

/-- Executor-faithful terminal condition for an eventful trace.  The last row must carry the exact
canonical HALT code, not only the low-byte AIR classification, and its source is the traditional
`SP1Halted` state exposed to users of the zkVM theorem. -/
def EventExecutionTrace.HaltsWith (program : GuestProgram) (exitCode : BitVec 64)
    (execution : EventExecutionTrace) : Prop :=
  ∃ transition event,
    execution.transitions.getLast? = some transition ∧
      transition.event = .syscall event ∧
      event.IsCanonicalHalt ∧
      event.arg1 = exitCode ∧
      SP1Halted program exitCode execution.stateBeforeFinal

theorem EventExecutionPrefix.events_length {handler : SyscallHandler}
    {program : GuestProgram} {initialState : SailState}
    (execution : EventExecutionPrefix handler program initialState) :
    execution.events.length = execution.steps := by
  obtain ⟨steps, path⟩ := execution
  unfold EventExecutionPrefix.events
  induction path with
  | nil => rfl
  | step _ tail ih => simp [ih]

end SP1Clean.Machine
