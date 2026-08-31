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

/-- The native 25-chip slice contains only ordinary Sail instructions. This predicate is stated on
the proof-free trace so support checks and trace compilation never inspect a validity proof. -/
def EventExecutionTrace.AllOrdinary (execution : EventExecutionTrace) : Prop :=
  ∀ transition ∈ execution.transitions, transition.event = .ordinary

/-- A valid transition list containing only ordinary events is exactly an official-Sail chain.
The syscall handler disappears from the conclusion because no syscall constructor can occur. -/
theorem EventTransitionsValid.sailChain_of_allOrdinary {handler : SyscallHandler}
    {program : GuestProgram} {source : SailState} {transitions : List EventTransition}
    (valid : EventTransitionsValid handler program source transitions)
    (ordinary : ∀ transition ∈ transitions, transition.event = .ordinary) :
    SailChain transitions.length source (stateAfterTransitions source transitions) := by
  induction valid with
  | nil state => exact .refl state
  | @cons source transition rest step tail ih =>
      have headOrdinary : transition.event = .ordinary := ordinary transition (by simp)
      have restOrdinary : ∀ item ∈ rest, item.event = .ordinary :=
        fun item itemMem => ordinary item (by simp [itemMem])
      rcases transition with ⟨event, target⟩
      simp only at headOrdinary
      subst event
      cases step with
      | ordinary _ sailStep =>
          simpa only [List.length_cons, stateAfterTransitions, List.foldl_cons,
            Nat.succ_eq_add_one] using SailChain.step sailStep (ih restOrdinary)

/-- The ordinary fragment of an event trace forgets directly to the canonical Sail-chain
semantics; no parallel execution carrier is needed. -/
theorem EventExecutionTrace.sailChain {handler : SyscallHandler} {program : GuestProgram}
    (execution : EventExecutionTrace) (valid : execution.Valid handler program)
    (ordinary : execution.AllOrdinary) :
    SailChain execution.steps execution.initialState execution.finalState := by
  simpa only [EventExecutionTrace.Valid, EventExecutionTrace.steps,
    EventExecutionTrace.finalState] using valid.sailChain_of_allOrdinary ordinary

/-- One proof-free transition together with the source state at which it occurs. The target remains
the one stored by `EventTransition`; this is a derived chronological view, not a second trace. -/
structure LocatedTransition where
  source : SailState
  transition : EventTransition

/-- Attach each transition to its source state, threading targets in execution order. -/
def locateTransitions : SailState → List EventTransition → List LocatedTransition
  | _, [] => []
  | source, transition :: rest =>
      ⟨source, transition⟩ :: locateTransitions transition.target rest

/-- The chronological transition view consumed by trace compilation. -/
def EventExecutionTrace.locatedTransitions (execution : EventExecutionTrace) :
    List LocatedTransition :=
  locateTransitions execution.initialState execution.transitions

@[simp] theorem locateTransitions_length (source : SailState)
    (transitions : List EventTransition) :
    (locateTransitions source transitions).length = transitions.length := by
  induction transitions generalizing source with
  | nil => rfl
  | cons transition rest ih => simp [locateTransitions, ih]

@[simp] theorem EventExecutionTrace.locatedTransitions_length
    (execution : EventExecutionTrace) :
    execution.locatedTransitions.length = execution.steps := by
  simp [EventExecutionTrace.locatedTransitions, EventExecutionTrace.steps]

@[simp] theorem locateTransitions_map_transition (source : SailState)
    (transitions : List EventTransition) :
    (locateTransitions source transitions).map LocatedTransition.transition = transitions := by
  induction transitions generalizing source with
  | nil => rfl
  | cons transition rest ih => simp [locateTransitions, ih]

@[simp] theorem EventExecutionTrace.locatedTransitions_map_transition
    (execution : EventExecutionTrace) :
    execution.locatedTransitions.map LocatedTransition.transition = execution.transitions := by
  simp [EventExecutionTrace.locatedTransitions]

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

/-- Read proof-free transitions from a PolyFun prefix. -/
def prefixTransitions {handler : SyscallHandler} {program : GuestProgram} :
    {source : SailState} → {steps : ℕ} →
      PFunctor.DynSystem.Prefix (eventSystem handler program) source steps →
        List EventTransition
  | _, _, .nil => []
  | _, _, .step direction tail =>
      ⟨direction.event, direction.target⟩ :: prefixTransitions tail

/-- A checked proof-free transition list has a PolyFun prefix with exactly the same transitions.
This is first proved propositionally because `EventTransitionsValid` lives in `Prop`; the data-level
view below selects the prefix noncomputably without making validity proof data observable. -/
theorem EventTransitionsValid.exists_prefix {handler : SyscallHandler} {program : GuestProgram}
    {source : SailState} {transitions : List EventTransition}
    (valid : EventTransitionsValid handler program source transitions) :
    ∃ path : PFunctor.DynSystem.Prefix (eventSystem handler program) source transitions.length,
      prefixTransitions path = transitions := by
  induction valid with
  | nil => exact ⟨.nil, rfl⟩
  | cons transition step tail ih =>
      rcases transition with ⟨event, target⟩
      obtain ⟨path, pathTransitions⟩ := ih
      refine ⟨.step ⟨event, target, step⟩ path, ?_⟩
      exact congrArg (⟨event, target⟩ :: ·) pathTransitions

/-- Turn checked proof-free transitions directly into PolyFun's finite-orbit carrier. -/
noncomputable def EventTransitionsValid.toPrefix {handler : SyscallHandler}
    {program : GuestProgram} {source : SailState} {transitions : List EventTransition}
    (valid : EventTransitionsValid handler program source transitions) :
    PFunctor.DynSystem.Prefix (eventSystem handler program) source transitions.length :=
  Classical.choose valid.exists_prefix

@[simp] theorem EventTransitionsValid.prefixTransitions_toPrefix
    {handler : SyscallHandler} {program : GuestProgram} {source : SailState}
    {transitions : List EventTransition}
    (valid : EventTransitionsValid handler program source transitions) :
    prefixTransitions valid.toPrefix = transitions :=
  Classical.choose_spec valid.exists_prefix

/-- The PolyFun view of a valid proof-free execution trace. `EventExecutionTrace` remains the one
public execution carrier; `Prefix` is created only when a generic operational theorem needs it. -/
noncomputable def EventExecutionTrace.toPrefix {handler : SyscallHandler}
    {program : GuestProgram} (execution : EventExecutionTrace)
    (valid : execution.Valid handler program) :
    PFunctor.DynSystem.Prefix (eventSystem handler program)
      execution.initialState execution.transitions.length :=
  valid.toPrefix

/-- Forget the proof fields of a PolyFun prefix and recover the canonical proof-free trace. -/
def EventExecutionTrace.ofPrefix {handler : SyscallHandler} {program : GuestProgram}
    {initialState : SailState} {steps : ℕ}
    (path : PFunctor.DynSystem.Prefix (eventSystem handler program) initialState steps) :
    EventExecutionTrace where
  initialState := initialState
  transitions := prefixTransitions path

@[simp] theorem prefixTransitions_length {handler : SyscallHandler} {program : GuestProgram}
    {initialState : SailState} {steps : ℕ}
    (path : PFunctor.DynSystem.Prefix (eventSystem handler program) initialState steps) :
    (prefixTransitions path).length = steps := by
  induction path with
  | nil => rfl
  | step _ _ ih => simp [prefixTransitions, ih]

/-- The transitions read from a PolyFun prefix are valid by construction. -/
theorem prefixTransitions_valid {handler : SyscallHandler} {program : GuestProgram}
    {initialState : SailState} {steps : ℕ}
    (path : PFunctor.DynSystem.Prefix (eventSystem handler program) initialState steps) :
    EventTransitionsValid handler program initialState (prefixTransitions path) := by
  induction path with
  | nil => exact .nil _
  | @step source steps direction tail ih =>
      refine .cons ⟨direction.event, direction.target⟩ direction.valid ?_
      simpa only [eventSystem, PFunctor.DynSystem.update_mk'] using ih

/-- A PolyFun prefix converted to the proof-free carrier remains valid. -/
theorem EventExecutionTrace.ofPrefix_valid {handler : SyscallHandler} {program : GuestProgram}
    {initialState : SailState} {steps : ℕ}
    (path : PFunctor.DynSystem.Prefix (eventSystem handler program) initialState steps) :
    (EventExecutionTrace.ofPrefix path).Valid handler program :=
  prefixTransitions_valid path

/-- Folding the extracted transition targets reaches the PolyFun prefix's endpoint. -/
theorem stateAfterTransitions_prefixTransitions {handler : SyscallHandler}
    {program : GuestProgram} {initialState : SailState} {steps : ℕ}
    (path : PFunctor.DynSystem.Prefix (eventSystem handler program) initialState steps) :
    stateAfterTransitions initialState (prefixTransitions path) = path.last := by
  induction path with
  | nil => rfl
  | @step source steps direction tail ih =>
      change stateAfterTransitions direction.target (prefixTransitions tail) = tail.last
      simpa only [eventSystem, PFunctor.DynSystem.update_mk'] using ih

/-- Forgetting proof fields preserves the event transcript. -/
theorem events_prefixTransitions {handler : SyscallHandler}
    {program : GuestProgram} {initialState : SailState} {steps : ℕ}
    (path : PFunctor.DynSystem.Prefix (eventSystem handler program) initialState steps) :
    (prefixTransitions path).map EventTransition.event =
      path.events (eventMap handler program) := by
  induction path with
  | nil => rfl
  | step direction tail ih =>
      change direction.event :: List.map EventTransition.event (prefixTransitions tail) =
        direction.event :: tail.events (eventMap handler program)
      exact congrArg (direction.event :: ·) ih

theorem EventExecutionTrace.ofPrefix_finalState {handler : SyscallHandler}
    {program : GuestProgram} {initialState : SailState} {steps : ℕ}
    (path : PFunctor.DynSystem.Prefix (eventSystem handler program) initialState steps) :
    (EventExecutionTrace.ofPrefix path).finalState = path.last :=
  stateAfterTransitions_prefixTransitions path

theorem EventExecutionTrace.ofPrefix_events {handler : SyscallHandler}
    {program : GuestProgram} {initialState : SailState} {steps : ℕ}
    (path : PFunctor.DynSystem.Prefix (eventSystem handler program) initialState steps) :
    (EventExecutionTrace.ofPrefix path).events = path.events (eventMap handler program) :=
  events_prefixTransitions path

/-- Passing a valid proof-free trace through its PolyFun view loses only proof fields. -/
@[simp] theorem EventExecutionTrace.ofPrefix_toPrefix {handler : SyscallHandler}
    {program : GuestProgram} (execution : EventExecutionTrace)
    (valid : execution.Valid handler program) :
    EventExecutionTrace.ofPrefix (execution.toPrefix valid) = execution := by
  cases execution
  simp [EventExecutionTrace.ofPrefix, EventExecutionTrace.toPrefix]

/-- Advance an interaction clock through an event transcript. -/
def clockAfterEvents (initialClock : ℕ) (events : List ExecutionEvent) : ℕ :=
  events.foldl (fun clock event => clock + ExecutionEvent.duration event) initialClock

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

theorem EventExecutionTrace.events_length (execution : EventExecutionTrace) :
    execution.events.length = execution.steps := by
  simp [EventExecutionTrace.events, EventExecutionTrace.steps]

/-! ## Append/snoc structure (the halting-shard assembly)

A halting shard's trace is an ordinary instruction prefix with one terminal syscall transition
appended.  These lemmas transport validity, the schedule discipline, the clock accounting, and the
terminal-halt condition across that append. -/

theorem stateAfterTransitions_append (source : SailState) (l₁ l₂ : List EventTransition) :
    stateAfterTransitions source (l₁ ++ l₂) =
      stateAfterTransitions (stateAfterTransitions source l₁) l₂ :=
  List.foldl_append ..

theorem clockAfterEvents_append (clock : ℕ) (e₁ e₂ : List ExecutionEvent) :
    clockAfterEvents clock (e₁ ++ e₂) = clockAfterEvents (clockAfterEvents clock e₁) e₂ :=
  List.foldl_append ..

theorem EventTransitionsValid.append {handler : SyscallHandler} {program : GuestProgram}
    {source : SailState} {l₁ l₂ : List EventTransition}
    (h₁ : EventTransitionsValid handler program source l₁)
    (h₂ : EventTransitionsValid handler program (stateAfterTransitions source l₁) l₂) :
    EventTransitionsValid handler program source (l₁ ++ l₂) := by
  induction l₁ generalizing source with
  | nil =>
      cases h₁
      simpa [stateAfterTransitions] using h₂
  | cons t rest ih =>
      cases h₁ with
      | cons _ step tail =>
          refine .cons t step (ih tail ?_)
          simpa [stateAfterTransitions] using h₂

theorem eventTransitionsClocked_append {clock : ℕ} {l₁ l₂ : List EventTransition}
    (h₁ : EventTransitionsClocked clock l₁)
    (h₂ : EventTransitionsClocked
      (clockAfterEvents clock (l₁.map EventTransition.event)) l₂) :
    EventTransitionsClocked clock (l₁ ++ l₂) := by
  induction l₁ generalizing clock with
  | nil => simpa [clockAfterEvents] using h₂
  | cons t rest ih =>
      obtain ⟨starts, tail⟩ := h₁
      exact ⟨starts, ih tail (by simpa [clockAfterEvents] using h₂)⟩

theorem locateTransitions_append (source : SailState) (l₁ l₂ : List EventTransition) :
    locateTransitions source (l₁ ++ l₂) =
      locateTransitions source l₁ ++
        locateTransitions (stateAfterTransitions source l₁) l₂ := by
  induction l₁ generalizing source with
  | nil => rfl
  | cons transition rest ih =>
      simp only [List.cons_append, locateTransitions, ih, stateAfterTransitions,
        List.foldl_cons]

/-- The snoc trace's terminal condition: appending one canonical-HALT syscall transition to a
trace whose final state is `SP1Halted` halts the whole trace. -/
theorem EventExecutionTrace.haltsWith_snoc (program : GuestProgram) (exitCode : BitVec 64)
    (execution : EventExecutionTrace) (event : CoreSyscallEvent) (target : SailState)
    (canonical : event.IsCanonicalHalt) (arg1 : event.arg1 = exitCode)
    (halted : SP1Halted program exitCode execution.finalState) :
    EventExecutionTrace.HaltsWith program exitCode
      ⟨execution.initialState,
        execution.transitions ++ [⟨.syscall event, target⟩]⟩ := by
  refine ⟨⟨.syscall event, target⟩, event, ?_, rfl, canonical, arg1, ?_⟩
  · exact List.getLast?_concat
  · show SP1Halted program exitCode (stateAfterTransitions execution.initialState
      ((execution.transitions ++
        [(⟨.syscall event, target⟩ : EventTransition)]).dropLast))
    rw [List.dropLast_concat]
    exact halted

end SP1Clean.Machine
