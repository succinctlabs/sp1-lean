import SP1Clean.Model.Core.ExecutionPath
import SP1Clean.Model.Machine.Execution

/-! # Replaying mixed event tapes with evolving host state

Replay consumes only the source state and event data. A host event is checked against the call
computed from the actual registers, memory, host queue, and clock; its claimed result is not used
as an oracle. The returned host state feeds the next step. Ordinary replay uses official Sail.

`ExecutionStep.replay` and `ExecutionPath.replay` establish agreement with the semantic relation.
The converse still requires normal-retirement evidence for ordinary instructions: successful
`try_step` evaluation alone also includes interpreter paths other than instruction retirement.
This semantic Sail replay is noncomputable, like the existing machine replay; it is not the
exportable row compiler. Its prefix trajectory supplies the paired state for mixed grounding.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Machine SP1Clean.Soundness.Target LeanRV64D

/-- Computable host replay checks the whole event against the concrete interpreter result. -/
def replayHost? (policy : HostPolicy) (program : GuestProgram) (source : ExecutionState)
    (event : CoreSyscallEvent) : Option ExecutionState := do
  let (host, sail, actual) ← source.host.step policy program source.clock source.sail
  if actual = event then some ⟨sail, host, source.clock + syscallSchedule.duration⟩ else none

theorem replayHost?_eq_some_iff (policy : HostPolicy) (program : GuestProgram)
    (source target : ExecutionState) (event : CoreSyscallEvent) :
    replayHost? policy program source event = some target ↔
      ExecutionStep policy program source (.syscall event) target := by
  constructor
  · intro success
    simp only [replayHost?, bind, Option.bind_eq_some_iff] at success
    obtain ⟨⟨host, sail, actual⟩, ran, success⟩ := success
    dsimp only at success
    split_ifs at success with same
    · subst actual
      cases success
      exact .syscall ran
  · intro step
    cases step with
    | syscall ran => simp [replayHost?, ran]

/-- The Boolean ECALL test observes the actual PC in the committed program. -/
def ExecutionState.atEcall (program : GuestProgram) (source : ExecutionState) : Bool :=
  ((source.sail.regs.get? LeanRV64D.Defs.Register.PC).bind program.fetchWord) == some ECALL_ENC

theorem ExecutionState.atEcall_iff (program : GuestProgram) (source : ExecutionState) :
    source.atEcall program = true ↔ AboutToExecuteEcall program source.sail := by
  simp [ExecutionState.atEcall, AboutToExecuteEcall, Option.bind_eq_some_iff]

/-- Replay one label, guarding both arms against resumption after HALT. -/
noncomputable def replayStep? (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) : ExecutionEvent → Option ExecutionState
  | .ordinary =>
      if source.host.exitCode.isSome || source.atEcall program then none
      else (stepOnce source.sail).map fun sail =>
        ⟨sail, source.host, source.clock + ordinarySchedule.duration⟩
  | .syscall event => replayHost? policy program source event

/-- On a running non-ECALL source, replay preserves the host and executes official Sail. -/
theorem replayStep?_ordinary (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (running : source.host.exitCode = none)
    (notEcall : ¬ AboutToExecuteEcall program source.sail) :
    replayStep? policy program source .ordinary =
      (stepOnce source.sail).map (fun sail =>
        ⟨sail, source.host, source.clock + ordinarySchedule.duration⟩) := by
  have atEcall : source.atEcall program = false :=
    Bool.eq_false_iff.mpr (fun atEcall => notEcall ((source.atEcall_iff program).mp atEcall))
  simp only [replayStep?, running, Option.isSome_none, atEcall, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

/-- The guarded ordinary replay projects to exactly the same Sail step. -/
theorem replayStep?_ordinary_sail (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (running : source.host.exitCode = none)
    (notEcall : ¬ AboutToExecuteEcall program source.sail) :
    (replayStep? policy program source .ordinary).map ExecutionState.sail = stepOnce source.sail := by
  rw [replayStep?_ordinary policy program source running notEcall]
  simp only [Option.map_map, Function.comp_def, Option.map_id']

/-- Successful replay authenticates the event's clock cost even before normal retirement is proved. -/
theorem replayStep?_clock {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (success : replayStep? policy program source event = some target) :
    target.clock = source.clock + event.duration := by
  cases event with
  | ordinary =>
    simp only [replayStep?] at success
    split_ifs at success
    obtain ⟨next, _, rfl⟩ := Option.map_eq_some_iff.mp success
    rfl
  | syscall event => exact ((replayHost?_eq_some_iff _ _ _ _ _).mp success).clock

/-- Replay can create terminal status only together with the reserved HALT PC. -/
theorem replayStep?_terminal_pc {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (success : replayStep? policy program source event = some target)
    (stopped : target.host.exitCode ≠ none) :
    target.sail.regs.get? LeanRV64D.Defs.Register.PC = some haltPc := by
  cases event with
  | ordinary =>
    simp only [replayStep?] at success
    split_ifs at success with blocked
    obtain ⟨next, _, rfl⟩ := Option.map_eq_some_iff.mp success
    have running : source.host.exitCode = none := by
      cases status : source.host.exitCode with
      | none => rfl
      | some code => simp only [status, Option.isSome_some, Bool.true_or, not_true_eq_false] at blocked
    exact (stopped running).elim
  | syscall event =>
    have step := (replayHost?_eq_some_iff _ _ _ _ _).mp success
    cases step with
    | syscall ran =>
      obtain ⟨pc, execution, _, _, run, rfl, rfl, _⟩ := HostState.step_observations ran
      have exit := HostState.run_exit run
      have halt : execution.kind = .halt := by
        by_contra other
        exact stopped (by simpa only [other, ↓reduceIte] using exit)
      simp only [HostExecution.apply, Std.ExtDHashMap.get?_insert_self, HostExecution.nextPc, halt, ↓reduceIte]

/-- Every semantic transition is reconstructed from its event label and incoming whole state. -/
theorem ExecutionStep.replay {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep policy program source event target) :
    replayStep? policy program source event = some target := by
  cases step with
  | ordinary running notEcall normal =>
      have notAtEcall : source.atEcall program = false :=
        Bool.eq_false_iff.mpr (fun atEcall => notEcall ((source.atEcall_iff program).mp atEcall))
      obtain ⟨_, stepped⟩ := normal.sailStep
      simp [replayStep?, running, notAtEcall, stepOnce, stepped]
  | syscall ran => exact (replayHost?_eq_some_iff _ _ _ _ _).mpr (.syscall ran)

/-- A source plus an event tape determines every intermediate host and Sail state. -/
noncomputable def replayEvents? (policy : HostPolicy) (program : GuestProgram) :
    ExecutionState → List ExecutionEvent → Option ExecutionState
  | source, [] => some source
  | source, event :: rest =>
      (replayStep? policy program source event).bind fun next => replayEvents? policy program next rest

/-- Replay itself composes at a semantic cut; no proof term or initial-state reset is involved. -/
theorem replayEvents?_append (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (first second : List ExecutionEvent) :
    replayEvents? policy program source (first ++ second) =
      (replayEvents? policy program source first).bind fun middle =>
        replayEvents? policy program middle second := by
  induction first generalizing source with
  | nil => rfl
  | cons event rest ih => simp only [List.cons_append, replayEvents?, ih, Option.bind_assoc]

/-- Replay counts actual event widths, independently of table height or padding. -/
theorem replayEvents?_clock {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (success : replayEvents? policy program source events = some target) :
    target.clock = source.clock + (events.map ExecutionEvent.duration).sum := by
  induction events generalizing source with
  | nil => cases success; simp
  | cons event rest ih =>
    obtain ⟨middle, step, suffix⟩ := Option.bind_eq_some_iff.mp success
    rw [ih suffix, replayStep?_clock step]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

/-- An observation of the actual replay is computed by folding the corresponding row data.
The labels may retain physical data that semantic event labels deliberately omit. -/
theorem replayEvents?_fold {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {ρ α : Type*} {rows : List ρ}
    (label : ρ → ExecutionEvent) (observe : ExecutionState → α) (update : α → ρ → α)
    (success : replayEvents? policy program source (rows.map label) = some target)
    (effect : ∀ n current next row, rows[n]? = some row →
      replayEvents? policy program source ((rows.take n).map label) = some current →
      replayStep? policy program current (label row) = some next →
        observe next = update (observe current) row) :
    observe target = rows.foldl update (observe source) := by
  induction rows generalizing source with
  | nil => cases success; rfl
  | cons row rest ih =>
    obtain ⟨middle, step, suffix⟩ := Option.bind_eq_some_iff.mp success
    rw [List.foldl_cons, ← effect 0 source middle row rfl rfl step]
    apply ih suffix
    intro n current next item atItem prefixReplay replay
    apply effect (n + 1) current next item (by simpa only [List.getElem?_cons_succ] using atItem) _ replay
    simpa only [List.take_succ_cons, List.map_cons, replayEvents?, step, Option.bind_some] using prefixReplay

/-- An observation preserved at every actual prefix transition survives the complete replay. -/
theorem replayEvents?_preserves {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    {α : Sort*} (observe : ExecutionState → α)
    (success : replayEvents? policy program source events = some target)
    (frame : ∀ n current next event, events[n]? = some event →
      replayEvents? policy program source (events.take n) = some current →
      replayStep? policy program current event = some next → observe next = observe current) :
    observe target = observe source := by
  induction events generalizing source with
  | nil => cases success; rfl
  | cons event rest ih =>
    obtain ⟨middle, step, suffix⟩ := Option.bind_eq_some_iff.mp success
    refine (ih suffix ?_).trans (frame 0 source middle event rfl rfl step)
    intro n current next label atLabel prefixReplay replay
    apply frame (n + 1) current next label (by simpa only [List.getElem?_cons_succ] using atLabel) _ replay
    simpa only [List.take_succ_cons, replayEvents?, step, Option.bind_some] using prefixReplay

/-- The terminal-PC invariant propagates through replay, including the empty tape. -/
theorem replayEvents?_terminal_pc {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (initial : source.host.exitCode ≠ none →
      source.sail.regs.get? LeanRV64D.Defs.Register.PC = some haltPc)
    (success : replayEvents? policy program source events = some target)
    (stopped : target.host.exitCode ≠ none) :
    target.sail.regs.get? LeanRV64D.Defs.Register.PC = some haltPc := by
  induction events generalizing source with
  | nil => cases success; exact initial stopped
  | cons event rest ih =>
    obtain ⟨middle, step, suffix⟩ := Option.bind_eq_some_iff.mp success
    exact ih (replayStep?_terminal_pc step) suffix

/-- A replayed state that can fetch committed code is still running. The reserved HALT PC
cannot occur in the program image, so this guard follows from incoming State/Program truth. -/
theorem replayEvents?_running_of_fetch {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (initial : source.host.exitCode = none)
    (success : replayEvents? policy program source events = some target)
    {pc : BitVec 64} {word : BitVec 32}
    (atPc : target.sail.regs.get? LeanRV64D.Defs.Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) : target.host.exitCode = none := by
  by_contra stopped
  have parked := replayEvents?_terminal_pc (fun stopped => (stopped initial).elim) success stopped
  have same : pc = haltPc := Option.some.inj (atPc.symm.trans parked)
  rw [same, program.fetchWord_low_none (by decide : haltPc.toNat < 2 ^ 16)] at fetched
  contradiction

theorem ExecutionPath.replay {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) :
    replayEvents? policy program source events = some target := by
  induction path with
  | nil => rfl
  | cons step _ ih => simp only [replayEvents?, step.replay, Option.bind_some, ih]

/-- Prefix replay is the internal paired-state trajectory. Beyond the tape it holds the endpoint;
that mathematical extension does not add semantic steps. -/
noncomputable def executionTrajectory (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) (position : ℕ) : Option ExecutionState :=
  replayEvents? policy program source (events.take position)

@[simp] theorem executionTrajectory_zero (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) :
    executionTrajectory policy program source events 0 = some source := rfl

/-- At an actual event position, the paired trajectory executes exactly that event. -/
theorem executionTrajectory_succ (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) {position : ℕ} {event : ExecutionEvent}
    (present : events[position]? = some event) :
    executionTrajectory policy program source events (position + 1) =
      (executionTrajectory policy program source events position).bind
        (fun state => replayStep? policy program state event) := by
  have take : events.take (position + 1) = events.take position ++ [event] := by
    rw [List.take_succ_eq_append_getElem (List.getElem?_eq_some_iff.mp present).1,
      (List.getElem?_eq_some_iff.mp present).2]
  simp only [executionTrajectory, take, replayEvents?_append, replayEvents?, Option.bind_fun_some]

/-- Past the finite tape, the trajectory holds its endpoint without adding execution steps. -/
theorem executionTrajectory_after (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) (position : ℕ)
    (covered : events.length ≤ position) :
    executionTrajectory policy program source events position = replayEvents? policy program source events := by
  simp only [executionTrajectory, List.take_of_length_le covered]

/-- Valid paths authenticate the state returned at every semantic cut. -/
theorem ExecutionPath.replay_split {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) (cut : ℕ) :
    ∃ middle, executionTrajectory policy program source events cut = some middle ∧
      ExecutionPath policy program source (events.take cut) middle ∧
      ExecutionPath policy program middle (events.drop cut) target := by
  obtain ⟨middle, left, right⟩ := path.split cut
  exact ⟨middle, left.replay, left, right⟩

/-- Every actual event has a replayed source and its genuine next semantic step. -/
theorem ExecutionPath.step_at {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) {cut : ℕ} {event : ExecutionEvent}
    (atEvent : events[cut]? = some event) :
    ∃ current next, executionTrajectory policy program source events cut = some current ∧
      ExecutionStep policy program current event next := by
  induction path generalizing cut with
  | nil => simp at atEvent
  | @cons source middle target label events step rest ih =>
    cases cut with
    | zero =>
      have same : label = event := by simpa using atEvent
      subst event
      exact ⟨source, middle, rfl, step⟩
    | succ cut =>
      obtain ⟨current, next, prefixReplay, nextStep⟩ := ih (by simpa using atEvent)
      refine ⟨current, next, ?_, nextStep⟩
      simpa only [executionTrajectory, List.take_succ_cons, replayEvents?, step.replay, Option.bind_some]
        using prefixReplay

/-- Every replayed active position and its full event duration fit before the final clock. -/
theorem ExecutionPath.clock_at {policy : HostPolicy} {program : GuestProgram}
    {source target current : ExecutionState} {events : List ExecutionEvent} {event : ExecutionEvent}
    (path : ExecutionPath policy program source events target) {cut : ℕ}
    (atEvent : events[cut]? = some event)
    (replay : executionTrajectory policy program source events cut = some current) :
    current.clock + event.duration ≤ target.clock := by
  induction path generalizing cut with
  | nil => simp at atEvent
  | cons step tail ih =>
    cases cut with
    | zero =>
      cases Option.some.inj atEvent
      cases Option.some.inj replay
      have final := tail.clock
      have next := step.clock
      omega
    | succ cut =>
      apply ih (by simpa only [List.getElem?_cons_succ] using atEvent)
      simpa only [executionTrajectory, List.take_succ_cons, replayEvents?, step.replay,
        Option.bind_some] using replay

end SP1Clean.Model.Core
