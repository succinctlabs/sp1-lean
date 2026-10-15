import SP1Clean.Model.Core.Execution

/-! # Finite native execution segments and their composition

The primary semantic object is a local path between arbitrary complete states. Boot and HALT
are endpoint conditions, not separate instruction semantics. Paths compose through the exact
shared machine/host boundary and can be cut at any semantic step. No per-shard capacity is
imposed here: joining two legal shards need not produce a run that fits in one shard.

The labels are proof-free data. PolyFun's finite `Prefix` is an equivalent theorem view; it
does not introduce padding steps or assert AIR validity. Inactive rows and administrative
ledger work must be related to this path by the enclosing AIR proof.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Machine SP1Clean.Soundness.Target LeanRV64D PFunctor

/-- A finite path carrying exactly the executed instruction/syscall labels. -/
inductive ExecutionPath (policy : HostPolicy) (program : GuestProgram) :
    ExecutionState → List ExecutionEvent → ExecutionState → Prop
  | nil (state : ExecutionState) : ExecutionPath policy program state [] state
  | cons {source middle target : ExecutionState} {event : ExecutionEvent}
      {events : List ExecutionEvent} :
      ExecutionStep policy program source event middle →
      ExecutionPath policy program middle events target →
      ExecutionPath policy program source (event :: events) target

namespace ExecutionPath

variable {policy : HostPolicy} {program : GuestProgram}
  {source middle target : ExecutionState} {first second : List ExecutionEvent}

@[simp] theorem nil_iff : ExecutionPath policy program source [] target ↔ target = source := by
  constructor
  · intro path; cases path; rfl
  · rintro rfl; exact .nil _

/-- A shared boundary is the whole state, not just the PC/clock pair. -/
theorem append (left : ExecutionPath policy program source first middle)
    (right : ExecutionPath policy program middle second target) :
    ExecutionPath policy program source (first ++ second) target := by
  induction left with
  | nil => exact right
  | cons step _ ih => exact .cons step (ih right)

/-- Splitting a path supplies the same full state to both pieces. -/
theorem append_iff : ExecutionPath policy program source (first ++ second) target ↔
    ∃ middle, ExecutionPath policy program source first middle ∧
      ExecutionPath policy program middle second target := by
  constructor
  · intro path
    induction first generalizing source with
    | nil => exact ⟨source, .nil source, path⟩
    | cons event rest ih =>
        cases path with
        | cons step tail =>
            obtain ⟨middle, left, right⟩ := ih tail
            exact ⟨middle, .cons step left, right⟩
  · rintro ⟨middle, left, right⟩
    exact left.append right

/-- Every semantic cut is valid; a syscall and its effects occupy one indivisible step. -/
theorem split (path : ExecutionPath policy program source first target) (cut : ℕ) :
    ∃ middle, ExecutionPath policy program source (first.take cut) middle ∧
      ExecutionPath policy program middle (first.drop cut) target := by
  exact append_iff.mp (by simpa using path)

/-- The final interaction clock sums event costs, not table heights. -/
theorem clock (path : ExecutionPath policy program source first target) :
    target.clock = source.clock + (first.map ExecutionEvent.duration).sum := by
  induction path with
  | nil => simp
  | cons step _ ih =>
      rw [ih, step.clock]
      simp [Nat.add_assoc]

/-- No nonempty path starts at a halted state. Empty paths preserve every field. -/
theorem of_halted (path : ExecutionPath policy program source first target)
    (halted : source.host.exitCode ≠ none) : first = [] ∧ target = source := by
  cases path with
  | nil => exact ⟨rfl, rfl⟩
  | cons step _ => exact (halted step.running).elim

theorem running (path : ExecutionPath policy program source first target)
    (nonempty : first ≠ []) : source.host.exitCode = none := by
  cases path with
  | nil => exact (nonempty rfl).elim
  | cons step _ => exact step.running

/-- Equal numbers of steps from the same whole state give the same events and endpoint. -/
theorem deterministic {other : ExecutionState}
    (left : ExecutionPath policy program source first target)
    (right : ExecutionPath policy program source second other)
    (lengths : first.length = second.length) : first = second ∧ target = other := by
  induction left generalizing second other with
  | nil =>
      have empty : second = [] := by simpa using lengths.symm
      subst second
      exact ⟨rfl, (nil_iff.mp right).symm⟩
  | cons step _ ih =>
      cases right with
      | nil => simp at lengths
      | cons otherStep tail =>
          obtain ⟨rfl, rfl⟩ := step.deterministic otherStep
          obtain ⟨rfl, rfl⟩ := ih tail (by simpa using lengths)
          exact ⟨rfl, rfl⟩

/-- A nonempty path has a last real transition and a prefix ending at its exact source. -/
theorem last (path : ExecutionPath policy program source first target) (nonempty : first ≠ []) :
    ∃ events before event, first = events ++ [event] ∧
      ExecutionPath policy program source events before ∧
      ExecutionStep policy program before event target := by
  induction path with
  | nil => exact (nonempty rfl).elim
  | @cons source middle target event events step tail ih =>
      cases events with
      | nil =>
          obtain rfl := nil_iff.mp tail
          exact ⟨[], source, event, rfl, .nil source, step⟩
      | cons head rest =>
          obtain ⟨beforeEvents, before, lastEvent, same, leading, lastStep⟩ :=
            ih (List.cons_ne_nil _ _)
          exact ⟨event :: beforeEvents, before, lastEvent,
            congrArg (event :: ·) same, .cons step leading, lastStep⟩

/-- A running-to-halted path ends with an actual HALT; even exit zero cannot be forged by padding. -/
theorem ends_in_halt (path : ExecutionPath policy program source first target)
    (running : source.host.exitCode = none) {code : BitVec 32}
    (halted : target.host.exitCode = some code) :
    ∃ events before call, first = events ++ [.syscall call] ∧
      ExecutionPath policy program source events before ∧
      ExecutionStep policy program before (.syscall call) target ∧
      call.rawCode = 0 ∧ call.arg1.setWidth 32 = code := by
  have nonempty : first ≠ [] := by
    rintro rfl
    obtain rfl := nil_iff.mp path
    rw [running] at halted
    contradiction
  obtain ⟨events, before, event, same, leading, step⟩ := path.last nonempty
  obtain ⟨call, rfl, zero, exit⟩ := (step.halted_iff code).mp halted
  exact ⟨events, before, call, same, leading, step, zero, exit⟩

/-- Reassociation joins the same event tape and needs no intermediate boot condition. -/
theorem append_assoc {third : List ExecutionEvent} {next : ExecutionState}
    (left : ExecutionPath policy program source first middle)
    (center : ExecutionPath policy program middle second next)
    (right : ExecutionPath policy program next third target) :
    ExecutionPath policy program source (first ++ (second ++ third)) target :=
  left.append (center.append right)

end ExecutionPath

/-- Exactly `steps` successful local transitions, without prescribing boot or termination. -/
def ExecutionSegment (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (steps : ℕ) (target : ExecutionState) : Prop :=
  ∃ events, events.length = steps ∧ ExecutionPath policy program source events target

namespace ExecutionSegment

variable {policy : HostPolicy} {program : GuestProgram}
  {source middle target : ExecutionState} {m n : ℕ}

@[simp] theorem zero_iff : ExecutionSegment policy program source 0 target ↔ target = source := by
  simp [ExecutionSegment]

theorem refl (source : ExecutionState) : ExecutionSegment policy program source 0 source :=
  zero_iff.mpr rfl

theorem append (left : ExecutionSegment policy program source m middle)
    (right : ExecutionSegment policy program middle n target) :
    ExecutionSegment policy program source (m + n) target := by
  obtain ⟨first, firstLength, left⟩ := left
  obtain ⟨second, secondLength, right⟩ := right
  exact ⟨first ++ second, by simp [firstLength, secondLength], left.append right⟩

theorem add_iff : ExecutionSegment policy program source (m + n) target ↔
    ∃ middle, ExecutionSegment policy program source m middle ∧
      ExecutionSegment policy program middle n target := by
  constructor
  · rintro ⟨events, length, path⟩
    obtain ⟨middle, left, right⟩ := path.split m
    refine ⟨middle, ⟨events.take m, ?_, left⟩, ⟨events.drop m, ?_, right⟩⟩
    · simp [length]
    · simp [length]
  · rintro ⟨middle, left, right⟩
    exact left.append right

theorem of_halted (segment : ExecutionSegment policy program source n target)
    (halted : source.host.exitCode ≠ none) : n = 0 ∧ target = source := by
  obtain ⟨events, length, path⟩ := segment
  obtain ⟨rfl, rfl⟩ := path.of_halted halted
  exact ⟨length.symm, rfl⟩

theorem deterministic {other : ExecutionState}
    (left : ExecutionSegment policy program source n target)
    (right : ExecutionSegment policy program source n other) : target = other := by
  obtain ⟨first, firstLength, left⟩ := left
  obtain ⟨second, secondLength, right⟩ := right
  exact (left.deterministic right (firstLength.trans secondLength.symm)).2

end ExecutionSegment

/-- Dependent directions are precisely valid next steps of the concrete stateful core. -/
structure ExecutionDirection (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) where
  event : ExecutionEvent
  target : ExecutionState
  valid : ExecutionStep policy program source event target

def executionInterface (policy : HostPolicy) (program : GuestProgram) : PFunctor where
  A := ExecutionState
  B := ExecutionDirection policy program

def executionSystem (policy : HostPolicy) (program : GuestProgram) :
    DynSystem ExecutionState (executionInterface policy program) :=
  DynSystem.mk' id fun _ direction => direction.target

def executionEventMap (policy : HostPolicy) (program : GuestProgram) :
    (executionSystem policy program).EventMap ExecutionEvent :=
  fun _ direction => direction.event

/-- Every semantic path has a PolyFun orbit with the same events and full endpoint. -/
theorem ExecutionPath.exists_prefix {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) :
    ∃ orbit : DynSystem.Prefix (executionSystem policy program) source events.length,
      orbit.last = target ∧ orbit.events (executionEventMap policy program) = events := by
  induction path with
  | nil => exact ⟨.nil, rfl, rfl⟩
  | cons step _ ih =>
      obtain ⟨orbit, endpoint, labels⟩ := ih
      exact ⟨.step ⟨_, _, step⟩ orbit, endpoint, congrArg (_ :: ·) labels⟩

/-- The PolyFun view has exactly the same semantic steps; it cannot add idle or padding steps. -/
theorem executionPath_of_prefix {policy : HostPolicy} {program : GuestProgram}
    {source : ExecutionState} {steps : ℕ}
    (orbit : DynSystem.Prefix (executionSystem policy program) source steps) :
    ExecutionPath policy program source
      (orbit.events (executionEventMap policy program)) orbit.last := by
  induction orbit with
  | nil => exact .nil _
  | step direction _ ih => exact .cons direction.valid ih

theorem executionPrefix_events_length {policy : HostPolicy} {program : GuestProgram}
    {source : ExecutionState} {steps : ℕ}
    (orbit : DynSystem.Prefix (executionSystem policy program) source steps) :
    (orbit.events (executionEventMap policy program)).length = steps := by
  induction orbit with
  | nil => rfl
  | step _ _ ih => exact congrArg Nat.succ ih

/-- Counted native execution is exactly finite PolyFun reachability. -/
theorem ExecutionSegment.iff_reachableIn {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {steps : ℕ} :
    ExecutionSegment policy program source steps target ↔
      (executionSystem policy program).ReachableIn steps source target := by
  constructor
  · rintro ⟨events, rfl, path⟩
    obtain ⟨orbit, endpoint, _⟩ := path.exists_prefix
    exact ⟨orbit, endpoint⟩
  · rintro ⟨orbit, rfl⟩
    exact ⟨_, executionPrefix_events_length orbit, executionPath_of_prefix orbit⟩

end SP1Clean.Model.Core
