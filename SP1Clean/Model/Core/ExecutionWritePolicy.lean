import SP1Clean.Model.Core.ExecutionReplay
import SP1Clean.Model.Core.InstructionWrite

/-! # Ordinary write permission along the shared execution path

The permission predicate observes each ordinary event's actual incoming state by replaying its
prefix. It contains no AIR rows, compiler result, or second transition relation. Host events
already check their writes in `HostState.run`; ordinary events use `InstructionWrite.PermittedAt`.

The predicate restricts an existing `ExecutionPath`. Successful replay and normal retirement
remain obligations of that path, so a failed prefix cannot make an invalid execution admissible.
Empty paths impose no write obligation, including identities at halted states. Composition uses
the complete intermediate state, preserving changes to base registers made before a shard cut.
-/

namespace SP1Clean.Model.Core.ExecutionPath

open Machine Soundness.Target

/-- Every ordinary occurrence permits its full decoded write footprint at the replayed source.
This is a policy on an existing path, not evidence that replay or normal retirement succeeds. -/
def WritesPermitted (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) : Prop :=
  ∀ n current, events[n]? = some .ordinary →
    replayEvents? policy program source (events.take n) = some current →
      InstructionWrite.PermittedAt policy.memory.readOnly program current.sail

variable {policy : HostPolicy} {program : GuestProgram}
  {source middle target : ExecutionState} {event : ExecutionEvent} {events first second : List ExecutionEvent}

/-- An identity path has no ordinary writes to authorize. -/
@[simp] theorem writesPermitted_nil : WritesPermitted policy program source [] := by
  intro n current atEvent
  simp at atEvent

/-- At a genuine step, prefix-indexed permission is exactly the head obligation and tail policy. -/
theorem writesPermitted_cons_iff
    (step : ExecutionStep policy program source event middle) :
    WritesPermitted policy program source (event :: events) ↔
      (event = .ordinary → InstructionWrite.PermittedAt policy.memory.readOnly program source.sail) ∧
        WritesPermitted policy program middle events := by
  constructor
  · intro permitted
    refine ⟨fun ordinary => permitted 0 source (congrArg some ordinary) rfl, ?_⟩
    intro n current atEvent replay
    apply permitted (n + 1) current (by simpa only [List.getElem?_cons_succ] using atEvent)
    simpa only [List.take_succ_cons, replayEvents?, step.replay, Option.bind_some] using replay
  · rintro ⟨head, tail⟩ n current atEvent replay
    cases n with
    | zero =>
      have same : source = current := Option.some.inj replay
      subst current
      exact head (Option.some.inj atEvent)
    | succ n =>
      apply tail n current (by simpa only [List.getElem?_cons_succ] using atEvent)
      simpa only [List.take_succ_cons, replayEvents?, step.replay, Option.bind_some] using replay

/-- Permission composes exactly at the complete boundary of an actual execution prefix. -/
theorem writesPermitted_append_iff (left : ExecutionPath policy program source first middle) :
    WritesPermitted policy program source (first ++ second) ↔
      WritesPermitted policy program source first ∧ WritesPermitted policy program middle second := by
  induction left with
  | nil => simp only [List.nil_append, writesPermitted_nil, true_and]
  | cons step _ ih =>
    simp only [List.cons_append, writesPermitted_cons_iff step, ih, and_assoc]

/-- Joining permitted paths preserves the policy without resetting the source observations. -/
theorem WritesPermitted.append (left : WritesPermitted policy program source first)
    (right : WritesPermitted policy program middle second)
    (path : ExecutionPath policy program source first middle) :
    WritesPermitted policy program source (first ++ second) :=
  (writesPermitted_append_iff path).mpr ⟨left, right⟩

/-- Cutting a permitted path gives the same policy on both pieces and the actual shared state. -/
theorem WritesPermitted.split (permitted : WritesPermitted policy program source events)
    (path : ExecutionPath policy program source events target) (cut : ℕ) :
    ∃ middle, ExecutionPath policy program source (events.take cut) middle ∧
      ExecutionPath policy program middle (events.drop cut) target ∧
      WritesPermitted policy program source (events.take cut) ∧
      WritesPermitted policy program middle (events.drop cut) := by
  obtain ⟨middle, left, right⟩ := path.split cut
  have both := (writesPermitted_append_iff left).mp
    (show WritesPermitted policy program source (events.take cut ++ events.drop cut) by
      simpa only [List.take_append_drop] using permitted)
  exact ⟨middle, left, right, both⟩

/-- At an ordinary path head, permission is required even when the event changes no memory. -/
theorem WritesPermitted.head (permitted : WritesPermitted policy program source (.ordinary :: events)) :
    InstructionWrite.PermittedAt policy.memory.readOnly program source.sail :=
  permitted 0 source rfl rfl

end SP1Clean.Model.Core.ExecutionPath
