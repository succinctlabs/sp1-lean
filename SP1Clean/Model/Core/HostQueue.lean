import SP1Clean.Model.Core.HintQueue
import SP1Clean.Model.Core.HostExecutionLaws

/-! # Queue updates derived from complete host execution

The eight-call interpreter either preserves the queue, prepends guest/hook hints, or consumes
one hint. The compiler below derives that update from its successful result and preserves the
entire persistent suffix. It does not assume a static source queue or accept a claimed HINT_LEN
return. These are semantic compilation proofs; the mixed AIR must still authenticate allocations,
head transitions, and observations with its own ledgers.
-/

namespace SP1Clean.Model.Core

namespace HintQueue

inductive Update where
  | prepend (hints : List Bytes)
  | pop
deriving DecidableEq, Repr

def Update.allocations : Update → ℕ
  | .prepend hints => hints.length
  | .pop => 0

def Update.apply? (update : Update) (store : Store) (head : ℕ) : Option (Store × ℕ) :=
  match update with
  | .prepend hints => some (HintQueue.prepend store head hints)
  | .pop => (pop? store head).map (fun (_, tail) => (store, tail))

/-- No call changes any previously allocated hint bytes or links. -/
theorem Update.apply?_extends {update : Update} {store next : Store} {head tail : ℕ}
    (success : update.apply? store head = some (next, tail)) : Extends store next := by
  cases update with
  | prepend hints =>
    have same : (HintQueue.prepend store head hints).1 = next := congrArg Prod.fst (Option.some.inj success)
    rw [← same]
    exact prepend_extends store head hints
  | pop =>
    obtain ⟨⟨bytes, pointer⟩, _, same⟩ := Option.map_eq_some_iff.mp success
    cases same
    exact .refl store

/-- Exact allocation cost, including zero allocations for observations and pops. -/
theorem Update.apply?_size {update : Update} {store next : Store} {head tail : ℕ}
    (success : update.apply? store head = some (next, tail)) :
    next.size = store.size + update.allocations := by
  cases update with
  | prepend hints =>
    have same : (HintQueue.prepend store head hints).1 = next := congrArg Prod.fst (Option.some.inj success)
    rw [← same]
    exact prepend_size store head hints
  | pop =>
    obtain ⟨⟨bytes, pointer⟩, _, same⟩ := Option.map_eq_some_iff.mp success
    cases same
    rfl

/-- Compilation preserves every local node condition and keeps the new root in the inventory. -/
theorem Update.apply?_valid {update : Update} {store next : Store} {head tail : ℕ}
    (valid : WellFormed store) (bound : head ≤ store.size)
    (success : update.apply? store head = some (next, tail)) :
    WellFormed next ∧ tail ≤ next.size := by
  cases update with
  | prepend hints =>
    have same := Option.some.inj success
    have storeEq : (HintQueue.prepend store head hints).1 = next := congrArg Prod.fst same
    have headEq : (HintQueue.prepend store head hints).2 = tail := congrArg Prod.snd same
    rw [← storeEq, ← headEq]
    exact ⟨prepend_wellFormed valid bound hints, prepend_head_bound bound hints⟩
  | pop =>
    obtain ⟨⟨bytes, pointer⟩, popped, same⟩ := Option.map_eq_some_iff.mp success
    cases same
    obtain ⟨node, read, pairEq⟩ := Option.map_eq_some_iff.mp popped
    have tailEq : node.tail = tail := congrArg Prod.snd pairEq
    have descending := valid _ _ read
    exact ⟨valid, by omega⟩

end HintQueue

/-- WRITE preserves its old queue as a suffix, even when a request-bound hook supplies hints. -/
theorem HostState.writeOutput_hintSuffix {host next : HostState} {descriptor : BitVec 64}
    {bytes : Bytes} (success : host.writeOutput descriptor bytes = some next) :
    ∃ added, next.io.hints = added ++ host.io.hints := by
  unfold HostState.writeOutput at success
  split_ifs at success
  all_goals try { cases success; exact ⟨[], rfl⟩ }
  · cases success
    exact ⟨[bytes], rfl⟩
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at success
    obtain ⟨⟨io, replies⟩, applied, rfl⟩ := success
    obtain ⟨hints, _, rfl⟩ := (host.io.applyHook_eq_some_iff _ _ _ _).mp applied
    exact ⟨hints, rfl⟩

/-- HINT_READ is the sole queue-consuming arm; every other arm only prepends or preserves. -/
theorem HostState.executeKind_hintSuffix {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {kind : SyscallKind} {arg1 arg2 : BitVec 64} {effect : HostEffect}
    (success : host.executeKind policy context kind arg1 arg2 = some effect)
    (notRead : kind ≠ .hintRead) :
    ∃ added, effect.state.io.hints = added ++ host.io.hints := by
  cases kind with
  | hintRead => exact False.elim (notRead rfl)
  | write =>
    obtain ⟨_, _, _, _, _, written, rfl⟩ :=
      (host.execute_write_iff policy context arg1 arg2 effect).mp success
    exact HostState.writeOutput_hintSuffix written
  | verifyProof =>
    simp only [HostState.executeKind, bind, Option.bind_eq_some_iff, Option.some.injEq] at success
    obtain ⟨_, _, _, _, rfl⟩ := success
    exact ⟨[], rfl⟩
  | enterUnconstrained | hintLength => cases success; exact ⟨[], rfl⟩
  | halt | commit | commitDeferred =>
    simp only [HostState.executeKind] at success
    split_ifs at success
    all_goals cases success; exact ⟨[], rfl⟩

/-- Compile the actual host effect. Unchanged queues become a zero-allocation prepend. -/
def HostState.hintUpdate (host : HostState) (execution : HostExecution) : HintQueue.Update :=
  if execution.kind = .hintRead then .pop
  else .prepend (execution.effect.state.io.hints.take
    (execution.effect.state.io.hints.length - host.io.hints.length))

/-- Every successful host call has a computed queue update, with no extra readiness condition. -/
theorem HostState.hintUpdate_sound {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {execution : HostExecution}
    (success : host.run policy context = some execution)
    {store : HintQueue.Store} {head : ℕ} (represents : HintQueue.Represents store head host.io.hints) :
    ∃ next, (host.hintUpdate execution).apply? store head = some next ∧
      HintQueue.Represents next.1 next.2 execution.effect.state.io.hints := by
  have executed := (host.run_eq_some_iff policy context execution).mp success |>.2.2.2.2.2
  by_cases isRead : execution.kind = .hintRead
  · rw [isRead] at executed
    obtain ⟨bytes, rest, hints, _, _, _, effect⟩ :=
      (host.execute_hintRead_iff policy context execution.arg1 execution.arg2 execution.effect).mp executed
    rw [hints] at represents
    obtain ⟨tail, popped, suffix, _⟩ := HintQueue.pop?_of_represents represents
    refine ⟨(store, tail), ?_, ?_⟩
    · simp [hintUpdate, isRead, HintQueue.Update.apply?, popped]
    · simpa only [effect] using suffix
  · obtain ⟨added, hints⟩ := HostState.executeKind_hintSuffix executed isRead
    refine ⟨HintQueue.prepend store head added, ?_, ?_⟩
    · simp only [hintUpdate, if_neg isRead, hints, List.length_append, Nat.add_sub_cancel_right,
        List.take_left, HintQueue.Update.apply?]
    · rw [hints]
      exact HintQueue.prepend_represents represents added

/-- A represented current queue supplies the interpreter's actual HINT_LEN return word. -/
theorem HostState.hintLength?_of_run {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {execution : HostExecution}
    (success : host.run policy context = some execution) (kind : execution.kind = .hintLength)
    {store : HintQueue.Store} {head : ℕ} (represents : HintQueue.Represents store head host.io.hints) :
    HintQueue.hintLength? store head = some execution.result := by
  have result := (host.run_eq_some_iff policy context execution).mp success |>.2.2.2.2.1
  rw [result, kind]
  exact HintQueue.hintLength?_of_represents represents

end SP1Clean.Model.Core
