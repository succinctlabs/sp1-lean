import SP1Clean.Model.Core.HostQueue

/-! # Byte-level replay of queue observations and updates

Queue history records observed length words and the exact natural lengths of consumed hints.
Prepends include complete bytes and retain their order, covering guest WRITE and hook replies.
This is a projection of the existing host interpreter, not a second host execution relation:
`HostState.hintEvent_sound` derives its replay from every successful interpreter call.
-/

namespace SP1Clean.Model.Core

namespace HintQueue

inductive Event where
  | length (result : BitVec 64)
  | read (length : ℕ)
  | prepend (hints : List Bytes)
deriving DecidableEq, Repr

def Event.apply? : Event → List Bytes → Option (List Bytes)
  | .length result, hints => if result = (HostIO.mk hints []).hintLength then some hints else none
  | .read count, bytes :: rest => if bytes.length = count then some rest else none
  | .read _, [] => none
  | .prepend added, hints => some (added ++ hints)

def replay? (events : List Event) (hints : List Bytes) : Option (List Bytes) :=
  events.foldlM (fun hints event => event.apply? hints) hints

theorem replay?_cons (event : Event) (events : List Event) (hints : List Bytes) :
    replay? (event :: events) hints = (event.apply? hints).bind (replay? events) := rfl

theorem replay?_append (first second : List Event) (hints : List Bytes) :
    replay? (first ++ second) hints = (replay? first hints).bind (replay? second) :=
  List.foldlM_append

end HintQueue

/-- The queue observable of a concrete host result; queue-preserving calls prepend nothing. -/
def HostState.hintEvent (host : HostState) (execution : HostExecution) : HintQueue.Event :=
  if execution.kind = .hintLength then .length execution.result
  else if execution.kind = .hintRead then .read execution.arg2.toNat
  else .prepend (execution.effect.state.io.hints.take
    (execution.effect.state.io.hints.length - host.io.hints.length))

theorem HostState.hintEvent_sound {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {execution : HostExecution}
    (success : host.run policy context = some execution) :
    (host.hintEvent execution).apply? host.io.hints = some execution.effect.state.io.hints := by
  have facts := (host.run_eq_some_iff policy context execution).mp success
  have executed := facts.2.2.2.2.2
  by_cases length : execution.kind = .hintLength
  · have result := facts.2.2.2.2.1
    rw [length] at executed result
    have effect : execution.effect = ⟨host, none⟩ := (Option.some.inj executed).symm
    simp only [hintEvent, if_pos length, HintQueue.Event.apply?, effect, result,
      HostState.result, HostIO.hintLength, ↓reduceIte]
  · by_cases read : execution.kind = .hintRead
    · rw [read] at executed
      obtain ⟨bytes, rest, hints, count, _, _, effect⟩ :=
        (host.execute_hintRead_iff policy context execution.arg1 execution.arg2 execution.effect).mp executed
      simp only [hintEvent, if_neg length, if_pos read, hints, HintQueue.Event.apply?, count,
        ↓reduceIte, effect]
    · obtain ⟨added, hints⟩ := HostState.executeKind_hintSuffix executed read
      simp only [hintEvent, if_neg length, if_neg read, HintQueue.Event.apply?, hints,
        List.length_append, Nat.add_sub_cancel_right, List.take_left]

end SP1Clean.Model.Core
