import SP1Clean.Model.Core.HostQueue
import SP1Clean.Model.Core.BankReplay
import SP1Clean.Model.SP1Field

/-! # Stateful queue compilation regressions

Actual host dispatch drives the queue compiler through guest prepends, request-bound hook
responses, observations, and padded hint reads. These tests check changing lengths and complete
bytes; they do not claim the queue inventory is already authenticated by the mixed AIR.
-/

namespace SP1CleanTest.Core.HostQueue

open SP1Clean SP1Clean.Model.Core

private def policy : HostPolicy := ⟨⟨fun _ => false, NativeLayout.guestMemory⟩, SP1Prime⟩

private def context (kind : SyscallKind) (arg1 arg2 length : BitVec 64) : HostReadContext where
  register index :=
    if index = 5 then some kind.code else if index = 10 then some arg1 else
    if index = 11 then some arg2 else if index = 12 then some length else none
  byte address := some (if address = 65536 then 9 else if address = 65537 then 8 else 0)

private structure State where
  host : HostState
  store : HintQueue.Store
  head : ℕ
  lengths : List (BitVec 64) := []
  writes : List Bytes := []

private def initial : State :=
  let host : HostState := { io.hints := [[1, 2, 3]], replies := [⟨⟨15, [9, 8]⟩, [[], [7]]⟩] }
  let (store, head) := HintQueue.ofList host.io.hints
  ⟨host, store, head, [], []⟩

private abbrev Call := SyscallKind × BitVec 64 × BitVec 64 × BitVec 64

private def step (state : State) (call : Call) : Option State := do
  let execution ← state.host.run policy (context call.1 call.2.1 call.2.2.1 call.2.2.2)
  let (store, head) ← (state.host.hintUpdate execution).apply? state.store state.head
  some ⟨execution.effect.state, store, head,
    if execution.kind = .hintLength then state.lengths ++ [execution.result] else state.lengths,
    state.writes ++ execution.effect.write.toList.map (·.bytes)⟩

private def calls : List Call :=
  [(.hintLength, 0, 0, 0), (.write, 14, 65536, 2), (.hintLength, 0, 0, 0),
   (.enterUnconstrained, 0, 0, 0), (.commit, 0, 4, 0), (.commitDeferred, 1, 5, 0),
   (.verifyProof, 65536, 65536, 0), (.hintRead, 65536, 2, 0), (.write, 15, 65536, 2),
   (.hintLength, 0, 0, 0), (.hintRead, 65536, 0, 0), (.hintLength, 0, 0, 0),
   (.hintRead, 65536, 1, 0), (.hintLength, 0, 0, 0), (.hintRead, 65536, 3, 0),
   (.hintLength, 0, 0, 0), (.halt, 0, 0, 0)]

private def finalState : Option State := calls.foldlM step initial

private structure Summary where
  lengths : List (BitVec 64)
  writes : List Bytes
  nodes : ℕ
  decoded : Option (List Bytes)
  hints : List Bytes
  committed : BitVec 32
  deferred : BitVec 32
  requests : ℕ
  replies : ℕ
  exitCode : Option (BitVec 32)
deriving DecidableEq

private def summary (state : State) : Summary :=
  ⟨state.lengths, state.writes, state.store.size, HintQueue.decode? state.store state.head,
    state.host.io.hints, state.host.committed[0], state.host.deferred[1],
    state.host.requests.length, state.host.replies.length, state.host.exitCode⟩

/-- All eight calls share one mutable host and persistent queue. Empty hints still write their
mandatory padding word; the empty queue returns the sentinel only after every hint is consumed. -/
theorem changingQueue :
    finalState.map summary =
      some ⟨[3, 2, 0, 1, 3, BitVec.allOnes 64],
        [[9, 8, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0],
         [7, 0, 0, 0, 0, 0, 0, 0], [1, 2, 3, 0, 0, 0, 0, 0]],
        4, some [], [], 4, 5, 2, 0, some 0⟩ := by native_decide

/-- Both banks agree with the selected call fold through all eight kinds, including hook
writes and VERIFY. Nonzero untouched slots survive; reversing repeated writes changes the result.
This exercises the host projection, independently of mixed-AIR installation. -/
theorem bankProjection :
    let start := { initial with
      host := { initial.host with
        committed := #v[10, 20, 30, 40, 50, 60, 70, 80]
        deferred := #v[101, 102, 103, 104, 105, 106, 107, 108] } }
    let tape := calls.dropLast ++ [(.commit, 0, 11, 0), (.commitDeferred, 1, 12, 0), (.halt, 0, 0, 0)]
    let result := tape.foldlM step start
    result.map (fun state => (state.host.committed, state.host.deferred)) =
      some (#v[11, 20, 30, 40, 50, 60, 70, 80], #v[101, 12, 103, 104, 105, 106, 107, 108]) ∧
    [false, true].all (fun deferred =>
      let updates := tape.filterMap fun call => bankCall? deferred call.1.code call.2.1 call.2.2.1
      result.any fun state => decide (
        updates.foldl bankUpdate (start.host.bank deferred) = state.host.bank deferred ∧
        updates.reverse.foldl bankUpdate (start.host.bank deferred) ≠ state.host.bank deferred)) = true := by
  native_decide

/-- Every historical head still denotes its full original bytes after later prepends and pops. -/
theorem historicalHeads :
    finalState.map (fun state => (List.range 5).map (HintQueue.decode? state.store)) =
      some [some [], some [[1, 2, 3]], some [[9, 8], [1, 2, 3]],
        some [[7], [1, 2, 3]], some [[], [7], [1, 2, 3]]] := by native_decide

/-- Dangling, cyclic, and forward pointers fail. Equal lengths do not authenticate equal bytes. -/
theorem rejectsMalformedAndDistinguishesBytes :
    [HintQueue.decode? #[⟨[1], 0⟩] 2,
     HintQueue.decode? #[⟨[1], 1⟩] 1,
     HintQueue.decode? #[⟨[1], 2⟩, ⟨[2], 0⟩] 1] = [none, none, none] ∧
      HintQueue.hintLength? #[⟨[4, 5, 6], 0⟩] 1 = HintQueue.hintLength? initial.store initial.head ∧
      HintQueue.decode? #[⟨[4, 5, 6], 0⟩] 1 ≠ HintQueue.decode? initial.store initial.head := by
  native_decide

end SP1CleanTest.Core.HostQueue
