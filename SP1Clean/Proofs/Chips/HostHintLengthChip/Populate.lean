import SP1Clean.Proofs.Chips.HostHintLengthChip.Formal
import SP1Clean.Model.Core.HostQueue
import SP1Clean.Proofs.Operations.HintQueueCursor
import SP1Clean.Proofs.Chips.HostControlPopulate
import SP1Clean.Proofs.Operations.ClockOrderPopulate

/-! # HINT_LEN rows from successful host execution

The constructor selects the empty/nonempty component and reads the actual immutable head node.
Successful dispatch supplies the return; only the explicit pointer and strictly increasing
48-bit queue-clock bounds remain compiler-domain conditions.
-/

namespace SP1Clean.HostHintLengthChip

open SP1Clean.Model.Core SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def populate (store : HintQueue.Store) (head previousClock clock : ℕ)
    (executed : HostExecution) : Inputs (ZMod p) :=
  ⟨HostControl.message clock executed,
    HostHintQueue.State.encode previousClock head store.size,
    HintQueue.NodeRecord.encode head ((HintQueue.node? store head).getD default)⟩

private theorem clock_spec (store : HintQueue.Store) (head previousClock clock : ℕ)
    (executed : HostExecution) (fits : clock < 2 ^ 48) (order : previousClock < clock) :
    ClockOrder.Spec (populate (p := p) store head previousClock clock executed).clock :=
  ClockOrder.encode_spec previousClock clock fits order

/-- The actual semantic call constructs both routing and the complete handler domain. -/
theorem populate_spec_of_run (store : HintQueue.Store) (head previousClock clock : ℕ)
    (executed : HostExecution) (host : HostState) (policy : HostPolicy) (context : HostReadContext)
    (success : host.run policy context = some executed) (kind : executed.kind = .hintLength)
    (current : HintQueue.Represents store head host.io.hints)
    (headBound : head < 2 ^ 48) (fits : clock < 2 ^ 48) (order : previousClock < clock) :
    Spec (decide (head = 0)) (populate (p := p) store head previousClock clock executed) := by
  refine ⟨?_, rfl, clock_spec store head previousClock clock executed fits order, ?_⟩
  · simp only [populate, HostControl.message, kind, codeWord]
  have length := HostState.hintLength?_of_run success kind current
  by_cases empty : head = 0
  · have result : executed.result = BitVec.allOnes 64 := by
      simpa only [empty, HintQueue.hintLength?, ↓reduceIte, Option.some.injEq] using length.symm
    simp [HeadSpec, empty, populate, HostControl.message, result, emptyWord, HostHintQueue.State.encode, Address.ofNat]
    rfl
  · obtain ⟨node, read, descending⟩ : ∃ node, HintQueue.node? store head = some node ∧ node.tail < head := by
      generalize host.io.hints = hints at current
      cases current with
      | nil => exact False.elim (empty rfl)
      | cons read descending _ => exact ⟨_, read, descending⟩
    have result : executed.result = BitVec.ofNat 64 node.bytes.length := by
      simpa only [HintQueue.hintLength?, if_neg empty, read, Option.map_some, Option.some.injEq] using length.symm
    simp only [HeadSpec, decide_eq_false empty, Bool.false_eq_true, ↓reduceIte,
      populate, read, Option.getD_some, HostControl.message]
    exact ⟨rfl, congrArg bitVecToWord result, HintQueue.NodeRecord.encode_valid _ _ headBound descending⟩

/-- The constructor's nonempty node also binds to the same persistent store used by the semantics. -/
theorem populate_binding (store : HintQueue.Store) (head previousClock clock : ℕ)
    (executed : HostExecution) (hints : List Bytes) (current : HintQueue.Represents store head hints)
    (headBound : head < 2 ^ 48) (nonempty : head ≠ 0) :
    (populate (p := p) store head previousClock clock executed).node.Binds store := by
  cases current with
  | nil => exact False.elim (nonempty rfl)
  | cons read descending _ =>
    simp only [populate, read, Option.getD_some]
    exact HintQueue.NodeRecord.encode_binds read headBound descending

/-- The input records the full allocation frontier, including nodes no longer in the current queue. -/
theorem populate_cursor (store : HintQueue.Store) (head previousClock clock : ℕ)
    (executed : HostExecution) (hints : List Bytes) (current : HintQueue.Represents store head hints)
    (fits : store.size < 2 ^ 48) :
    (populate (p := p) store head previousClock clock executed).previous.Binds store hints :=
  HostHintQueue.State.encode_binds previousClock current fits

end SP1Clean.HostHintLengthChip
