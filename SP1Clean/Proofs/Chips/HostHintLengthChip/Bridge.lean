import SP1Clean.Proofs.Chips.HostHintLengthChip.Formal
import SP1Clean.Model.Core.HostQueue

/-! # Current-queue HINT_LEN semantics

The node binding and current-head representation remain explicit assembly premises. Together
with the local handler contract they determine the entire host call: the exact return, unchanged
host state, and no guest-memory write. Neither premise is a channel payload guarantee.
-/

namespace SP1Clean.HostHintLengthChip

open SP1Clean.Model.Core SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def execution (input : Inputs (ZMod p)) (host : HostState) : HostExecution :=
  ⟨.hintLength, Word.toBitVec64 input.call.arg1, Word.toBitVec64 input.call.arg2,
    Word.toBitVec64 input.call.result, ⟨host, none⟩⟩

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Observing a length preserves both the current head and all allocated historical identities. -/
theorem next_binds (input : Inputs (ZMod p)) (store : HintQueue.Store) (hints : List Bytes)
    (current : input.previous.Binds store hints) : input.next.Binds store hints := current

/-- The same statement covers an empty queue and a nonempty queue, including empty hint bytes. -/
theorem result_of_spec (empty : Bool) (input : Inputs (ZMod p)) (valid : Spec empty input)
    (host : HostState) (store : HintQueue.Store)
    (current : HintQueue.Represents store (Address.toNat input.previous.head) host.io.hints)
    (binding : empty = false → input.node.Binds store) :
    Word.toBitVec64 input.call.result = host.io.hintLength := by
  have observed : HintQueue.hintLength? store (Address.toNat input.previous.head) =
      some (Word.toBitVec64 input.call.result) := by
    cases empty with
    | false =>
      have head := valid.2.2.2
      change input.previous.head = input.node.pointer ∧
        input.call.result = input.node.length ∧ input.node.Valid at head
      rw [head.1, head.2.1]
      exact (binding rfl).hintLength
    | true =>
      have head := valid.2.2.2
      change input.previous.head = 0 ∧ input.call.result = emptyWord at head
      rw [head.1, head.2]
      simp [HintQueue.hintLength?, Address.toNat, emptyWord, toBitVec64_bitVecToWord]
  exact Option.some.inj (observed.symm.trans (HintQueue.hintLength?_of_represents current))

/-- Register observations and authenticated current-queue data imply the full host transition. -/
theorem run_of_spec (empty : Bool) (input : Inputs (ZMod p)) (valid : Spec empty input)
    (host : HostState) (store : HintQueue.Store)
    (current : HintQueue.Represents store (Address.toNat input.previous.head) host.io.hints)
    (binding : empty = false → input.node.Binds store)
    (running : host.exitCode = none) (policy : HostPolicy) (context : HostReadContext)
    (code : context.register 5 = some (Word.toBitVec64 input.call.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 input.call.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 input.call.arg2)) :
    host.run policy context = some (execution input host) := by
  apply (host.run_eq_some_iff policy context (execution input host)).mpr
  refine ⟨running, ?_, arg1, arg2, ?_, rfl⟩
  · simpa only [valid.1, codeWord, toBitVec64_bitVecToWord, execution] using code
  · exact result_of_spec empty input valid host store current binding

end SP1Clean.HostHintLengthChip
