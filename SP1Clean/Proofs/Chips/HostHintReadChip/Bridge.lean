import SP1Clean.Proofs.Chips.HostHintReadChip.Formal
import SP1Clean.Proofs.Operations.HintReadSpanNode
import SP1Clean.Model.Core.HostExecutionLaws

/-! # HINT_READ reaches the concrete host interpreter

Authenticated current-queue, node, and final-word records determine the exact natural length,
queue pop, and complete padded write. Actual writable permission and register observations
remain explicit until the enclosing AIR derives them. No per-instruction or word case split is
part of the host execution statement.
-/

namespace SP1Clean.HostHintReadChip

open Model.Core Model.Core.HintQueue Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private theorem queue_tail {store : Store} {head : ℕ} {hints : List Bytes} {node : Node}
    (current : Represents store head hints) (read : node? store head = some node) :
    ∃ rest, hints = node.bytes :: rest ∧ Represents store node.tail rest := by
  cases current with
  | nil => simp [node?] at read
  | cons found _ suffix =>
    have same := Option.some.inj (found.symm.trans read)
    cases same
    exact ⟨_, rfl, suffix⟩

omit [Fact (2 ^ 17 < p)] in
/-- The checked handler consumes exactly the current node, including its true natural extent. -/
theorem node_effect_of_spec (input : Inputs (ZMod p)) (valid : Spec input)
    (store : Store) (hints : List Bytes) (current : input.previous.Binds store hints)
    (header : input.node.Binds store) (word : input.endStep.word.Binds store) :
    ∃ node rest, node? store (Address.toNat input.node.pointer) = some node ∧
      hints = node.bytes :: rest ∧ input.next.Binds store rest ∧
      Word.toNat input.call.arg2 = node.bytes.length ∧
      Address.toNat input.span.count = wordCount node.bytes := by
  obtain ⟨_, _, _, _, length, nodeLength, head, _, span, ending, nodeValid⟩ := valid
  have headerBinding := header
  obtain ⟨node, read, tail, _⟩ := header
  have currentHead := current.2.2.2
  rw [head] at currentHead
  obtain ⟨rest, hints, suffix⟩ := queue_tail currentHead read
  have extent := span.node_end input.node headerBinding nodeValid nodeLength input.endStep.word
    word ending.1 rfl rfl read
  refine ⟨node, rest, read, hints, ?_, ?_, extent.2.1⟩
  · exact ⟨nodeValid.2.1, current.2.1, current.2.2.1, tail.symm ▸ suffix⟩
  · rw [length]
    exact extent.1

def execution (input : Inputs (ZMod p)) (host : HostState) (bytes : Bytes) (rest : List Bytes) :
    HostExecution :=
  ⟨.hintRead, Word.toBitVec64 input.call.arg1, Word.toBitVec64 input.call.arg2,
    Word.toBitVec64 input.call.result, ⟨{ host with io := { host.io with hints := rest } },
      some ⟨Address.toNat input.span.start, hintWriteBytes bytes⟩⟩⟩

/-- A full interpreter call follows from authenticated records and permissions for the checked span. -/
theorem run_of_spec (input : Inputs (ZMod p)) (valid : Spec input)
    (host : HostState) (store : Store) (current : input.previous.Binds store host.io.hints)
    (header : input.node.Binds store) (word : input.endStep.word.Binds store)
    (running : host.exitCode = none) (policy : HostPolicy) (context : HostReadContext)
    (permitted : policy.memory.permits (Address.toNat input.span.start)
      (8 * (Word.toNat input.span.length.value / 8 + 1)) = true)
    (code : context.register 5 = some (Word.toBitVec64 input.call.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 input.call.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 input.call.arg2)) :
    ∃ bytes rest, host.io.hints = bytes :: rest ∧ input.next.Binds store rest ∧
      Address.toNat input.span.count = wordCount bytes ∧
      host.run policy context = some (execution input host bytes rest) := by
  obtain ⟨node, rest, _, hints, next, length, count⟩ :=
    node_effect_of_spec input valid store host.io.hints current header word
  obtain ⟨hcode, _, result, address, argLength, _, _, _, span, _⟩ := valid
  have addressNat : (Word.toBitVec64 input.call.arg1).toNat = Address.toNat input.span.start := by
    rw [address, Word.toBitVec64_toNat (Address.isU64_asWord span.1), Address.toNat_asWord]
  have lengthNat : (Word.toBitVec64 input.call.arg2).toNat = node.bytes.length := by
    rw [argLength, Word.toBitVec64_toNat span.2.1]
    rwa [argLength] at length
  have permission : policy.memory.permits (Address.toNat input.span.start)
      (hintWriteBytes node.bytes).length = true := by
    rw [hintWriteBytes_length]
    rw [argLength] at length
    rwa [length] at permitted
  refine ⟨node.bytes, rest, hints, next, count, ?_⟩
  apply (host.run_eq_some_iff policy context (execution input host node.bytes rest)).mpr
  refine ⟨running, ?_, arg1, arg2, ?_, ?_⟩
  · simpa only [hcode, codeWord, toBitVec64_bitVecToWord, execution] using code
  · simp only [execution, result, codeWord, toBitVec64_bitVecToWord, HostState.result]
  · apply (host.execute_hintRead_iff policy context _ _ _).mpr
    exact ⟨node.bytes, rest, hints, lengthNat.symm,
      addressNat ▸ span.2.2.1.2.1, addressNat ▸ permission, by simp only [execution, addressNat]⟩

end SP1Clean.HostHintReadChip
