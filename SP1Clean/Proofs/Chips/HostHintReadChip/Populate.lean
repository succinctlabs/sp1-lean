import SP1Clean.Proofs.Chips.HostHintReadChip.Formal
import SP1Clean.Proofs.Operations.HintReadSpanPopulate
import SP1Clean.Proofs.Chips.HostControlPopulate
import SP1Clean.Proofs.Operations.HintQueueCursor
import SP1Clean.Proofs.Operations.ClockOrderPopulate

/-! # HINT_READ rows from successful semantic calls

The constructor reads the actual current node and its final padded word. Successful dispatch
derives the exact length, alignment, and complete span bounds. Only store capacity and bounded
strict event-clock order remain resource conditions of the enclosing compiler.
-/

namespace SP1Clean.HostHintReadChip

open Model.Core Model.Core.HintQueue Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def populate (store : Store) (head previousClock clock : ℕ) (executed : HostExecution) : Inputs (ZMod p) :=
  let node := (node? store head).getD default
  ⟨HostControl.message clock executed, HostHintQueue.State.encode previousClock head store.size,
    NodeRecord.encode head node,
    HintReadSpan.populate (Address.ofNat executed.arg1.toNat) (bitVecToWord executed.arg2),
    Address.ofNat (node.bytes.length / 8), bitVecToWord (wordValue node.bytes (node.bytes.length / 8))⟩

private theorem natural_word (word : BitVec 64) : Word.toNat (bitVecToWord (p := p) word) = word.toNat := by
  rw [← Word.toBitVec64_toNat (isU64_bitVecToWord _), toBitVec64_bitVecToWord]

omit [Fact (2 ^ 25 < p)] in
private theorem address_word (word : BitVec 64) (fits : word.toNat < 2 ^ 48) :
    bitVecToWord (p := p) word = Address.asWord (Address.ofNat word.toNat) := by
  apply Vector.ext
  intro index bound
  interval_cases index <;> simp [bitVecToWord, Address.asWord, Address.ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_eq_of_lt (show word.toNat < 281474976710656 from fits)]
  simp

private theorem final_step (span : HintReadSpan.Inputs (ZMod p)) (valid : HintReadSpan.Spec span)
    (pointer : ℕ) (bytes : Bytes) (positive : 0 < pointer) (bounded : pointer < 2 ^ 48)
    (length : Word.toNat span.length.value = bytes.length) :
    HintReadStep.Spec true
      ⟨WordRecord.encode pointer bytes (bytes.length / 8), span.last, span.count, span.last⟩ := by
  have domain := valid.2.2.1
  rw [length] at domain
  have indexBound : bytes.length / 8 < 2 ^ 48 := by have := domain.bounds.2.1; omega
  refine ⟨WordRecord.encode_valid pointer bytes _ positive bounded, ?_, valid.2.2.2.1,
    valid.2.2.2.2.2.1, ?_, valid.2.2.2.1, by simp⟩
  · simp only [WordRecord.encode, wordCount, ↓reduceIte]
  · simp only [WordRecord.encode, Address.toNat_ofNat _ indexBound]
    rw [valid.2.2.2.2.2.2, length]

private theorem populate_at_node (store : Store) (head previousClock clock : ℕ)
    (executed : HostExecution) (bytes : Bytes) (tail : ℕ)
    (read : node? store head = some ⟨bytes, tail⟩) (descending : tail < head)
    (headBound : head < 2 ^ 48) (kind : executed.kind = .hintRead)
    (result : executed.result = SyscallKind.hintRead.code) (length : bytes.length = executed.arg2.toNat)
    (domain : HintReadSpan.Domain executed.arg1.toNat bytes.length)
    (fits : clock < 2 ^ 48) (order : previousClock < clock) :
    let input := populate (p := p) store head previousClock clock executed
    ProverAssumptions input ∧ input.node.Binds store ∧ input.endStep.word.Binds store := by
  have startBound := domain.bounds.1
  have nodeBound := domain.bounds.2.1
  have indexBound : bytes.length / 8 < 2 ^ 48 := by omega
  have valueLength : Word.toNat (bitVecToWord (p := p) executed.arg2) = bytes.length := by
    rw [natural_word, length]
  have spanDomain : HintReadSpan.Domain
      (Address.toNat (Address.ofNat (p := p) executed.arg1.toNat))
      (Word.toNat (bitVecToWord (p := p) executed.arg2)) := by
    rwa [Address.toNat_ofNat _ startBound, valueLength]
  have span := HintReadSpan.populate_spec _ _ (Address.bounded_ofNat _) (isU64_bitVecToWord _) spanDomain
  have spanAssumptions := HintReadSpan.populate_assumptions _ _
    (Address.bounded_ofNat _) (isU64_bitVecToWord _) spanDomain
  have exactArg : executed.arg2 = BitVec.ofNat 64 bytes.length := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bytes.length < 2 ^ 64)]
    exact length.symm
  have marker : bytes.length / 8 + 1 = wordCount bytes := rfl
  have endWord : (populate (p := p) store head previousClock clock executed).endStep.word =
      WordRecord.encode head bytes (bytes.length / 8) := by
    simp only [populate, read, Option.getD_some, Inputs.endStep, NodeRecord.encode,
      WordRecord.encode, marker, ↓reduceIte]
  have wordBinding := WordRecord.encode_binds (p := p) read headBound (bytes.length / 8)
    (by simp only [wordCount]; omega) indexBound
  refine ⟨⟨spanAssumptions, ?_⟩, ?_, endWord.symm ▸ wordBinding⟩
  · refine ⟨?_, rfl, ?_, ?_, rfl, ?_, rfl,
      ClockOrder.encode_spec previousClock clock fits order, span, ?_, ?_⟩
    · simp only [populate, HostControl.message, kind, codeWord]
    · simp only [populate, HostControl.message, result, codeWord]
    · exact address_word executed.arg1 startBound
    · simp only [populate, read, Option.getD_some, HintReadSpan.populate, AddressDiv8.populate,
        NodeRecord.encode, exactArg]
    · have step := final_step _ span head bytes (by omega) headBound valueLength
      rw [← endWord] at step
      exact step
    · simpa only [populate, read, Option.getD_some] using
        NodeRecord.encode_valid (p := p) head ⟨bytes, _⟩ headBound descending
  · simpa only [populate, read, Option.getD_some] using
      NodeRecord.encode_binds (p := p) read headBound descending

/-- The interpreter supplies the complete handler domain and authentic records together. -/
theorem populate_of_run (store : Store) (head previousClock clock : ℕ)
    (executed : HostExecution) (host : HostState) (policy : HostPolicy) (context : HostReadContext)
    (success : host.run policy context = some executed) (kind : executed.kind = .hintRead)
    (current : Represents store head host.io.hints) (capacity : store.size < 2 ^ 48)
    (lower : 2 ^ 16 ≤ policy.memory.lower) (upper : policy.memory.upper ≤ 2 ^ 48)
    (fits : clock < 2 ^ 48) (order : previousClock < clock) :
    let input := populate (p := p) store head previousClock clock executed
    ProverAssumptions input ∧ input.previous.Binds store host.io.hints ∧
      input.node.Binds store ∧ input.endStep.word.Binds store := by
  have cursor := HostHintQueue.State.encode_binds (p := p) previousClock current capacity
  have run := (host.run_eq_some_iff policy context executed).mp success
  have effect := run.2.2.2.2.2
  rw [kind] at effect
  obtain ⟨bytes, rest, hints, length, aligned, permitted, _⟩ :=
    (host.execute_hintRead_iff policy context executed.arg1 executed.arg2 executed.effect).mp effect
  have result : executed.result = SyscallKind.hintRead.code := by
    simpa only [kind, HostState.result] using run.2.2.2.2.1
  have domain := HintReadSpan.domain_of_permitted bytes policy.memory executed.arg1.toNat
    lower upper aligned permitted
  rw [hints] at current
  cases current with
  | cons read descending _ =>
    have result := populate_at_node (p := p) store head previousClock clock executed bytes _ read descending
      (by have := node?_bound read; omega) kind result length domain fits order
    exact ⟨result.1, cursor, result.2⟩

end SP1Clean.HostHintReadChip
