import SP1Clean.Proofs.Operations.HintReadSpanPopulate
import SP1Clean.Model.Core.HintQueueWordRecords

/-! # Checked HINT_READ endpoints bound to the actual immutable node

A final-word marker authenticates the true node extent. Together with its metadata and the
checked span, it rules out modulo-64-bit length aliases without a static source-size restriction.
The future handler must derive these bindings from the source/allocation and queue ledgers.
-/

namespace SP1Clean.HintReadSpan

open Model.Core Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime]

/-- The authenticated node and its final word agree with both checked span endpoints. -/
theorem Spec.node_end {input : Inputs (ZMod p)} (span : Spec input)
    {store : Store} (header : NodeRecord (ZMod p)) (binding : header.Binds store) (valid : header.Valid)
    (length : input.length.value = header.length) (word : WordRecord (ZMod p))
    (wordBinding : word.Binds store) (wordValid : word.Valid) (same : word.pointer = header.pointer)
    (last : word.isLast = 1) {node : Node} (read : node? store (Address.toNat header.pointer) = some node) :
    Word.toNat input.length.value = node.bytes.length ∧
      Address.toNat input.count = wordCount node.bytes ∧
      Address.toNat word.index + 1 = Address.toNat input.count := by
  have exactLength : Word.toNat input.length.value = node.bytes.length := by
    rw [length]
    exact binding.length_eq_of_last valid word wordBinding wordValid same last read
  have atWord : node? store (Address.toNat word.pointer) = some node := by rwa [same]
  have count := span.word_count node.bytes exactLength
  exact ⟨exactLength, count, ((wordBinding.isLast_iff atWord).mp last).trans count.symm⟩

end SP1Clean.HintReadSpan
