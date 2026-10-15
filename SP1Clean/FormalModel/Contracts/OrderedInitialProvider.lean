import SP1Clean.FormalModel.Contracts.MemoryBoundary
import SP1Clean.FormalModel.Contracts.OrderedMemoryProvider

/-! # Authenticated initial records with ordered address keys

The payload remains private to the chosen register or RAM provider. Both expose the same public
contract on their control link and Memory record, allowing one uniqueness theorem for a mixed table.
-/

namespace SP1Clean.OrderedInitialProvider

open SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels

abbrev Inputs := OrderedMemoryProvider.Inputs

variable {p : ℕ} [Fact p.Prime]

/-- The control key is the actual decoded Memory-bus location's address plus one. -/
def Spec (image : ProgramImage) (link : OrderedBoundary.Inputs (ZMod p))
    (record : MemoryMsg (ZMod p)) : Prop :=
  MemoryBoundary.InitialSpec image record ∧ OrderedBoundary.Spec link ∧
    Word.toNat link.current = (MemoryMsg.locOf record).busAddress + 1

end SP1Clean.OrderedInitialProvider
