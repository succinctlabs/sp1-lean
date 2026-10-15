import SP1Clean.FormalModel.Contracts.MemoryBoundary
import SP1Clean.FormalModel.Contracts.OrderedBoundary

/-! # Canonical memory inventories

Initialization and finalization use the same ordering contract. Their separate record predicates
state the value semantics; the control key always names the actual decoded Memory location.
-/

namespace SP1Clean.OrderedMemoryProvider

open SP1Clean.Channels SP1Clean.Semantics

structure Inputs (Payload : TypeMap) (F : Type) where
  payload : Payload F
  link : OrderedBoundary.Inputs F
deriving ProvableStruct

variable {p : ℕ} [Fact p.Prime]

def Spec (recordSpec : MemoryMsg (ZMod p) → Prop) (link : OrderedBoundary.Inputs (ZMod p))
    (record : MemoryMsg (ZMod p)) : Prop :=
  recordSpec record ∧ OrderedBoundary.Spec link ∧
    Word.toNat link.current = (MemoryMsg.locOf record).busAddress + 1

end SP1Clean.OrderedMemoryProvider
