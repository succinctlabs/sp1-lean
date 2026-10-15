import SP1Clean.FormalModel.Contracts.HintNodeAllocate
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Native.Operations.AddressOrder
import SP1Clean.Proofs.Operations.AddrAddOperation.Formal

/-! # A checked append to the persistent hint store

Compose existing word bounds, inclusive address order, and nonwrapping address addition. The
new pointer is exactly the old allocation frontier plus one; it cannot reuse a popped identity.
The operation does not publish node contents or alter the queue ledger by itself: its enclosing
host handler must authorize the bytes and assemble its full before/after call transition.
-/

namespace SP1Clean.HintNodeAllocate

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var HostHintQueue.State (ZMod p)) := do
  assertion WordRangeCheck.circuit (Address.asWord input.previous.head)
  assertion WordRangeCheck.circuit (Address.asWord input.previous.allocated)
  assertion AddressOrder.circuit ⟨input.previous.head, input.previous.allocated⟩
  assertion (Gadgets.Equality.circuit (fields 3)) (input.node.tail, input.previous.head)
  assertion WordRangeCheck.circuit input.node.length
  assertion AddrAddOperation.circuit input.addition
  return input.next

instance elaborated : ElaboratedCircuit (ZMod p) Inputs HostHintQueue.State main := by elaborate_circuit

end SP1Clean.HintNodeAllocate
