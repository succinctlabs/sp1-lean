import SP1Clean.FormalModel.Contracts.HintQueue
import SP1Clean.FormalModel.Contracts.Operations

/-! # Fresh persistent hint-node allocation

One append consumes the next unused identity, links to the current head, and advances both
head and allocation frontier. Popping a head never releases an identity. This is an internal
queue operation; the host handler must separately authenticate the allocated bytes and its call.
-/

namespace SP1Clean.HintNodeAllocate

open SP1Clean.Model.Core

structure Inputs (F : Type) where
  previous : HostHintQueue.State F
  node : HintQueue.NodeRecord F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def Inputs.next {F : Type} (input : Inputs F) : HostHintQueue.State F :=
  ⟨input.previous.clk_high, input.previous.clk_low, input.node.pointer, input.node.pointer⟩

def Inputs.addition {F : Type} [Zero F] [One F] (input : Inputs F) : AddrAddOperation.Inputs F :=
  ⟨Address.asWord input.previous.allocated, #v[1, 0, 0, 0], ⟨input.node.pointer⟩, 1⟩

def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  Address.Bounded input.previous.head ∧ Address.Bounded input.previous.allocated ∧
    Address.toNat input.previous.head ≤ Address.toNat input.previous.allocated ∧
    input.node.tail = input.previous.head ∧ input.node.Valid ∧
    Address.toNat input.node.pointer = Address.toNat input.previous.allocated + 1

end SP1Clean.HintNodeAllocate
