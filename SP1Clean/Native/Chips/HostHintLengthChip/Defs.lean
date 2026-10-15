import SP1Clean.FormalModel.Contracts.HintQueue
import SP1Clean.Native.Operations.ClockOrder
import Clean.Gadgets.Equality

/-! # HINT_LEN observes the current persistent queue head

Each row consumes one full instruction handoff and replaces a clocked queue state with the same
head. The nonempty variant consumes that head's immutable node record; the empty variant requires
zero head and the all-ones return. Every auxiliary clock witness is computed by Clean subcircuits.
-/

namespace SP1Clean.HostHintLengthChip

open Circuit HostHintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def main (empty : Bool) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.Equality.circuit Word) (input.call.code, const codeWord)
  assertion (Gadgets.Equality.circuit Word) (input.call.length, const (0 : Word (ZMod p)))
  let _ ← ClockOrder.circuit input.clock
  -- A `match` rather than `if empty`: `elaborate_circuit` reduces the literal-`Bool` match in each
  -- `cases` branch, while an `ite` on `false = true` stays stuck in the explicit metadata.
  match empty with
  | true =>
    assertion (Gadgets.Equality.circuit (fields 3)) (input.previous.head, const (0 : fields 3 (ZMod p)))
    assertion (Gadgets.Equality.circuit Word) (input.call.result, const emptyWord)
  | false =>
    assertion (Gadgets.Equality.circuit (fields 3)) (input.previous.head, input.node.pointer)
    assertion (Gadgets.Equality.circuit Word) (input.call.result, input.node.length)
    nodeChannel.pull input.node
  HostCallChip.channel.pull input.call
  stateChannel.pull input.previous
  stateChannel.push input.next

instance elaborated (empty : Bool) : ElaboratedCircuit (ZMod p) Inputs unit (main empty) := by
  cases empty <;> elaborate_circuit

end SP1Clean.HostHintLengthChip
