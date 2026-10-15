import SP1Clean.FormalModel.Contracts.HostHintRead
import SP1Clean.Proofs.Operations.HintReadSpan
import SP1Clean.Proofs.Operations.HintReadStep
import SP1Clean.Native.Operations.ClockOrder
import Clean.Gadgets.Equality

/-! # Native HINT_READ handler

All call operands, the full return code, current head, padded span, and actual final-word
request are connected by Clean subcircuits. The emitted word endpoints require the physical
consumer tables to cover the whole write. This row itself performs no physical Memory access.
-/

namespace SP1Clean.HostHintReadChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.Equality.circuit Word) (input.call.code, const codeWord)
  assertion (Gadgets.Equality.circuit Word) (input.call.length, const (0 : Word (ZMod p)))
  assertion (Gadgets.Equality.circuit Word) (input.call.result, const codeWord)
  assertion (Gadgets.Equality.circuit Word) (input.call.arg1, Address.asWord input.span.start)
  assertion (Gadgets.Equality.circuit Word) (input.call.arg2, input.span.length.value)
  assertion (Gadgets.Equality.circuit Word) (input.span.length.value, input.node.length)
  assertion (Gadgets.Equality.circuit (fields 3)) (input.previous.head, input.node.pointer)
  let _ ← ClockOrder.circuit input.clock
  let _ ← HintReadSpan.circuit input.span
  let _ ← HintReadStep.circuit true input.endStep
  HostHintQueue.nodeChannel.pull input.node
  HostCallChip.channel.pull input.call
  HostHintQueue.stateChannel.pull input.previous
  HostHintQueue.stateChannel.push input.next
  HintReadWordChip.stateChannel.push input.first
  HintReadWordChip.stateChannel.pull input.final

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by elaborate_circuit

end SP1Clean.HostHintReadChip
