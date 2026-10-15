import SP1Clean.FormalModel.Contracts.HostControl
import Clean.Gadgets.Equality

/-! # Constrained-replay ENTER_UNCONSTRAINED

Consume the full instruction handoff with the canonical code and zero return. Arguments are
unused by this call and stay unrestricted. All fields are supplied by the matched instruction.
-/

namespace SP1Clean.HostEnterChip

open Circuit

variable {p : ℕ} [Fact p.Prime]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.Equality.circuit Word) (input.code, const codeWord)
  assertion (Gadgets.Equality.circuit Word) (input.result, const (0 : Word (ZMod p)))
  assertion (Gadgets.Equality.circuit Word) (input.length, const (0 : Word (ZMod p)))
  HostCallChip.channel.pull input

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit

end SP1Clean.HostEnterChip
