import SP1Clean.FormalModel.Contracts.HintReadSpan
import SP1Clean.Proofs.Operations.AddressDiv8
import SP1Clean.Native.Operations.AddressOrder
import SP1Clean.Proofs.Operations.AddrAddOperation.Address

/-! # Checked HINT_READ word-span endpoints

Reuse Euclidean division for alignment and padded count, inclusive address order for the guest
lower bound, and the bounded adder for the last written cell. The mathematical one-past endpoint
may equal `2^48`; it is never narrowed into an address field.
-/

namespace SP1Clean.HintReadSpan

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def minimum : fields 3 (ZMod p) := Address.ofNat (2 ^ 16)

def Inputs.startDivision {F : Type} [Zero F] (input : Inputs F) : AddressDiv8.Inputs F :=
  ⟨Address.asWord input.start, input.startQuotients⟩

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let start ← AddressDiv8.circuit input.startDivision
  let length ← AddressDiv8.circuit input.length
  assertZero start.remainder
  assertion AddressOrder.circuit ⟨const minimum, input.start⟩
  assertion AddrAddOperation.circuit ⟨Address.asWord input.start, length.rounded, ⟨input.last⟩, 1⟩
  assertion AddrAddOperation.circuit ⟨Address.asWord length.quotient, #v[1, 0, 0, 0], ⟨input.count⟩, 1⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by elaborate_circuit

end SP1Clean.HintReadSpan
