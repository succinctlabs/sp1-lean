import SP1Clean.FormalModel.Contracts.HintReadStep
import SP1Clean.Proofs.Operations.AddrAddOperation.Address
import SP1Clean.Native.Operations.WordRangeCheck
import Clean.Gadgets.Equality

/-! # Checked successor and address for a hint word consumer

All arithmetic crosses existing Clean proof boundaries. The immutable word pull includes its
end marker. The final variant retains the current cell instead of encoding a one-past address.
-/

namespace SP1Clean.HintReadStep

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def increment {F : Type} [Zero F] [OfNat F 8] (last : Bool) : Word F :=
  #v[if last then 0 else 8, 0, 0, 0]

def main (last : Bool) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  HostHintQueue.wordChannel.pull input.word
  assertZero (input.word.isLast - (if last then 1 else 0))
  assertion WordRangeCheck.circuit (Address.asWord input.address)
  assertion AddrAddOperation.circuit ⟨Address.asWord input.word.index, #v[1, 0, 0, 0], ⟨input.nextIndex⟩, 1⟩
  assertion AddrAddOperation.circuit ⟨Address.asWord input.address, increment last, ⟨input.nextAddress⟩, 1⟩

instance elaborated (last : Bool) : ElaboratedCircuit (ZMod p) Inputs unit (main last) := by
  elaborate_circuit

end SP1Clean.HintReadStep
