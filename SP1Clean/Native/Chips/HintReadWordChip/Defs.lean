import SP1Clean.FormalModel.Contracts.HintReadWord
import SP1Clean.FormalModel.Contracts.WritePermission
import SP1Clean.Proofs.Operations.HintReadStep
import SP1Clean.Proofs.Chips.HostRamAccessChip.Formal
import Clean.Circuit.Loops

/-! # A physical padded hint word consumer

The two bundled subcircuits connect the actual Memory update to the immutable word and its
successor. Every written byte, including padding, requests writable permission. The RAM access's
coordination pair cancels internally; the private cursor accounts for the entire row inventory.
-/

namespace SP1Clean.HintReadWordChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def main (last : Bool) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← HostRamAccessChip.circuit input.ram
  let _ ← HintReadStep.circuit last (input.step last)
  HostRamAccessChip.channel.pull input.ram.message
  Circuit.forEach (Vector.range 8) fun index =>
    WritePermissionProvider.channel.pull (Address.offset input.address (.const (index : ZMod p)))
  stateChannel.pull input.previous
  stateChannel.push input.next

instance elaborated (last : Bool) : ElaboratedCircuit (ZMod p) Inputs unit (main last) := by
  cases last <;> elaborate_circuit

end SP1Clean.HintReadWordChip
