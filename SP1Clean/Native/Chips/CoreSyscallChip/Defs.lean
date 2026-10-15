import SP1Clean.Proofs.Chips.SyscallInstrsChip.Formal
import SP1Clean.Native.Operations.SyscallCodeGuard

/-! # The native core syscall instruction circuit

Compose the complete SP1 syscall instruction circuit with the native full-code profile guard.
The guard adds a fixed lookup and no witness columns or channel interactions. Host effects are
still a separate circuit boundary: this instruction row alone does not authenticate WRITE's x12
and RAM reads or HINT_READ's writes.
-/

namespace SP1Clean.CoreSyscallChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (input : Var SyscallInstrsChip.Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← SyscallInstrsChip.circuit input
  assertion SyscallCodeGuard.circuit ⟨input.op_a_memory.prev_value, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) SyscallInstrsChip.Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := SyscallInstrsChip.circuit.channelsWithGuarantees

end SP1Clean.CoreSyscallChip
