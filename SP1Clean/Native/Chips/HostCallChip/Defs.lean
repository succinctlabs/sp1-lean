import SP1Clean.FormalModel.Contracts.HostCall
import SP1Clean.Proofs.Chips.CoreSyscallChip.Formal
import SP1Clean.Native.Readers.RegisterRead
import Clean.Gadgets.IsEqual

/-! # A native syscall row with its host-call handoff

The full-word equality gadget computes WRITE selection internally. That selector gates the
extra x12 Memory pair, while the instruction's activity gate controls the host-call handoff.
The original instruction circuit, including its PublicValues interactions, is preserved.
-/

namespace SP1Clean.HostCallChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← CoreSyscallChip.circuit input.instruction
  let flag ← Gadgets.IsEqual.circuit (input.instruction.op_a_memory.prev_value, const writeWord)
  let _ ← Readers.RegisterRead.circuit (input.read flag)
  channel.pushIf input.instruction.is_real (input.message flag)

/-- The internal equality output; the raw-constraint bridge identifies its meaning. -/
def selector (input : Var Inputs (ZMod p)) (offset : ℕ) : Expression (ZMod p) :=
  Gadgets.IsEqual.circuit.output
    (input.instruction.op_a_memory.prev_value, const writeWord) offset

/-- Keep the composed operation spine separate from the instruction's large row. -/
theorem operations_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (main input).operations offset =
      [.subcircuit (CoreSyscallChip.circuit.toSubcircuit offset input.instruction),
       .subcircuit (Gadgets.IsEqual.circuit.toSubcircuit offset
         (input.instruction.op_a_memory.prev_value, const writeWord)),
       .subcircuit (Readers.RegisterRead.circuit.toSubcircuit (offset + 8)
         (input.read (selector input offset))),
       .interact (channel.pushedIf input.instruction.is_real
         (input.message (selector input offset))).toRaw] := by
  rfl

@[circuit_norm] theorem core_requirements :
    (CoreSyscallChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] := rfl

@[circuit_norm] theorem read_requirements :
    (Readers.RegisterRead.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] theorem equal_requirements :
    (Gadgets.IsEqual.circuit (F := ZMod p) (α := Word)).channelsWithRequirements = [] := rfl

omit [Fact (2 ^ 25 < p)] in
set_option linter.unusedSectionVars false in
@[local circuit_norm] private theorem equal_guarantees :
    (Gadgets.IsEqual.circuit (F := ZMod p) (α := Word)).channelsWithGuarantees = [] := rfl

@[local circuit_norm] private theorem read_guarantees :
    (Readers.RegisterRead.circuit (p := p)).channelsWithGuarantees =
      [byteChannel.toRaw, memoryChannel.toRaw] := rfl

@[circuit_norm] theorem core_guarantees :
    (CoreSyscallChip.circuit (p := p)).channelsWithGuarantees =
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
        exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw] := rfl

attribute [local circuit_norm] channel

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit

@[circuit_norm] theorem channelsWithGuarantees_eq :
    (elaborated (p := p)).channelsWithGuarantees =
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
        exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw,
        byteChannel.toRaw, memoryChannel.toRaw] := rfl

end SP1Clean.HostCallChip
