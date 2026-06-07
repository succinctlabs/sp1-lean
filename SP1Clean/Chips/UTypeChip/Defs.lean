import SP1Clean.Specs.Chip
import SP1Clean.Operations.AddOperation.Formal
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.JTypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.UTypeChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The U-type chip row (`LUI` / `AUIPC`) as a `GeneralFormalCircuit`

Composes, as true Clean subcircuits (mirroring SP1's `UType` `air.rs:eval`, `Extracted/UTypeChip.lean`):

- the `Readers.CPUState` adapter, fed the **straight-line** `next_pc = [pc[0] + 4, pc[1], pc[2]]` and
  `clk_inc = 8` (U-type does not branch);
- a single `AddOperation` gadget `addend + op_b_imm = add_operation.value` — the rd write value — gated
  **additively** by `is_real - op_a_0` (so it is not enforced when `rd = x0`), where the witnessed `addend`
  is `is_auipc · pc` (= the program counter for AUIPC, `0` for LUI);
- the `Readers.JTypeReader` adapter (program fetch at the flag-selected opcode `is_auipc·48 + (1-is_auipc)·49`
  with `imm_b = imm_c = 1`, the two `op_a` memory writes, and the `op_a_0` binary + zeroing gates);
- the per-limb `addend[i] = is_auipc · pc[i]` gates, the `is_auipc` binary gate, and the `is_real` binary gate.

The chip `Spec` (in `Specs/Chip.lean`) is the J-type reader sub-`Spec` + the proven `is_real`/`is_auipc`
binary facts + the `is_real`/`op_a_0`-gated `RV64.lui`/`RV64.auipc` identities. The buses' cross-row meaning
(the PC chain, memory permutation) lives at the trace level in `Soundness/{State,Memory}Consistency.lean`.

(`main` + the `ElaboratedCircuit` instance; the `Assumptions`/`Spec`/soundness/completeness/`circuit` live
in the sibling `Formal` module, the Sail bridge in `Bridge`.) -/

namespace SP1Clean.UTypeChip

open Circuit
open Extracted (UTypeColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Compose the U-type row. The chip **witnesses** the addend (`is_auipc · pc`, three limbs) and the add
result (`addend + op_b_imm`, four limbs via `AddOperation.populate`), composes the `CPUState` reader (with a
straight-line `next_pc`), the `AddOperation` gadget (additive `is_real - op_a_0` gate), and the J-type reader,
then pins the addend with the per-limb `is_auipc · pc` gates and the two binary gates. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var UTypeColumns (ZMod p)) := do
  let addend ← witnessVector 3 (fun env =>
    #v[env input.is_auipc * env input.state.pc[0],
       env input.is_auipc * env input.state.pc[1],
       env input.is_auipc * env input.state.pc[2]])
  let add_value ← witnessVector 4 (fun env =>
    AddOperation.populate
      #v[env input.is_auipc * env input.state.pc[0],
         env input.is_auipc * env input.state.pc[1],
         env input.is_auipc * env input.state.pc[2], 0]
      #v[env input.adapter.op_b_imm[0], env input.adapter.op_b_imm[1],
         env input.adapter.op_b_imm[2], env input.adapter.op_b_imm[3]])
  let addendV : Word (Expression (ZMod p)) := #v[addend[0], addend[1], addend[2], 0]
  -- CPUState with the straight-line next_pc = [pc[0] + 4, pc[1], pc[2]].
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  -- add_operation: addend + op_b_imm = rd write value, gated additively by `is_real - op_a_0`.
  assertion AddOperation.circuit
    ⟨addendV, input.adapter.op_b_imm, { value := add_value }, input.is_real - input.adapter.op_a_0⟩
  -- JTypeReader: program fetch (flag-selected opcode), op_a memory writes, op_a_0 binary + zeroing gates.
  assertion Readers.JTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     input.is_auipc * 48 + (1 - input.is_auipc) * 49,
     add_value[0], add_value[1], add_value[2], add_value[3]⟩
  -- addend correctness: addend[i] = is_auipc * pc[i] (pc for AUIPC, 0 for LUI).
  addend[0] - input.is_auipc * input.state.pc[0] === 0
  addend[1] - input.is_auipc * input.state.pc[1] === 0
  addend[2] - input.is_auipc * input.state.pc[2] === 0
  input.is_auipc * (input.is_auipc - 1) === 0
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, addend, ⟨add_value⟩, input.is_auipc, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs UTypeColumns main where
  channelsLawful := by simp [circuit_norm, main, AddOperation.circuit, Readers.CPUState.circuit, Readers.JTypeReader.circuit]
  -- The chip witnesses the 3 addend limbs + 4 add-result limbs (7); the readers/operation are `assertion`s
  -- (`localLength 0`), the gates add no witnesses.
  localLength _ := 7
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

end SP1Clean.UTypeChip
