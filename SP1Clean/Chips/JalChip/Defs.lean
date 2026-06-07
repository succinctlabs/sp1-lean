import SP1Clean.Specs.Chip
import SP1Clean.Operations.AddOperation.Formal
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.JTypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Foundations.ByteTable
import SP1Clean.Extracted.JalChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The JAL chip row as a `GeneralFormalCircuit` — control-flow proof of concept

The first **control-flow** chip: its committed `next_pc` is *computed data* (the jump target
`add_operation.value`), not the straight-line `pc + 4` every ALU chip passes. Composes, as true Clean
subcircuits (mirroring SP1's `Jal` `air.rs:eval`, `Extracted/JalChip.lean`):

- the `Readers.CPUState` adapter, fed the **data-dependent** `next_pc = add_operation.value` (the jump
  target) and `clk_inc = 8`;
- **two** `AddOperation` gadgets — `pc + op_b_imm = add_operation.value` (the jump target, gated `is_real`)
  and `pc + 4 = op_a_operation.value` (the return/link address, gated *additively* by `is_real - op_a_0`,
  so it is not enforced when `rd = x0`);
- the `Readers.JTypeReader` adapter (program fetch at opcode 46 with `imm_b = imm_c = 1`, the two `op_a`
  memory writes, and the `op_a_0` binary + zeroing gates);
- the 4-byte **alignment** range check on the jump target (`Range(add_operation.value[0] / 4, 14)`);
- the `is_real` binary gate.

The chip `Spec` is the J-type reader sub-`Spec` + the proven `is_real`-binary + the `is_real`-gated jump
(`add_operation.value = pc + op_b_imm`) and link (`op_a_0 = 0 → op_a_operation.value = pc + 4`) identities.
The buses' cross-row meaning (the PC chain now threading a *data-dependent* `next_pc`, memory permutation)
lives at the trace level in `Soundness/{State,Memory}Consistency.lean`. -/

namespace SP1Clean.JalChip

open Circuit
open Extracted (JalColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `14 < p`, so the alignment `Range` byte-row width column `14` round-trips through `byteRowSpec_range`. -/
lemma h14p : (14 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- Compose the JAL row. The chip **witnesses** the two add results (`add_operation.value` = the jump
target, `op_a_operation.value` = the link address) via `AddOperation.populate`, then composes the demoted
`AddOperation` gadget as a Clean `assertion` over each whole `⟨a, b, value, gate⟩` column struct. The
`CPUState` reader is fed the **data-dependent** `next_pc = add_operation.value`; the second add's gate is
the additive `is_real - op_a_0` (SP1's `op_a_operation` gate). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var JalColumns (ZMod p)) := do
  let add_value ← witnessVector 4 (fun env =>
    AddOperation.populate
      #v[env input.state.pc[0], env input.state.pc[1], env input.state.pc[2], 0]
      #v[env input.adapter.op_b_imm[0], env input.adapter.op_b_imm[1],
         env input.adapter.op_b_imm[2], env input.adapter.op_b_imm[3]])
  let op_a_value ← witnessVector 4 (fun env =>
    AddOperation.populate
      #v[env input.state.pc[0], env input.state.pc[1], env input.state.pc[2], 0]
      #v[4, 0, 0, 0])
  let pcWordV : Word (Expression (ZMod p)) :=
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0]
  -- CPUState with the **data-dependent** next_pc = jump target = add_operation.value.
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[add_value[0], add_value[1], add_value[2]], 8, input.is_real⟩
  -- add_operation: pc + op_b_imm = next_pc (jump target), gated `is_real`.
  assertion AddOperation.circuit ⟨pcWordV, input.adapter.op_b_imm, { value := add_value }, input.is_real⟩
  add_value[3] === 0
  -- op_a_operation: pc + 4 = link address, gated additively by `is_real - op_a_0`.
  assertion AddOperation.circuit
    ⟨pcWordV, #v[4, 0, 0, 0], { value := op_a_value }, input.is_real - input.adapter.op_a_0⟩
  op_a_value[3] === 0
  -- JTypeReader: program fetch (opcode 46), op_a memory writes, op_a_0 binary + zeroing gates.
  assertion Readers.JTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 46,
     op_a_value[0], op_a_value[1], op_a_value[2], op_a_value[3]⟩
  -- next_pc 4-byte alignment: Range(add_operation.value[0] / 4, 14).
  byteChannel.gatedReceive input.is_real
    (⟨6, (add_value[0] * (4 : ZMod p)⁻¹), Expression.const ((14 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, ⟨add_value⟩, ⟨op_a_value⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs JalColumns main where
  channelsLawful := by simp [circuit_norm, main, AddOperation.circuit, Readers.CPUState.circuit, Readers.JTypeReader.circuit]
  -- The chip witnesses the two add results (8 limbs); the readers/operations are `assertion`s
  -- (`localLength 0`), the alignment pull and binary gate add no witnesses.
  localLength _ := 8
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

end SP1Clean.JalChip
