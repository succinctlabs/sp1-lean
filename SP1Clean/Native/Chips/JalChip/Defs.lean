import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.JTypeReader
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import SP1Clean.Extracted.JalChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The JAL chip row as a `GeneralFormalCircuit`

`next_pc` is computed data (the jump target `add_operation.value`), not `pc + 4`. Composes two
`AddOperation` gadgets (jump target `pc + op_b_imm` + link address `pc + 4`), `CPUState`, `JTypeReader`,
and a 4-byte alignment range check (`Range(add_operation.value[0] / 4, 14)`). The link-address gate is
`is_real - op_a_0` (not enforced when `rd = x0`). Implements SP1's `Jal` `air.rs:eval`. -/

namespace SP1Clean.JalChip

open Circuit
open Extracted (JalColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `14 < p`, so the alignment `Range` byte-row width column `14` round-trips through `byteRowSpec_range`. -/
lemma h14p : (14 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- Witness the two add results (`add_operation.value` = jump target, `op_a_operation.value` = link
address) via `AddOperation.populate`, then compose as Clean `assertion`s. The `CPUState` reader is fed
the data-dependent `next_pc = add_operation.value`; the link add's gate is `is_real - op_a_0`. -/
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
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[add_value[0], add_value[1], add_value[2]], 8, input.is_real⟩
  assertion AddOperation.circuit ⟨pcWordV, input.adapter.op_b_imm, { value := add_value }, input.is_real⟩
  add_value[3] === 0
  assertion AddOperation.circuit
    ⟨pcWordV, #v[4, 0, 0, 0], { value := op_a_value }, input.is_real - input.adapter.op_a_0⟩
  op_a_value[3] === 0
  assertion Readers.JTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 46,
     op_a_value[0], op_a_value[1], op_a_value[2], op_a_value[3]⟩
  byteChannel.pullIf input.is_real
    (⟨6, (add_value[0] * (4 : ZMod p)⁻¹), Expression.const ((14 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, ⟨add_value⟩, ⟨op_a_value⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs JalColumns main where
  channelsLawful := by simp [circuit_norm, main, AddOperation.circuit, Readers.CPUState.circuit, Readers.JTypeReader.circuit]
  -- 2 × 4-limb add-result witnesses; all readers/operations are `assertion`s (localLength 0).
  localLength _ := 8
  channelsWithGuarantees := [byteChannel.toRaw]

end SP1Clean.JalChip
