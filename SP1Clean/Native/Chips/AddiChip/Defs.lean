import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReader
import SP1Clean.Model.Channels
import SP1Clean.Extracted.AddiChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `Addi` chip row as a `GeneralFormalCircuit`

`ADDI`: the `AddOperation` gadget over an I-type adapter (second summand is the immediate `op_c_imm`,
not a register read); reader is `Readers.ITypeReader.circuit` with opcode `1`.
The `is_real`-gated semantic `Spec` (RV64 `add` identity on `cols.add_operation.value`) lives in
`Specs/Chip.lean`; soundness and completeness are fully proven. -/

namespace SP1Clean.AddiChip

open Circuit
open Extracted (AddiCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Assertion half** — the literal meaning of SP1's `AddiCols.asserts` *own* (inline) assertZero tail
(everything past the composed `AddOperation`/`CPUState`/`ITypeReader` sub-lists), in extracted order
(`Extracted/AddiChip.lean`: `E1, op_a_0`): the `is_real` binary gate and the `op_a_0` zeroing flag. -/
def AssertSpec (cols : AddiCols (ZMod p)) : Prop :=
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

/-- **Interaction half** — SP1's `AddiCols.interactions` *own* tail is **empty**
(`Extracted/AddiChip.lean` ends `… ++ [ ]`): every byte-range pull lives inside the composed
`AddOperation`/`CPUState`/`ITypeReader` sub-lists, anchored there. So the chip's own interaction meaning
is trivial. -/
def InteractSpec (_cols : AddiCols (ZMod p)) : Prop := True

/-- Compose the `CPUState`/`AddOperation`/`ITypeReader` sub-circuits, witness the ALU result word via
`AddOperation.populate`, gate `is_real`, and assemble the extracted `AddiCols` struct. The `ITypeReader`
carries opcode `1` and the four `op_a_write_value` limbs. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var AddiCols (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let value ← witnessVector 4 (fun env =>
    AddOperation.populate
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]])
  assertion AddOperation.circuit ⟨input.op_b_val, input.op_c_val, { value := value }, input.is_real⟩
  assertion Readers.ITypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 1,
     value[0], value[1], value[2], value[3]⟩
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, ⟨value⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs AddiCols main where
  channelsLawful := by simp [circuit_norm, main, AddOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit]
  localLength _ := 4
  -- `programChannel` joins the byte guarantee propagated up from `ITypeReader`'s program **pull** (W11 flip).
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw]

end SP1Clean.AddiChip
