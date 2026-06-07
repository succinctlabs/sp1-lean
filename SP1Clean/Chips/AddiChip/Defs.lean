import SP1Clean.Specs.Chip
import SP1Clean.Operations.AddOperation.Formal
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.ITypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.AddiChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `Addi` chip row as a `GeneralFormalCircuit`

The RISC-V `ADDI` (register-operand + immediate add) ported as a chip-level `GeneralFormalCircuit`. The
direct I-type analogue of `Chips/AddChip.lean`: it composes the **same** witnessed `AddOperation` gadget,
but over the **I-type** register adapter — the second summand is the adapter's *immediate* word
`op_c_imm` (threaded in as `input.op_c_val`), not a register read, so the reader sub-circuit is
`Readers.ITypeReader.circuit` (`Extracted/AddiChip.lean` calls `ITypeReader.asserts … opcode=1 …`).

Per `Extracted/AddiChip.lean` the chip's *own* asserts (everything past the composed
`AddOperation`/`CPUState`/`ITypeReader` sub-lists) reduce to just the `is_real` binary gate and
`op_a_0 = 0` (`AssertSpec`); the chip's *own* interactions tail is **empty**, so `InteractSpec := True`.
The semantic, `is_real`-gated `Spec` (the RV64 `add` identity on `cols.add_operation.value`, single
variant — `ADDI` has no flag split) lives in `Specs/Chip.lean`. `Faithful/AddiChip.lean` anchors the two
structural specs to SP1's extracted lists.

The `main` body composes the `CPUState`/`AddOperation`/`ITypeReader` sub-circuits (mirroring `AddChip.main`,
opcode `1`), witnesses the result word via `AddOperation.populate`, and gates `is_real`. Soundness and
completeness are fully proven (ported from `AddChip`), reusing the axiom-clean `AddOperation` gadget. -/

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

/-- Compose the threaded `CPUState`/`ITypeReader` reader blocks and the witnessed `AddOperation` gadget
as Clean sub-circuits (mirroring `AddChip.main`), **witness** the ALU result word `value` via
`AddOperation.populate` over the register operand `op_b_val` and the immediate `op_c_val`, gate `is_real`,
and assemble the extracted `AddiCols` struct. The `ITypeReader` carries `ADDI`'s opcode `1` and the four
`op_a_write_value` limbs `value[0..3]`. (The `AddChip` proofs are the direct template — swap `RTypeReader`
→ `ITypeReader`, opcode `0` → `1`, and the reader `Spec` accordingly.) -/
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
  -- The chip witnesses only the 4 result limbs (via `populate`); `AddOperation` is a `FormalAssertion`
  -- whose limb range checks are byte-bus pulls, and `CPUState`/`ITypeReader` are `assertion`s over the
  -- threaded `input.state`/`input.adapter` blocks (`localLength 0` each). The binary gate adds none.
  localLength _ := 4
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

end SP1Clean.AddiChip
