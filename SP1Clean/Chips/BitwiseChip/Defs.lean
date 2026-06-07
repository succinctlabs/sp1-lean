import SP1Clean.Specs.Chip
import SP1Clean.Operations.BitwiseU16Operation
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.ALUTypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.BitwiseChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The Bitwise chip row (AND/OR/XOR) as a `GeneralFormalCircuit`, output = the extracted column struct

The RISC-V bitwise family (`AND`/`OR`/`XOR`) ported as a chip-level `GeneralFormalCircuit`, keyed on
SP1's `Extracted.BitwiseCols` (`is_xor`/`is_or`/`is_and` selectors, composing the witnessed
`BitwiseU16Operation` gadget). **Structural mirror of `Chips/LtChip`**: it composes the
`CPUState`/`BitwiseU16Operation`/`ALUTypeReader` sub-circuits as true Clean `assertion`/`subcircuit`s
(emitting all four buses), witnesses the three variant flags, threads the SP1-derived `byte_opcode`
(`is_xor·2 + is_or·1 + is_and·0`) into the gadget and `cpu_opcode` (`is_xor·3 + is_or·4 + is_and·5`) into
the reader, gates `is_real`, emits the flag-boolean + sum-bound + `op_a_0` zeroing gates (`AssertSpec`),
and assembles the extracted `BitwiseCols` struct.

Per `Extracted/BitwiseChip.lean` the chip's *own* asserts (everything past the composed
`BitwiseU16Operation`/`CPUState`/`ALUTypeReader` sub-lists) reduce to the three selector booleans, their
sum-bound, and `op_a_0 = 0` (`AssertSpec`); the chip's *own* interactions tail is **empty**, so
`InteractSpec := True`. The operands `rs1`/`rs2` are projected from the adapter (the Memory-bus register
reads `op_b_memory.prev_value`/`op_c_memory.prev_value`) rather than carried as separate columns. The
semantic, `is_real`/flag-gated `Spec` (the RV64 `and`/`or`/`xor` identities) lives in the sibling `Formal`
module; the Sail bridge in `Bridge`. -/

namespace SP1Clean.BitwiseChip

open Circuit
open Extracted (BitwiseCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The `is_real` selector and the threaded committed reader column blocks `state`/`adapter` (the latter
an immediate-capable `ALUTypeReader`). The `rs1`/`rs2` operands are projected from the adapter (the
Memory-bus register reads) — see `Inputs.op_b_val`/`op_c_val` below — rather than carried as separate
committed columns. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
deriving ProvableStruct

/-- `rs1` operand = the `op_b` register read (`op_b_memory.prev_value`); `rs2` operand = the `op_c`
register read (`op_c_memory.prev_value`). Both feed the bitwise gadget exactly as in the extraction. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- The reassembled bitwise result word the reader writes for `rd`: the eight result bytes packed into
four 16-bit limbs (`BitwiseU16Operation.resultWord`). -/
def resultWord (cols : BitwiseCols (ZMod p)) : Word (ZMod p) :=
  BitwiseU16Operation.resultWord cols.bitwise_operation.bitwise_operation.result

/-- **Assertion half** — the literal meaning of SP1's `BitwiseCols.asserts` *own* (inline) assertZero
tail (everything past the composed `BitwiseU16Operation`/`CPUState`/`ALUTypeReader` sub-lists), in
extracted order (`Extracted/BitwiseChip.lean`: `E3,E5,E7,E9, op_a_0`): the three opcode-flag booleans
(`is_xor`, `is_or`, `is_and`), the sum-bound boolean on `E1 = is_xor + is_or + is_and`, and the
`op_a_0` zeroing flag. The byte-level bitwise arithmetic is *not* here — it is the composed
`BitwiseU16Operation` sub-list. -/
def AssertSpec (cols : BitwiseCols (ZMod p)) : Prop :=
  let x := cols.is_xor; let o := cols.is_or; let a := cols.is_and
  let sum := x + o + a
  x * (x - 1) = 0 ∧
  o * (o - 1) = 0 ∧
  a * (a - 1) = 0 ∧
  sum * (sum - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

/-- **Interaction half** — SP1's `BitwiseCols.interactions` *own* tail is **empty**
(`Extracted/BitwiseChip.lean` ends `… ++ [ ]`): every byte-range pull for the bitwise op lives inside
the composed `BitwiseU16Operation` sub-list, anchored at the operation level. So the chip's own
interaction meaning is trivial. -/
def InteractSpec (_cols : BitwiseCols (ZMod p)) : Prop := True

/-- Compose `Readers.CPUState.circuit` (forms `next_pc = [pc[0]+4, …]`, `clk_inc = 8`), **witness** the
three variant flags `is_xor`/`is_or`/`is_and`, compose the witnessed `BitwiseU16Operation` gadget
(`subcircuit`, fed the SP1 `byte_opcode = is_xor·2 + is_or·1 + is_and·0`), and `Readers.ALUTypeReader.circuit`
(`cpu_opcode = is_xor·3 + is_or·4 + is_and·5`; the `rd` write value is the reassembled result word's four
limbs), gate `is_real`, emit the three flag booleans + their sum-bound + the `op_a_0` zeroing (`AssertSpec`,
SP1's `builder.assert_zero(op_a_0)`), and assemble the extracted `BitwiseCols` struct. The `b_low_bytes`/
`c_low_bytes` column blocks are witnessed (the gadget enforces the decomposition on its own internal
copies; these struct fields are not read by the `Spec`). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var BitwiseCols (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let flags ← witnessVector 3 (fun _ => (#v[0, 0, 0] : Vector (ZMod p) 3))
  let is_xor := flags[0]; let is_or := flags[1]; let is_and := flags[2]
  let bw_op ← subcircuit BitwiseU16Operation.circuit
    ⟨input.op_b_val, input.op_c_val, is_xor * 2 + is_or * 1 + is_and * 0⟩
  let bLow ← witnessVector 4 (fun _ => (#v[0, 0, 0, 0] : Vector (ZMod p) 4))
  let cLow ← witnessVector 4 (fun _ => (#v[0, 0, 0, 0] : Vector (ZMod p) 4))
  let r := bw_op.result
  assertion Readers.ALUTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_xor * 3 + is_or * 4 + is_and * 5,
     r[0] + r[1] * 256, r[2] + r[3] * 256, r[4] + r[5] * 256, r[6] + r[7] * 256⟩
  input.is_real * (input.is_real - 1) === 0
  is_xor * (is_xor - 1) === 0
  is_or * (is_or - 1) === 0
  is_and * (is_and - 1) === 0
  (is_xor + is_or + is_and) * ((is_xor + is_or + is_and) - 1) === 0
  input.adapter.op_a_0 === 0
  return ⟨input.state, input.adapter,
          ⟨fromElements bLow, fromElements cLow, bw_op⟩, is_xor, is_or, is_and⟩

set_option maxHeartbeats 1000000 in
instance elaborated : ElaboratedCircuit (ZMod p) Inputs BitwiseCols main where
  channelsLawful := by
    simp [circuit_norm, main, BitwiseU16Operation.circuit, Readers.ALUTypeReader.circuit,
      Readers.CPUState.circuit]
  -- witnesses the three flags (3) + the `BitwiseU16Operation` block (16) + the `b_low`/`c_low`
  -- column blocks (4 + 4); the two readers are `assertion`s (`localLength 0`) over the threaded
  -- `state`/`adapter` inputs. 3 + 16 + 4 + 4 = 27.
  localLength _ := 27
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

end SP1Clean.BitwiseChip
