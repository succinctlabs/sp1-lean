import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.BitwiseU16Operation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Extracted.BitwiseChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The Bitwise chip row (AND/OR/XOR) as a `GeneralFormalCircuit`, output = the extracted column struct

Composes `CPUState`/`BitwiseU16Operation`/`ALUTypeReader` as Clean subcircuits/assertions (emitting all
four buses), witnesses the three variant flags, threads `byte_opcode` (`is_xor·2 + is_or·1`)
into the gadget and `cpu_opcode` (`is_xor·3 + is_or·4 + is_and·5`) into the reader, gates `is_real`, and
assembles the extracted `BitwiseCols` struct. Operands are projected from the adapter's
`op_b_memory`/`op_c_memory` register reads (not separate columns). Semantic `Spec` in `Formal.lean`. -/

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

/-- The three honest variant flags (`is_xor`, `is_or`, `is_and`) the prover supplies via the
`"bitwise_flags"` hint key (one-hot for the active variant, all-zero on padding). -/
def hintFlags (h : ProverHint (ZMod p)) : Vector (ZMod p) 3 :=
  ((h "bitwise_flags" 3)[0]?).getD #v[0, 0, 0]

/-- Compose `Readers.CPUState.circuit` (forms `next_pc = [pc[0]+4, …]`, `clk_inc = 8`), **witness** the
three variant flags `is_xor`/`is_or`/`is_and` (from the `"bitwise_flags"` `ProverHint`), compose the
witnessed `BitwiseU16Operation` gadget (`subcircuit`, fed the SP1
`byte_opcode = is_xor·2 + is_or·1 + is_and·0`), and `Readers.ALUTypeReader.circuit`
(`cpu_opcode = is_xor·3 + is_or·4 + is_and·5`; the `rd` write value is the reassembled result word's four
limbs), gate `is_real`, emit the three flag booleans + their sum-bound + the `op_a_0` zeroing (`AssertSpec`,
SP1's `builder.assert_zero(op_a_0)`), and assemble the extracted `BitwiseCols` struct. The `b_low_bytes`/
`c_low_bytes` column blocks are witnessed (the gadget enforces the decomposition on its own internal
copies; these struct fields are not read by the `Spec`). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var BitwiseCols (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let flags ← witnessVector 3 (fun env => hintFlags env.hint)
  let is_xor := flags[0]; let is_or := flags[1]; let is_and := flags[2]
  let byteOpcode : Expression (ZMod p) := is_xor * 2 + is_or * 1 + is_and * 0
  -- The chip witnesses the `BitwiseU16Operation` column struct (the two `U16toU8` low-byte blocks +
  -- the eight result bytes) via `populate`, then composes `BitwiseU16Operation.circuit` as a Clean
  -- `assertion` (it is a `FormalAssertion`, witnessing nothing of its own).
  let bw_cols ← ProvableType.witness (fun env =>
    BitwiseU16Operation.populate
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]]
      (env byteOpcode))
  assertion BitwiseU16Operation.circuit
    ⟨input.op_b_val, input.op_c_val, bw_cols, byteOpcode, input.is_real⟩
  let r := bw_cols.bitwise_operation.result
  assertion Readers.ALUTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_xor * 3 + is_or * 4 + is_and * 5,
     r[0] + r[1] * 256, r[2] + r[3] * 256, r[4] + r[5] * 256, r[6] + r[7] * 256⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `BitwiseU16Operation`, so `isU64 (resultWord)` (the reassembled result word, each byte range-checked by
  -- the bitwise byte-bus pulls) discharges its requirement. The written value is the four-limb result word
  -- `#v[r[0]+r[1]*256, …]`; the write access clock is the recombined low clock `+ 4`.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, #v[r[0] + r[1] * 256, r[2] + r[3] * 256, r[4] + r[5] * 256, r[6] + r[7] * 256],
     input.is_real⟩
  -- Inline `assertZero` (not `=== 0`) so the `is_real` booleanity is visible to
  -- `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table (A2).
  assertZero (input.is_real * (input.is_real - 1))
  is_xor * (is_xor - 1) === 0
  is_or * (is_or - 1) === 0
  is_and * (is_and - 1) === 0
  (is_xor + is_or + is_and) * ((is_xor + is_or + is_and) - 1) === 0
  input.adapter.op_a_0 === 0
  return ⟨input.state, input.adapter, bw_cols, is_xor, is_or, is_and⟩

set_option maxHeartbeats 1000000 in
instance elaborated : ElaboratedCircuit (ZMod p) Inputs BitwiseCols main where
  channelsLawful := by
    simp [circuit_norm, main, BitwiseU16Operation.circuit, Readers.ALUTypeReader.circuit,
      Readers.CPUState.circuit, Readers.RegisterWrite.circuit]
  -- witnesses the three flags (3) + the `BitwiseU16Operation` column struct (`b_low_bytes` 4 +
  -- `c_low_bytes` 4 + `bitwise_operation.result` 8 = 16); `BitwiseU16Operation`, the two readers and
  -- `RegisterWrite` are `assertion`s (`localLength 0`). 3 + 16 = 19.
  localLength _ := 19
  -- `programChannel` joins the byte guarantee propagated up from `ALUTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `ALUTypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

end SP1Clean.BitwiseChip
