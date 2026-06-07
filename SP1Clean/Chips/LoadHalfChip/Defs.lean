import SP1Clean.Specs.Chip
import SP1Clean.Operations.AddressOperation
import SP1Clean.Operations.U16MSBOperation.Formal
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.ITypeReader
import SP1Clean.Readers.MemoryAccess
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.LoadHalfChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `LoadHalf` chip row as a `GeneralFormalCircuit`

SP1's `LoadHalf` (LH / LHU): `rd ← mem[rs1 + signExtend(imm)]`, 2-byte aligned, the selected 16-bit
limb of the read 64-bit word, sign-extended (LH) or zero-extended (LHU) to 64 bits. The direct sub-word
analogue of `LoadWord`: two offset bits `offset_bit[0..1]` (bits 1–2 of the address) select 1 of the 4
u16 limbs of `prev_value` into the single 16-bit `selected_half`; the `U16MSBOperation` gadget pins the
high bit `msb` of `selected_half` (gated by `is_lh`) to drive the sign extension. The loaded word is
`#v[selected_half, 65535·msb, 65535·msb, 65535·msb]`.

The SP1 memory **bus** access stays 8-byte-aligned: `MemoryAccess` sends/receives the full 4-limb
`prev_value`. Two selectors `is_lh` / `is_lhu` replace the single `is_real` (`is_real = is_lh + is_lhu`);
LH sign-extends, LHU zero-extends (`msb` zeroed by `is_lhu·msb`). The cross-row offline-memory meaning
lives at the trace level (`Soundness/MemoryConsistency.lean`). -/

namespace SP1Clean.LoadHalfChip

open Circuit
open Extracted (LoadHalfColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The operand reads + threaded reader column blocks. `op_b_val` is the rs1 base-address value, `op_c_imm`
the sign-extended immediate; `state`/`adapter`/`memory_access` are the committed column blocks; `offset_bit`
are bits 1–2 of the address; `selected_half` the selected 16-bit limb; `msb` the witnessed high bit (via
`U16MSBOperation.populate_msb`); `is_lh`/`is_lhu` the signed/unsigned selectors. -/
structure Inputs (F : Type) where
  op_b_val : fields 4 F
  op_c_imm : fields 4 F
  is_lh : F
  is_lhu : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : fields 2 F
  selected_half : F
  msb : F
deriving ProvableStruct

/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- The row selector `is_lh + is_lhu` (SP1's `is_real`). -/
@[reducible] def isReal (input : Inputs (ZMod p)) : ZMod p := input.is_lh + input.is_lhu

/-- Compose the column blocks as Clean sub-circuits and assemble the extracted `LoadHalfColumns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (offset bits 1–2 =
`offset_bit[0..1]`, bit 0 = 0 since LH is 2-byte aligned); `MemoryAccess` is a read at the 48-bit
address; `U16MSBOperation` pins `msb` to the high bit of `selected_half` (gated by `is_lh`); `ITypeReader`
writes the extended word to `op_a` (opcode `30·is_lh + 33·is_lhu`). The four 2-bit offset-selection gates,
the `op_a != x0` gate, the `is_lhu·msb` zero-extension gate, and the binary gates are imposed directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var LoadHalfColumns (ZMod p)) := do
  let is_real := input.is_lh + input.is_lhu
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, is_real⟩
  let addr_op ← subcircuit AddressOperation.circuit
    ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1]⟩
  assertion Readers.MemoryAccess.circuit
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      addr_op.addr_operation.value[0], addr_op.addr_operation.value[1], addr_op.addr_operation.value[2],
      input.memory_access.prev_value, is_real⟩
  assertion U16MSBOperation.circuit ⟨input.selected_half, ⟨input.msb⟩, input.is_lh⟩
  assertion Readers.ITypeReader.circuit
    ⟨input.adapter, is_real, is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, input.is_lh * 30 + input.is_lhu * 33,
      input.selected_half, 65535 * input.msb, 65535 * input.msb, 65535 * input.msb⟩
  -- offset selection: `selected_half` = the 2-bit-selected limb of `prev_value`.
  (input.selected_half - input.memory_access.prev_value[0])
    * (input.offset_bit[0] - 1 : Expression (ZMod p)) * (input.offset_bit[1] - 1) === 0
  (input.selected_half - input.memory_access.prev_value[1])
    * input.offset_bit[0] * (input.offset_bit[1] - 1) === 0
  (input.selected_half - input.memory_access.prev_value[2])
    * (input.offset_bit[0] - 1 : Expression (ZMod p)) * input.offset_bit[1] === 0
  (input.selected_half - input.memory_access.prev_value[3])
    * input.offset_bit[0] * input.offset_bit[1] === 0
  input.adapter.op_a_0 === 0
  input.is_lhu * input.msb === 0
  input.is_lh * (input.is_lh - 1) === 0
  input.is_lhu * (input.is_lhu - 1) === 0
  is_real * (is_real - 1) === 0
  return ⟨input.state, input.adapter, addr_op, input.memory_access, input.offset_bit,
    input.selected_half, ⟨input.msb⟩, input.is_lh, input.is_lhu⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs LoadHalfColumns main where
  channelsLawful := by simp [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, U16MSBOperation.circuit]
  -- only the `AddressOperation` subcircuit witnesses (its 65 columns); the other blocks/gates witness nothing.
  localLength _ := 3 + 1 + 13
  localLength_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, U16MSBOperation.circuit]
  output input i0 :=
    ⟨input.state, input.adapter,
      ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩,
      input.memory_access, input.offset_bit, input.selected_half, ⟨input.msb⟩,
      input.is_lh, input.is_lhu⟩
  output_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, U16MSBOperation.circuit]
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

/-- Semantic contract, composed from the sub-circuits' `Spec`s plus the four offset-selection equations,
the `op_a != x0` flag, the `is_lhu·msb` zero-extension gate, and the `is_lh`/`is_lhu`/`is_real` binaries. -/
def Spec (input : Inputs (ZMod p)) (cols : LoadHalfColumns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  AddressOperation.Spec ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1]⟩
    cols.address_operation ∧
  Readers.MemoryAccess.Spec
    ⟨input.memory_access, input.state.clk_high, clkLow input.state,
      cols.address_operation.addr_operation.value[0], cols.address_operation.addr_operation.value[1],
      cols.address_operation.addr_operation.value[2], input.memory_access.prev_value, isReal input⟩ ∧
  U16MSBOperation.Spec ⟨input.selected_half, ⟨input.msb⟩, input.is_lh⟩ ∧
  Readers.ITypeReader.Spec
    ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
      input.state.pc, input.is_lh * 30 + input.is_lhu * 33,
      input.selected_half, 65535 * input.msb, 65535 * input.msb, 65535 * input.msb⟩ ∧
  ((input.selected_half - input.memory_access.prev_value[0])
      * (input.offset_bit[0] - 1) * (input.offset_bit[1] - 1) = 0 ∧
    (input.selected_half - input.memory_access.prev_value[1])
      * input.offset_bit[0] * (input.offset_bit[1] - 1) = 0 ∧
    (input.selected_half - input.memory_access.prev_value[2])
      * (input.offset_bit[0] - 1) * input.offset_bit[1] = 0 ∧
    (input.selected_half - input.memory_access.prev_value[3])
      * input.offset_bit[0] * input.offset_bit[1] = 0) ∧
  input.adapter.op_a_0 = 0 ∧
  input.is_lhu * input.msb = 0 ∧
  (input.is_lh = 0 ∨ input.is_lh = 1) ∧ (input.is_lhu = 0 ∨ input.is_lhu = 1) ∧
  (isReal input = 0 ∨ isReal input = 1)

end SP1Clean.LoadHalfChip
