import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReader
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Model.Channels
import SP1Clean.Extracted.LoadWordChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `LoadWord` chip row as a `GeneralFormalCircuit`

SP1's `LoadWord` (LW / LWU): `rd ← mem[rs1 + signExtend(imm)]`, 4-byte aligned, the selected 32-bit
half of the read 64-bit word, sign-extended (LW) or zero-extended (LWU) to 64 bits. Composes — as Clean
sub-circuits — the `CPUState` reader (pc+4 / clk+8), the `AddressOperation` gadget (address
`= rs1 + imm` truncated to 48 bits, offset bit 2 = `offset_bit` — LW is 4-byte aligned), the
`MemoryAccess` primitive (a memory **read**: `new_value = prev_value`, at the 8-byte-aligned 48-bit
address), the `U16MSBOperation` gadget (the high bit `msb` of `selected_word[1]`, gated by `is_lw`),
and the `ITypeReader` adapter with the **sign/zero-extended loaded word**
`#v[selected_word[0], selected_word[1], 65535·msb, 65535·msb]` as `op_a`'s write value.

The SP1 memory **bus** access stays 8-byte-aligned: `MemoryAccess` sends/receives the full 4-limb
`prev_value`. The sub-word behaviour is in-circuit: `offset_bit` (bit 2 of the address) selects the
low (`prev_value[0..1]`) or high (`prev_value[2..3]`) 32-bit half into `selected_word`, and `msb`
drives the sign extension. Two selectors `is_lw` / `is_lwu` replace the single `is_real`
(`is_real = is_lw + is_lwu`); LW sign-extends, LWU zero-extends (`msb` zeroed by `(is_lw - 1)·msb`).

The chip `Spec` composes the sub-circuits' `Spec`s + the selection equations + the `op_a != x0` gate +
the selector binaries; the load meaning (`rd =` extended `selected_word`) is carried by `ITypeReader`'s
write value. The cross-row offline-memory meaning lives at the trace level
(`Soundness/MemoryConsistency.lean`). -/

namespace SP1Clean.LoadWordChip

open Circuit
open Extracted (LoadWordColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The threaded reader column blocks + chip-specific witnesses. `state`/`adapter`/`memory_access` are the
committed column blocks; `offset_bit` is bit 2 of the address; `selected_word` the selected 32-bit half;
`msb` the witnessed high bit (via `U16MSBOperation.populate_msb`); `is_lw`/`is_lwu` the signed/unsigned
selectors. The `address_operation` block is the `AddressOperation` sub-circuit's witnessed output, not an
input. The rs1 base-address value (`op_b_val`) and the sign-extended immediate (`op_c_imm`) are **adapter
projections** (`adapter.op_b_memory.prev_value` / `adapter.op_c_imm`), not committed columns — SP1 reads
them from the I-type adapter. -/
structure Inputs (F : Type) where
  is_lw : F
  is_lwu : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : F
  selected_word : fields 2 F
  msb : F
deriving ProvableStruct

/-- rs1 base-address value = the `op_b` register read (`op_b_memory.prev_value`). -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
/-- The sign-extended immediate = the I-type adapter's `op_c_imm`. -/
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm

/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- The row selector `is_lw + is_lwu` (SP1's `is_real`). -/
@[reducible] def isReal (input : Inputs (ZMod p)) : ZMod p := input.is_lw + input.is_lwu

/-- Compose the column blocks as Clean sub-circuits and assemble the extracted `LoadWordColumns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (offset bit 2 =
`offset_bit`); `MemoryAccess` is a read at the 48-bit address; `U16MSBOperation` pins `msb` to the high
bit of `selected_word[1]` (gated by `is_lw`); `ITypeReader` writes the extended word to `op_a` (opcode
`31·is_lw + 34·is_lwu`). The four offset-selection gates, the `op_a != x0` gate, the `(is_lw-1)·msb`
zero-extension gate, and the `is_lw`/`is_lwu`/`is_real` binary gates are imposed directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var LoadWordColumns (ZMod p)) := do
  let is_real := input.is_lw + input.is_lwu
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, is_real⟩
  let addr_op ← subcircuit AddressOperation.circuit ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit⟩
  assertion Readers.MemoryAccess.circuit
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      addr_op.addr_operation.value[0], addr_op.addr_operation.value[1], addr_op.addr_operation.value[2],
      input.memory_access.prev_value, is_real⟩
  assertion U16MSBOperation.circuit ⟨input.selected_word[1], ⟨input.msb⟩, input.is_lw⟩
  assertion Readers.ITypeReader.circuit
    ⟨input.adapter, is_real, is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, input.is_lw * 31 + input.is_lwu * 34,
      input.selected_word[0], input.selected_word[1], 65535 * input.msb, 65535 * input.msb⟩
  -- offset selection: `selected_word` = low half (offset 0) or high half (offset 1) of `prev_value`.
  (input.selected_word[0] - input.memory_access.prev_value[0]) * (input.offset_bit - 1) === 0
  (input.selected_word[1] - input.memory_access.prev_value[1]) * (input.offset_bit - 1) === 0
  (input.selected_word[0] - input.memory_access.prev_value[2]) * input.offset_bit === 0
  (input.selected_word[1] - input.memory_access.prev_value[3]) * input.offset_bit === 0
  input.adapter.op_a_0 === 0
  input.msb * (input.is_lw - 1) === 0
  input.is_lw * (input.is_lw - 1) === 0
  input.is_lwu * (input.is_lwu - 1) === 0
  is_real * (is_real - 1) === 0
  return ⟨input.state, input.adapter, addr_op, input.memory_access, input.offset_bit,
    input.selected_word, ⟨input.msb⟩, input.is_lw, input.is_lwu⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs LoadWordColumns main where
  channelsLawful := by simp [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, U16MSBOperation.circuit]
  -- only the `AddressOperation` subcircuit witnesses (its 65 columns); the other blocks/gates witness nothing.
  localLength _ := 3 + 1
  localLength_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, U16MSBOperation.circuit]
  output input i0 :=
    ⟨input.state, input.adapter,
      ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩,
      input.memory_access, input.offset_bit, input.selected_word, ⟨input.msb⟩,
      input.is_lw, input.is_lwu⟩
  output_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, U16MSBOperation.circuit]
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsWithRequirements :=
    [byteChannel.toRaw, stateChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw]

/-- Semantic contract, composed from the sub-circuits' `Spec`s. The `AddressOperation` address identity +
offset booleans, the `MemoryAccess` timestamp monotonicity, the `U16MSBOperation` high-bit fact, the
`ITypeReader` adapter facts (the extended loaded word), the four offset-selection equations, the
`op_a != x0` flag, the `(is_lw-1)·msb` zero-extension gate, and the `is_lw`/`is_lwu`/`is_real` binaries. -/
def Spec (input : Inputs (ZMod p)) (cols : LoadWordColumns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  AddressOperation.Spec ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit⟩ cols.address_operation ∧
  Readers.MemoryAccess.Spec
    ⟨input.memory_access, input.state.clk_high, clkLow input.state,
      cols.address_operation.addr_operation.value[0], cols.address_operation.addr_operation.value[1],
      cols.address_operation.addr_operation.value[2], input.memory_access.prev_value, isReal input⟩ ∧
  U16MSBOperation.Spec ⟨input.selected_word[1], ⟨input.msb⟩, input.is_lw⟩ ∧
  Readers.ITypeReader.Spec
    ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
      input.state.pc, input.is_lw * 31 + input.is_lwu * 34,
      input.selected_word[0], input.selected_word[1], 65535 * input.msb, 65535 * input.msb⟩ ∧
  ((input.selected_word[0] - input.memory_access.prev_value[0]) * (input.offset_bit - 1) = 0 ∧
    (input.selected_word[1] - input.memory_access.prev_value[1]) * (input.offset_bit - 1) = 0 ∧
    (input.selected_word[0] - input.memory_access.prev_value[2]) * input.offset_bit = 0 ∧
    (input.selected_word[1] - input.memory_access.prev_value[3]) * input.offset_bit = 0) ∧
  input.adapter.op_a_0 = 0 ∧
  input.msb * (input.is_lw - 1) = 0 ∧
  (input.is_lw = 0 ∨ input.is_lw = 1) ∧ (input.is_lwu = 0 ∨ input.is_lwu = 1) ∧
  (isReal input = 0 ∨ isReal input = 1)

end SP1Clean.LoadWordChip
