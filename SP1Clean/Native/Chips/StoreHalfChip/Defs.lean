import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReaderImmutable
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Model.Channels
import SP1Clean.Extracted.StoreHalfChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `StoreHalf` chip row as a `GeneralFormalCircuit`

SP1's `StoreHalf` (SH): `mem[rs1 + signExtend(imm)] ← rs2[15:0]`, 2-byte aligned. The **write**
counterpart of `LoadHalf`, and the sub-word analogue of `StoreWord`. Composes — as Clean sub-circuits —
the `CPUState` reader (pc+4 / clk+8), the `AddressOperation` gadget (offset bits 1–2 = `offset_bit[0..1]`),
the `MemoryAccess` primitive (a memory **write**: `new_value = store_value`, at the 8-byte-aligned 48-bit
address), and the `ITypeReaderImmutable` adapter (opcode `37 = SH`).

Because the memory bus access is 8-byte-aligned, `StoreHalf` is a **read-modify-write**: `store_value`
merges the low limb of rs2 (`adapter.op_a_memory.prev_value[0]`) into the `offset_bit`-selected limb of
the read `prev_value`, leaving the other three limbs equal to `prev_value`. The two offset bits select
which of the four 16-bit limbs is overwritten. -/

namespace SP1Clean.StoreHalfChip

open Circuit
open Extracted (StoreHalfColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The operand reads + threaded reader column blocks. `op_b_val` is the rs1 base-address value, `op_c_imm`
the immediate; `state`/`adapter`/`memory_access` are the committed column blocks; `offset_bit` are bits 1–2
of the address; `store_value` the read-modify-write word actually written. The stored limb is rs2's low
limb (`adapter.op_a_memory.prev_value[0]`). -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : fields 2 F
  store_value : (Word F)
deriving ProvableStruct

@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm


/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- Compose the column blocks as Clean sub-circuits and assemble the extracted `StoreHalfColumns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (offset bits 1–2 =
`offset_bit[0..1]`, bit 0 = 0 since SH is 2-byte aligned); `MemoryAccess` is a write
(`new_value = store_value`) at the 48-bit address; `ITypeReaderImmutable` reads op_a (rs2) / op_b (rs1)
(opcode `37 = SH`). The four read-modify-write `store_value` merge gates (2-bit-product coefficients) and
the `is_real` binary gate are imposed directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var StoreHalfColumns (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let addr_op ← subcircuit AddressOperation.circuit
    ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1]⟩
  assertion Readers.MemoryAccess.circuit
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      addr_op.addr_operation.value[0], addr_op.addr_operation.value[1], addr_op.addr_operation.value[2],
      input.store_value, input.is_real⟩
  assertion Readers.ITypeReaderImmutable.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, 37⟩
  -- read-modify-write merge: the 2-bit-selected limb is rs2's low limb, the other three stay `prev_value`.
  (input.store_value[0] - (input.memory_access.prev_value[0]
    + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[0])
      * ((1 : Expression (ZMod p)) - input.offset_bit[0]) * ((1 : Expression (ZMod p)) - input.offset_bit[1]))) === 0
  (input.store_value[1] - (input.memory_access.prev_value[1]
    + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[1])
      * input.offset_bit[0] * ((1 : Expression (ZMod p)) - input.offset_bit[1]))) === 0
  (input.store_value[2] - (input.memory_access.prev_value[2]
    + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[2])
      * ((1 : Expression (ZMod p)) - input.offset_bit[0]) * input.offset_bit[1])) === 0
  (input.store_value[3] - (input.memory_access.prev_value[3]
    + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[3])
      * input.offset_bit[0] * input.offset_bit[1])) === 0
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, addr_op, input.memory_access, input.offset_bit,
    input.store_value, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs StoreHalfColumns main where
  channelsLawful := by simp [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit, Readers.MemoryAccess.circuit]
  localLength _ := 3 + 1
  localLength_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit, Readers.MemoryAccess.circuit]
  output input i0 :=
    ⟨input.state, input.adapter,
      ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩,
      input.memory_access, input.offset_bit, input.store_value, input.is_real⟩
  output_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit, Readers.MemoryAccess.circuit]
  -- `programChannel` joins the byte guarantee propagated up from `ITypeReaderImmutable`'s program **pull** (W11 flip).
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw]

/-- Semantic contract, composed from the sub-circuits' `Spec`s plus the four read-modify-write
`store_value` equations and the `is_real`-binary fact. -/
def Spec (input : Inputs (ZMod p)) (cols : StoreHalfColumns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  AddressOperation.Spec ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1]⟩
    cols.address_operation ∧
  Readers.MemoryAccess.Spec
    ⟨input.memory_access, input.state.clk_high, clkLow input.state,
      cols.address_operation.addr_operation.value[0], cols.address_operation.addr_operation.value[1],
      cols.address_operation.addr_operation.value[2], input.store_value, input.is_real⟩ ∧
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
      input.state.pc, 37⟩ ∧
  (input.store_value[0] = input.memory_access.prev_value[0]
      + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[0])
        * (1 - input.offset_bit[0]) * (1 - input.offset_bit[1]) ∧
    input.store_value[1] = input.memory_access.prev_value[1]
      + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[1])
        * input.offset_bit[0] * (1 - input.offset_bit[1]) ∧
    input.store_value[2] = input.memory_access.prev_value[2]
      + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[2])
        * (1 - input.offset_bit[0]) * input.offset_bit[1] ∧
    input.store_value[3] = input.memory_access.prev_value[3]
      + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[3])
        * input.offset_bit[0] * input.offset_bit[1]) ∧
  (input.is_real = 0 ∨ input.is_real = 1)

end SP1Clean.StoreHalfChip
