import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReader
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Model.Channels
import SP1Clean.Extracted.LoadDoubleChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `LoadDouble` chip row as a `GeneralFormalCircuit`

SP1's `LoadDouble` (LD): `rd ← mem[rs1 + signExtend(imm)]`, 8-byte aligned, full 64-bit word, no
sign-extension. Composes — as Clean sub-circuits — the `CPUState` reader (pc+4 / clk+8), the
`AddressOperation` gadget (address `= rs1 + imm` truncated to 48 bits, offset bits `0`), the
`MemoryAccess` primitive (a memory **read**: `new_value = prev_value`, at the computed 48-bit address),
and the `ITypeReader` adapter with the **loaded word** `memory_access.prev_value` as `op_a`'s write value.
Output is the extracted `LoadDoubleColumns` struct.

The chip `Spec` is the composition of the sub-circuits' own `Spec`s + the proven `is_real`-binary fact +
the `op_a != x0` gate; the load *meaning* (`rd = memory_access.prev_value`) is carried by the `ITypeReader`
sub-`Spec` (its write value is the loaded word). The bus's cross-row offline-memory meaning
(`prev_value = actual memory contents at the address`) lives at the trace level
(`Soundness/MemoryConsistency.lean`). -/

namespace SP1Clean.LoadDoubleChip

open Circuit
open Extracted (LoadDoubleColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The operand reads + threaded reader column blocks. `op_b_val` is the rs1 base-address value (the
`op_b` register read), `op_c_imm` the sign-extended immediate; `state`/`adapter`/`memory_access` are the
committed CPUState / I-type-adapter / memory-access columns. The `address_operation` block is the
`AddressOperation` sub-circuit's witnessed output, not an input. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
deriving ProvableStruct

@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm


/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- Compose the four column blocks as Clean sub-circuits and assemble the extracted `LoadDoubleColumns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (offset bits `0` — LD is
8-byte aligned); `MemoryAccess` is a read (`new_value = prev_value`) at the 48-bit address; `ITypeReader`
writes the loaded word `memory_access.prev_value` to `op_a` (opcode `35 = LD`). The `op_a != x0` gate and
the `is_real` binary gate are imposed directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var LoadDoubleColumns (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let addr_op ← subcircuit AddressOperation.circuit ⟨input.op_b_val, input.op_c_imm, 0, 0, 0⟩
  assertion Readers.MemoryAccess.circuit
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      addr_op.addr_operation.value[0], addr_op.addr_operation.value[1], addr_op.addr_operation.value[2],
      input.memory_access.prev_value, input.is_real⟩
  assertion Readers.ITypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, 35,
      input.memory_access.prev_value[0], input.memory_access.prev_value[1],
      input.memory_access.prev_value[2], input.memory_access.prev_value[3]⟩
  input.adapter.op_a_0 === 0
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, addr_op, input.memory_access, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs LoadDoubleColumns main where
  channelsLawful := by simp [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit]
  -- only the `AddressOperation` subcircuit witnesses (its 65 columns); the other blocks are threaded
  -- inputs and the gates witness nothing.
  localLength _ := 3 + 1
  localLength_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit]
  output input i0 :=
    ⟨input.state, input.adapter,
      ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩,
      input.memory_access, input.is_real⟩
  output_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit]
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsWithRequirements :=
    [byteChannel.toRaw, stateChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw]

/-- Semantic contract, composed from the sub-circuits' `Spec`s. The `AddressOperation` address identity,
the `MemoryAccess` timestamp monotonicity, the `ITypeReader` adapter facts (which carry the load meaning —
`op_a`'s write value is `memory_access.prev_value`), the `op_a != x0` flag, and the `is_real`-binary fact. -/
def Spec (input : Inputs (ZMod p)) (cols : LoadDoubleColumns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  AddressOperation.Spec ⟨input.op_b_val, input.op_c_imm, 0, 0, 0⟩ cols.address_operation ∧
  Readers.MemoryAccess.Spec
    ⟨input.memory_access, input.state.clk_high, clkLow input.state,
      cols.address_operation.addr_operation.value[0], cols.address_operation.addr_operation.value[1],
      cols.address_operation.addr_operation.value[2], input.memory_access.prev_value, input.is_real⟩ ∧
  Readers.ITypeReader.Spec
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
      input.state.pc, 35,
      input.memory_access.prev_value[0], input.memory_access.prev_value[1],
      input.memory_access.prev_value[2], input.memory_access.prev_value[3]⟩ ∧
  input.adapter.op_a_0 = 0 ∧
  (input.is_real = 0 ∨ input.is_real = 1)

end SP1Clean.LoadDoubleChip
