import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReaderImmutable
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Model.Channels
import SP1Clean.Extracted.LoadX0Chip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `LoadX0` chip row as a `GeneralFormalCircuit`

SP1's `LoadX0` is the fast path for **loads whose destination register is `x0`** (the hardwired-zero
register). One chip bundles all seven load opcodes (`LB, LBU, LH, LHU, LW, LWU, LD`) behind seven
mutually-exclusive selectors. The memory read still happens (for side effects / fault checking), but the
loaded value is **discarded** (`wX 0 _` is a no-op), so the only observable effect is `nextPC = pc + 4`.

Composes — as Clean sub-circuits — the `CPUState` reader (pc+4 / clk+8), the `AddressOperation` gadget
(address `= rs1 + imm` truncated to 48 bits, with the three real offset bits), the `MemoryAccess`
primitive (a memory **read**: `new_value = prev_value`, at the computed 48-bit address), and the
`ITypeReaderImmutable` adapter (op_a a source **read**, no write value — the loaded word is never
written). The opcode fed to the reader is the weighted selector sum
`29·is_lb + 32·is_lbu + 30·is_lh + 33·is_lhu + 31·is_lw + 34·is_lwu + 35·is_ld`.

The chip `Spec` is the composition of the sub-circuits' own `Spec`s + the proven selector binaries / the
`is_real`-binary fact + the three per-width alignment equations + the two `op_a_0` forcing gates (which
pin `op_a_0 = is_real`, i.e. `op_a = x0` on real rows). Output is the extracted `LoadX0Columns`. -/

namespace SP1Clean.LoadX0Chip

open Circuit
open Extracted (LoadX0Columns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The operand reads + threaded reader column blocks. `op_b_val` is the rs1 base-address value (the
`op_b` register read), `op_c_imm` the sign-extended immediate; the seven selectors flag the active load
opcode; `state`/`adapter`/`memory_access` are the committed CPUState / I-type-adapter / memory-access
columns, `offset_bit` the low 3 bits of the address. The `address_operation` block is the
`AddressOperation` sub-circuit's witnessed output, not an input. -/
structure Inputs (F : Type) where
  is_lb : F
  is_lbu : F
  is_lh : F
  is_lhu : F
  is_lw : F
  is_lwu : F
  is_ld : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : fields 3 F
deriving ProvableStruct

@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm


/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- The umbrella `is_real` selector — the sum of the seven mutually-exclusive opcode flags. -/
@[reducible] def isReal (input : Inputs (ZMod p)) : ZMod p :=
  input.is_lb + input.is_lbu + input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld

/-- The weighted opcode value fed to the reader's Program bus. -/
@[reducible] def opcodeVal (input : Inputs (ZMod p)) : ZMod p :=
  29 * input.is_lb + 32 * input.is_lbu + 30 * input.is_lh + 33 * input.is_lhu
    + 31 * input.is_lw + 34 * input.is_lwu + 35 * input.is_ld

/-- Compose the four column blocks as Clean sub-circuits and assemble the extracted `LoadX0Columns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (with the three real
offset bits); `MemoryAccess` is a read (`new_value = prev_value`) at the 48-bit address;
`ITypeReaderImmutable` reads op_a / op_b (opcode the weighted selector sum). The seven selector binaries,
the `is_real` binary, the three per-width alignment gates, and the two `op_a_0` forcing gates are imposed
directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var LoadX0Columns (ZMod p)) := do
  let is_real := input.is_lb + input.is_lbu + input.is_lh + input.is_lhu
    + input.is_lw + input.is_lwu + input.is_ld
  let opcode := 29 * input.is_lb + 32 * input.is_lbu + 30 * input.is_lh + 33 * input.is_lhu
    + 31 * input.is_lw + 34 * input.is_lwu + 35 * input.is_ld
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, is_real⟩
  let addr_op ← subcircuit AddressOperation.circuit
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1], input.offset_bit[2]⟩
  assertion Readers.MemoryAccess.circuit
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      addr_op.addr_operation.value[0], addr_op.addr_operation.value[1], addr_op.addr_operation.value[2],
      input.memory_access.prev_value, is_real⟩
  assertion Readers.ITypeReaderImmutable.circuit
    ⟨input.adapter, is_real, is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, opcode⟩
  input.is_lb * (input.is_lb - 1) === 0
  input.is_lbu * (input.is_lbu - 1) === 0
  input.is_lh * (input.is_lh - 1) === 0
  input.is_lhu * (input.is_lhu - 1) === 0
  input.is_lw * (input.is_lw - 1) === 0
  input.is_lwu * (input.is_lwu - 1) === 0
  input.is_ld * (input.is_ld - 1) === 0
  assertZero (is_real * (is_real - 1))
  input.is_ld * input.offset_bit[2] === 0
  (input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[1] === 0
  (input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[0] === 0
  is_real * (input.adapter.op_a_0 - 1) === 0
  (is_real - 1) * input.adapter.op_a_0 === 0
  return ⟨input.state, input.adapter, addr_op, input.memory_access, input.offset_bit,
    input.is_lb, input.is_lbu, input.is_lh, input.is_lhu, input.is_lw, input.is_lwu, input.is_ld⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs LoadX0Columns main where
  channelsLawful := by simp [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit, Readers.MemoryAccess.circuit]
  -- only the `AddressOperation` subcircuit witnesses (its 65 columns); the other blocks are threaded
  -- inputs and the gates witness nothing.
  localLength _ := 3 + 1
  localLength_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit, Readers.MemoryAccess.circuit]
  output input i0 :=
    ⟨input.state, input.adapter,
      ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩,
      input.memory_access, input.offset_bit,
      input.is_lb, input.is_lbu, input.is_lh, input.is_lhu, input.is_lw, input.is_lwu, input.is_ld⟩
  output_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit, Readers.MemoryAccess.circuit]
  -- `programChannel` joins the byte guarantee propagated up from `ITypeReaderImmutable`'s program **pull**;
  -- `memoryChannel` from `MemoryAccess`'s read-prior **pull** (W11 memory flip).
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- Semantic contract, composed from the sub-circuits' `Spec`s. The `AddressOperation` address identity,
the `MemoryAccess` timestamp monotonicity (a read), the `ITypeReaderImmutable` adapter facts (op_a/op_b
reads + the `op_a_0` read-zeroing — the loaded word is discarded), the seven selector binaries, the
`is_real`-binary fact, the three per-width alignment equations, and the two `op_a_0` forcing gates. -/
def Spec (input : Inputs (ZMod p)) (cols : LoadX0Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  AddressOperation.Spec
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1], input.offset_bit[2]⟩
    cols.address_operation ∧
  Readers.MemoryAccess.Spec
    ⟨input.memory_access, input.state.clk_high, clkLow input.state,
      cols.address_operation.addr_operation.value[0], cols.address_operation.addr_operation.value[1],
      cols.address_operation.addr_operation.value[2], input.memory_access.prev_value, isReal input⟩ ∧
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
      input.state.pc, opcodeVal input⟩ ∧
  (input.is_lb = 0 ∨ input.is_lb = 1) ∧ (input.is_lbu = 0 ∨ input.is_lbu = 1) ∧
  (input.is_lh = 0 ∨ input.is_lh = 1) ∧ (input.is_lhu = 0 ∨ input.is_lhu = 1) ∧
  (input.is_lw = 0 ∨ input.is_lw = 1) ∧ (input.is_lwu = 0 ∨ input.is_lwu = 1) ∧
  (input.is_ld = 0 ∨ input.is_ld = 1) ∧
  (isReal input = 0 ∨ isReal input = 1) ∧
  input.is_ld * input.offset_bit[2] = 0 ∧
  (input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[1] = 0 ∧
  (input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[0] = 0 ∧
  isReal input * (input.adapter.op_a_0 - 1) = 0 ∧
  (isReal input - 1) * input.adapter.op_a_0 = 0

end SP1Clean.LoadX0Chip
