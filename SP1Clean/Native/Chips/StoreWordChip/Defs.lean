import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReaderImmutable
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `StoreWord` chip row as a `GeneralFormalCircuit`

SP1's `StoreWord` (SW): `mem[rs1 + signExtend(imm)] ← rs2[31:0]`, 4-byte aligned. The **write**
counterpart of `LoadWord`. Composes — as Clean sub-circuits — the `CPUState` reader (pc+4 / clk+8),
the `AddressOperation` gadget (offset bit 2 = `offset_bit`), the `MemoryAccess` primitive (a memory
**write**: `new_value = store_value`, at the 8-byte-aligned 48-bit address), and the
`ITypeReaderImmutable` adapter (op_a = rs2 read, op_b = rs1 read, opcode `38 = SW`).

Because the memory bus access is 8-byte-aligned, `StoreWord` is a **read-modify-write**: `store_value`
merges the low two limbs of rs2 (`adapter.op_a_memory.prev_value[0..1]`) into the `offset_bit`-selected
half of the read `prev_value`, leaving the other half equal to `prev_value`. The bus receives the merged
8-byte `store_value`. -/

namespace SP1Clean.StoreWordChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native StoreWord-chip row (Rust field order). The reader and memory blocks reuse the project
substrate (`Extracted.AddressOperation` is still a standalone generated module — the other loads and
stores compose the same gadget; `Extracted.MemoryAccessCols` lives in the generated `MemoryAccess`
struct carrier). `Faithful.StoreWordChip.storeWordChipReconfigure` is the sole bridge to Rust's
separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  address_operation : Extracted.AddressOperation F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : F
  store_value : Word F
  is_real : F
deriving ProvableStruct

/-- The operand reads + threaded reader column blocks. `op_b_val` is the rs1 base-address value, `op_c_imm`
the immediate; `state`/`adapter`/`memory_access` are the committed column blocks; `offset_bit` is bit 2 of
the address; `store_value` the read-modify-write word actually written. The stored half is rs2's low two
limbs (`adapter.op_a_memory.prev_value[0..1]`). -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : F
  store_value : (Word F)
deriving ProvableStruct

@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real
         state := Eval.eval env input.state
         adapter := Eval.eval env input.adapter
         memory_access := Eval.eval env input.memory_access
         offset_bit := Eval.eval env input.offset_bit
         store_value := Eval.eval env input.store_value } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl


/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- Compose the column blocks as Clean sub-circuits and assemble the extracted `Columns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (offset bit 2 =
`offset_bit`); `MemoryAccess` is a write (`new_value = store_value`) at the 48-bit address;
`ITypeReaderImmutable` reads op_a (rs2) / op_b (rs1) (opcode `38 = SW`). The four read-modify-write
`store_value` merge gates and the `is_real` binary gate are imposed directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let addr_op ← AddressOperation.circuit
    ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩
  let address := AddressOperation.alignedValue
    ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩ addr_op
  -- `MemoryAccess` and `ITypeReaderImmutable` are now `GeneralFormalCircuit`s (SC Phase 2pre) — composed
  -- via the GFC `CoeFun` (`let _ ←` discards the `unit` output). Their `Spec`s (Contracts) are unchanged.
  let _ ← Readers.MemoryAccess.circuit
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      address[0], address[1], address[2],
      input.store_value, input.is_real⟩
  let _ ← Readers.ITypeReaderImmutable.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, 38⟩
  -- read-modify-write merge: the `offset_bit`-selected half is rs2's low two limbs, the other is `prev_value`.
  (input.store_value[0] - (input.memory_access.prev_value[0]
    + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[0]) * (1 - input.offset_bit))) === 0
  (input.store_value[1] - (input.memory_access.prev_value[1]
    + (input.adapter.op_a_memory.prev_value[1] - input.memory_access.prev_value[1]) * (1 - input.offset_bit))) === 0
  (input.store_value[2] - (input.memory_access.prev_value[2]
    + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[2]) * input.offset_bit)) === 0
  (input.store_value[3] - (input.memory_access.prev_value[3]
    + (input.adapter.op_a_memory.prev_value[1] - input.memory_access.prev_value[3]) * input.offset_bit)) === 0
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.state, input.adapter, addr_op, input.memory_access, input.offset_bit, input.store_value, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  channelsLawful := by simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit, Readers.MemoryAccess.circuit]
  localLength _ := 3 + 1
  output input i0 :=
    ⟨input.state, input.adapter,
      ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩,
      input.memory_access, input.offset_bit, input.store_value, input.is_real⟩
  -- `programChannel` joins the structural `RowSpec` propagated from `ITypeReaderImmutable`'s program **pull** (W11 flip).
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- Folded completed-row layout used by the whole-chip Rust AIR codec. -/
@[circuit_norm] lemma directOutput_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        ⟨varFromOffset Extracted.AddrAddOperation offset, var ⟨offset + 3⟩⟩,
        input.memory_access, input.offset_bit, input.store_value, input.is_real⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of a completed StoreWord row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state
         adapter := Eval.eval env cols.adapter
         address_operation := Eval.eval env cols.address_operation
         memory_access := Eval.eval env cols.memory_access
         offset_bit := Eval.eval env cols.offset_bit
         store_value := Eval.eval env cols.store_value
         is_real := Eval.eval env cols.is_real } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Semantic contract, composed from the sub-circuits' `Spec`s. The `AddressOperation` address identity +
offset booleans, the `MemoryAccess` timestamp monotonicity (whose `new_value` is `store_value`), the
`ITypeReaderImmutable` adapter facts, the four read-modify-write `store_value` equations, and the
`is_real`-binary fact. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  AddressOperation.RowSpec
      ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩
      cols.address_operation ∧
  Readers.MemoryAccess.Spec
    ⟨input.memory_access, input.state.clk_high, clkLow input.state,
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩
        cols.address_operation)[0],
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩
        cols.address_operation)[1],
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩
        cols.address_operation)[2],
      input.store_value, input.is_real⟩ ∧
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
      input.state.pc, 38⟩ ∧
  (input.store_value[0] = input.memory_access.prev_value[0]
      + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[0]) * (1 - input.offset_bit) ∧
    input.store_value[1] = input.memory_access.prev_value[1]
      + (input.adapter.op_a_memory.prev_value[1] - input.memory_access.prev_value[1]) * (1 - input.offset_bit) ∧
    input.store_value[2] = input.memory_access.prev_value[2]
      + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[2]) * input.offset_bit ∧
    input.store_value[3] = input.memory_access.prev_value[3]
      + (input.adapter.op_a_memory.prev_value[1] - input.memory_access.prev_value[3]) * input.offset_bit) ∧
  (input.is_real = 0 ∨ input.is_real = 1)

end SP1Clean.StoreWordChip
