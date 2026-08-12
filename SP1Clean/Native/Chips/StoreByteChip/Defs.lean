import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReaderImmutable
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `StoreByte` chip row as a `GeneralFormalCircuit`

SP1's `StoreByte` (SB): `mem[rs1 + signExtend(imm)] ← rs2[7:0]`, no alignment. The write counterpart of
`LoadByte`. Three offset bits select the target byte: `offset_bit[1..2]` pick the u16 limb (`mem_limb`,
the old value), `offset_bit[0]` the low/high byte within it. The new byte is `rs2`'s low byte
(`register_low_byte`). Both `register_low_byte` and `mem_limb_low_byte` are U8-range-checked (inline
`ByteOpcode.U8Range` pairs splitting `op_a_memory.prev_value[0]` / `mem_limb`). The `increment` is the
signed delta applied to the selected limb (`reg_low - mem_low` for the low byte, `256·(reg_low - mem_high)`
for the high byte), and `store_value` adds it to the `offset_bit[1..2]`-selected limb, leaving the others. -/

namespace SP1Clean.StoreByteChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native StoreByte-chip row (Rust field order). The reader and memory blocks reuse the project
substrate (`Extracted.AddressOperation` is still a standalone generated module — the other loads and
stores compose the same gadget; `Extracted.MemoryAccessCols` lives in the generated `MemoryAccess`
struct carrier). `Faithful.StoreByteChip.storeByteChipReconfigure` is the sole bridge to Rust's
separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  address_operation : Extracted.AddressOperation F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : Vector F 3
  mem_limb : F
  mem_limb_low_byte : F
  register_low_byte : F
  increment : F
  store_value : Word F
  is_real : F
deriving ProvableStruct

structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : fields 3 F
  mem_limb : F
  mem_limb_low_byte : F
  register_low_byte : F
  increment : F
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
         mem_limb := Eval.eval env input.mem_limb
         mem_limb_low_byte := Eval.eval env input.mem_limb_low_byte
         register_low_byte := Eval.eval env input.register_low_byte
         increment := Eval.eval env input.increment
         store_value := Eval.eval env input.store_value } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl


@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- High byte of the register low limb: `(op_a_memory.prev_value[0] - register_low_byte)·256⁻¹`. -/
@[reducible] def regHigh (input : Inputs (ZMod p)) : ZMod p :=
  (input.adapter.op_a_memory.prev_value[0] - input.register_low_byte) * (256 : ZMod p)⁻¹

/-- High byte of the memory limb: `(mem_limb - mem_limb_low_byte)·256⁻¹`. -/
@[reducible] def memHigh (input : Inputs (ZMod p)) : ZMod p :=
  (input.mem_limb - input.mem_limb_low_byte) * (256 : ZMod p)⁻¹

/-- The signed byte delta applied to the selected limb. -/
@[reducible] def incr (input : Inputs (ZMod p)) : ZMod p :=
  (input.register_low_byte - input.mem_limb_low_byte) * (1 - input.offset_bit[0])
    + 256 * (input.register_low_byte - memHigh input) * input.offset_bit[0]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let is_real := input.is_real
  let regHigh := (input.adapter.op_a_memory.prev_value[0] - input.register_low_byte)
    * Expression.const ((256 : ZMod p)⁻¹)
  let memHigh := (input.mem_limb - input.mem_limb_low_byte) * Expression.const ((256 : ZMod p)⁻¹)
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, is_real⟩
  let addr_op ← AddressOperation.circuit
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], is_real⟩
  let address := AddressOperation.alignedValue
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], is_real⟩
    addr_op
  -- `MemoryAccess` and `ITypeReaderImmutable` are now `GeneralFormalCircuit`s (SC Phase 2pre) — composed
  -- via the GFC `CoeFun` (`let _ ←` discards the `unit` output). Their `Spec`s (Contracts) are unchanged.
  let _ ← Readers.MemoryAccess.circuit
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      address[0], address[1], address[2],
      input.store_value, is_real⟩
  let _ ← Readers.ITypeReaderImmutable.circuit
    ⟨input.adapter, is_real, is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 36⟩
  byteChannel.pullIf is_real
    (⟨3, 0, input.register_low_byte, regHigh⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real
    (⟨3, 0, input.mem_limb_low_byte, memHigh⟩ : ByteRow (Expression (ZMod p)))
  -- mem_limb selection: the old value's `offset_bit[1..2]`-selected limb.
  (input.mem_limb - input.memory_access.prev_value[0])
    * (input.offset_bit[1] - 1 : Expression (ZMod p)) * (input.offset_bit[2] - 1) === 0
  (input.mem_limb - input.memory_access.prev_value[1])
    * input.offset_bit[1] * (input.offset_bit[2] - 1) === 0
  (input.mem_limb - input.memory_access.prev_value[2])
    * (input.offset_bit[1] - 1 : Expression (ZMod p)) * input.offset_bit[2] === 0
  (input.mem_limb - input.memory_access.prev_value[3])
    * input.offset_bit[1] * input.offset_bit[2] === 0
  -- increment identity.
  input.increment - ((input.register_low_byte - input.mem_limb_low_byte)
      * ((1 : Expression (ZMod p)) - input.offset_bit[0])
      + Expression.const (256 : ZMod p) * (input.register_low_byte - memHigh)
        * input.offset_bit[0]) === 0
  -- read-modify-write: add `increment` to the selected limb.
  input.store_value[0] - (input.memory_access.prev_value[0]
    + input.increment * ((1 : Expression (ZMod p)) - input.offset_bit[1])
      * ((1 : Expression (ZMod p)) - input.offset_bit[2])) === 0
  input.store_value[1] - (input.memory_access.prev_value[1]
    + input.increment * input.offset_bit[1] * ((1 : Expression (ZMod p)) - input.offset_bit[2])) === 0
  input.store_value[2] - (input.memory_access.prev_value[2]
    + input.increment * ((1 : Expression (ZMod p)) - input.offset_bit[1]) * input.offset_bit[2]) === 0
  input.store_value[3] - (input.memory_access.prev_value[3]
    + input.increment * input.offset_bit[1] * input.offset_bit[2]) === 0
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.state, input.adapter, addr_op, input.memory_access, input.offset_bit,
    input.mem_limb, input.mem_limb_low_byte, input.register_low_byte, input.increment,
    input.store_value, input.is_real⟩

/-- Derive the four address witness cells and the complete four-channel interface from `main`. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main := by
  elaborate_circuit

/-- Folded completed-row layout used by the whole-chip Rust AIR codec. -/
@[circuit_norm] lemma directOutput_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        ⟨varFromOffset Extracted.AddrAddOperation offset, var ⟨offset + 3⟩⟩,
        input.memory_access, input.offset_bit, input.mem_limb,
        input.mem_limb_low_byte, input.register_low_byte, input.increment,
        input.store_value, input.is_real⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of a completed StoreByte row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state
         adapter := Eval.eval env cols.adapter
         address_operation := Eval.eval env cols.address_operation
         memory_access := Eval.eval env cols.memory_access
         offset_bit := Eval.eval env cols.offset_bit
         mem_limb := Eval.eval env cols.mem_limb
         mem_limb_low_byte := Eval.eval env cols.mem_limb_low_byte
         register_low_byte := Eval.eval env cols.register_low_byte
         increment := Eval.eval env cols.increment
         store_value := Eval.eval env cols.store_value
         is_real := Eval.eval env cols.is_real } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Semantic contract. The spine sub-`Spec`s, the (real-row-gated) byte bounds, the mem-limb selection,
the increment identity, the read-modify-write equations, and the `is_real` binary. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  AddressOperation.RowSpec
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], input.is_real⟩
    cols.address_operation ∧
  Readers.MemoryAccess.Spec
    ⟨input.memory_access, input.state.clk_high, clkLow input.state,
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], input.is_real⟩
        cols.address_operation)[0],
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], input.is_real⟩
        cols.address_operation)[1],
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], input.is_real⟩
        cols.address_operation)[2],
      input.store_value, input.is_real⟩ ∧
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
      input.state.pc, 36⟩ ∧
  (input.is_real = 1 → input.register_low_byte.val < 256 ∧ (regHigh input).val < 256
      ∧ input.mem_limb_low_byte.val < 256 ∧ (memHigh input).val < 256) ∧
  ((input.mem_limb - input.memory_access.prev_value[0])
      * (input.offset_bit[1] - 1) * (input.offset_bit[2] - 1) = 0 ∧
    (input.mem_limb - input.memory_access.prev_value[1])
      * input.offset_bit[1] * (input.offset_bit[2] - 1) = 0 ∧
    (input.mem_limb - input.memory_access.prev_value[2])
      * (input.offset_bit[1] - 1) * input.offset_bit[2] = 0 ∧
    (input.mem_limb - input.memory_access.prev_value[3])
      * input.offset_bit[1] * input.offset_bit[2] = 0) ∧
  input.increment = (input.register_low_byte - input.mem_limb_low_byte) * (1 - input.offset_bit[0])
      + 256 * (input.register_low_byte
          - (input.mem_limb - input.mem_limb_low_byte) * (256 : ZMod p)⁻¹) * input.offset_bit[0] ∧
  (input.store_value[0] = input.memory_access.prev_value[0]
      + input.increment * (1 - input.offset_bit[1]) * (1 - input.offset_bit[2]) ∧
    input.store_value[1] = input.memory_access.prev_value[1]
      + input.increment * input.offset_bit[1] * (1 - input.offset_bit[2]) ∧
    input.store_value[2] = input.memory_access.prev_value[2]
      + input.increment * (1 - input.offset_bit[1]) * input.offset_bit[2] ∧
    input.store_value[3] = input.memory_access.prev_value[3]
      + input.increment * input.offset_bit[1] * input.offset_bit[2]) ∧
  (input.is_real = 0 ∨ input.is_real = 1)

end SP1Clean.StoreByteChip
