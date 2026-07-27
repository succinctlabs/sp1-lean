import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReader
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `LoadByte` chip row as a `GeneralFormalCircuit`

SP1's `LoadByte` (LB / LBU): `rd ← mem[rs1 + signExtend(imm)]`, no alignment, the selected 8-bit byte of
the read 64-bit word, sign-extended (LB) or zero-extended (LBU) to 64 bits. Three offset bits select 1 of
8 bytes: `offset_bit[1..2]` pick the u16 limb (`selected_limb`), `offset_bit[0]` picks the low/high byte
within it. The byte is sub-limb-decomposed (`selected_limb = selected_limb_low_byte + 256·high`, both
U8-range-checked via an inline `ByteOpcode.U8Range` pair) and its sign bit `msb` is pinned by an inline
`ByteOpcode.MSB` byte-bus pull (gated by `is_lb`). The loaded word is
`#v[selected_byte + 65280·msb, 65535·msb, 65535·msb, 65535·msb]` (the byte sign-extends *within* limb 0).

Unlike `LoadWord`/`LoadHalf` (which compose `U16MSBOperation` as a sub-gadget), SP1 inlines the byte-bus
lookups, so this chip emits them directly via `byteChannel.pullIf` (witnessing nothing). -/

namespace SP1Clean.LoadByteChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native LoadByte-chip row (Rust field order). The reader and memory blocks reuse the project
substrate (`Extracted.AddressOperation` is still a standalone generated module — the other loads and
stores compose the same gadget; `Extracted.MemoryAccessCols` lives in the generated `MemoryAccess`
struct carrier). `Faithful.LoadByteChip.loadByteChipReconfigure` is the sole bridge to Rust's
separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  address_operation : Extracted.AddressOperation F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : Vector F 3
  selected_limb : F
  selected_limb_low_byte : F
  selected_byte : F
  msb : F
  is_lb : F
  is_lbu : F
deriving ProvableStruct

structure Inputs (F : Type) where
  is_lb : F
  is_lbu : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : fields 3 F
  selected_limb : F
  selected_limb_low_byte : F
  selected_byte : F
  msb : F
deriving ProvableStruct

@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_lb := Eval.eval env input.is_lb
         is_lbu := Eval.eval env input.is_lbu
         state := Eval.eval env input.state
         adapter := Eval.eval env input.adapter
         memory_access := Eval.eval env input.memory_access
         offset_bit := Eval.eval env input.offset_bit
         selected_limb := Eval.eval env input.selected_limb
         selected_limb_low_byte := Eval.eval env input.selected_limb_low_byte
         selected_byte := Eval.eval env input.selected_byte
         msb := Eval.eval env input.msb } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl


@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

@[reducible] def isReal (input : Inputs (ZMod p)) : ZMod p := input.is_lb + input.is_lbu

/-- The sub-limb high byte `(selected_limb - selected_limb_low_byte)·256⁻¹` (over the field). -/
@[reducible] def highByte (input : Inputs (ZMod p)) : ZMod p :=
  (input.selected_limb - input.selected_limb_low_byte) * (256 : ZMod p)⁻¹

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let is_real := input.is_lb + input.is_lbu
  let high := (input.selected_limb - input.selected_limb_low_byte)
    * Expression.const ((256 : ZMod p)⁻¹)
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, is_real⟩
  let addr_op ← AddressOperation.circuit
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], is_real⟩
  let address := AddressOperation.alignedValue
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], is_real⟩
    addr_op
  -- SC Phase 2pre: `MemoryAccess` is now a `GeneralFormalCircuit`, composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.MemoryAccess.circuit
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      address[0], address[1], address[2],
      input.memory_access.prev_value, is_real⟩
  byteChannel.pullIf is_real
    (⟨3, 0, input.selected_limb_low_byte, high⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_lb
    (⟨5, input.msb, input.selected_byte, 0⟩ : ByteRow (Expression (ZMod p)))
  -- SC Phase 2pre: `ITypeReader` is now a `GeneralFormalCircuit`, composed via the GFC `CoeFun`.
  let _ ← Readers.ITypeReader.circuit
    ⟨input.adapter, is_real, is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, input.is_lb * 29 + input.is_lbu * 32,
      input.selected_byte + 65280 * input.msb, 65535 * input.msb, 65535 * input.msb, 65535 * input.msb⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- the memory read + byte selection, so `isU64 <loaded word>` discharges its requirement. The loaded word is
  -- the sign/zero-extended byte (the same tuple threaded to `ITypeReader` as `wv0..wv3`).
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a,
     #v[input.selected_byte + 65280 * input.msb, 65535 * input.msb, 65535 * input.msb,
        65535 * input.msb], is_real⟩
  (input.selected_limb - input.memory_access.prev_value[0])
    * (input.offset_bit[1] - 1 : Expression (ZMod p)) * (input.offset_bit[2] - 1) === 0
  (input.selected_limb - input.memory_access.prev_value[1])
    * input.offset_bit[1] * (input.offset_bit[2] - 1) === 0
  (input.selected_limb - input.memory_access.prev_value[2])
    * (input.offset_bit[1] - 1 : Expression (ZMod p)) * input.offset_bit[2] === 0
  (input.selected_limb - input.memory_access.prev_value[3])
    * input.offset_bit[1] * input.offset_bit[2] === 0
  input.selected_byte - (input.offset_bit[0] * high
    + ((1 : Expression (ZMod p)) - input.offset_bit[0]) * input.selected_limb_low_byte) === 0
  input.adapter.op_a_0 === 0
  input.is_lbu * input.msb === 0
  -- shallow (`assertZero`, W11 Phase 0c): the second byte pull is gated by `is_lb`, so its off-gate
  -- `Requirements` needs `is_lb ∈ {0,1}` visible to `ConstraintsHold.Shallow`.
  assertZero (input.is_lb * (input.is_lb - 1))
  input.is_lbu * (input.is_lbu - 1) === 0
  assertZero (is_real * (is_real - 1))
  return ⟨input.state, input.adapter, addr_op, input.memory_access, input.offset_bit,
    input.selected_limb, input.selected_limb_low_byte, input.selected_byte, input.msb,
    input.is_lb, input.is_lbu⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  channelsLawful := by simp [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, Readers.RegisterWrite.circuit]
  localLength _ := 3 + 1
  localLength_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, Readers.RegisterWrite.circuit]
  output input i0 :=
    ⟨input.state, input.adapter,
      ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩,
      input.memory_access, input.offset_bit, input.selected_limb, input.selected_limb_low_byte,
      input.selected_byte, input.msb, input.is_lb, input.is_lbu⟩
  output_eq := by intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, Readers.RegisterWrite.circuit]
  -- `programChannel` joins the byte guarantee propagated up from `ITypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `MemoryAccess`'s read pulls + `RegisterWrite`'s op_a write push (W11 memory flip).
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- Folded completed-row layout used by the whole-chip Rust AIR codec. -/
@[circuit_norm] lemma directOutput_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        ⟨varFromOffset Extracted.AddrAddOperation offset, var ⟨offset + 3⟩⟩,
        input.memory_access, input.offset_bit, input.selected_limb,
        input.selected_limb_low_byte, input.selected_byte, input.msb,
        input.is_lb, input.is_lbu⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of a completed LoadByte row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state
         adapter := Eval.eval env cols.adapter
         address_operation := Eval.eval env cols.address_operation
         memory_access := Eval.eval env cols.memory_access
         offset_bit := Eval.eval env cols.offset_bit
         selected_limb := Eval.eval env cols.selected_limb
         selected_limb_low_byte := Eval.eval env cols.selected_limb_low_byte
         selected_byte := Eval.eval env cols.selected_byte
         msb := Eval.eval env cols.msb
         is_lb := Eval.eval env cols.is_lb
         is_lbu := Eval.eval env cols.is_lbu } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Semantic contract. The spine sub-`Spec`s, the (real-row-gated) byte bounds, the (LB-gated) sign-bit
fact, the four limb-selection equations, the byte-mux equation, the `op_a != x0` flag, the `is_lbu·msb`
zero-extension gate, and the selector binaries. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  AddressOperation.RowSpec
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], isReal input⟩
    cols.address_operation ∧
  Readers.MemoryAccess.Spec
    ⟨input.memory_access, input.state.clk_high, clkLow input.state,
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], isReal input⟩
        cols.address_operation)[0],
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], isReal input⟩
        cols.address_operation)[1],
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], isReal input⟩
        cols.address_operation)[2],
      input.memory_access.prev_value, isReal input⟩ ∧
  Readers.ITypeReader.Spec
    ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
      input.state.pc, input.is_lb * 29 + input.is_lbu * 32,
      input.selected_byte + 65280 * input.msb, 65535 * input.msb, 65535 * input.msb, 65535 * input.msb⟩ ∧
  (isReal input = 1 → input.selected_limb_low_byte.val < 256 ∧ (highByte input).val < 256
      ∧ input.selected_byte.val < 256) ∧
  (input.is_lb = 1 → (input.msb = 0 ∨ input.msb = 1) ∧ (input.msb = 1 ↔ 128 ≤ input.selected_byte.val)) ∧
  ((input.selected_limb - input.memory_access.prev_value[0])
      * (input.offset_bit[1] - 1) * (input.offset_bit[2] - 1) = 0 ∧
    (input.selected_limb - input.memory_access.prev_value[1])
      * input.offset_bit[1] * (input.offset_bit[2] - 1) = 0 ∧
    (input.selected_limb - input.memory_access.prev_value[2])
      * (input.offset_bit[1] - 1) * input.offset_bit[2] = 0 ∧
    (input.selected_limb - input.memory_access.prev_value[3])
      * input.offset_bit[1] * input.offset_bit[2] = 0) ∧
  input.selected_byte = input.offset_bit[0] * highByte input
      + (1 - input.offset_bit[0]) * input.selected_limb_low_byte ∧
  input.adapter.op_a_0 = 0 ∧
  input.is_lbu * input.msb = 0 ∧
  (input.is_lb = 0 ∨ input.is_lb = 1) ∧ (input.is_lbu = 0 ∨ input.is_lbu = 1) ∧
  (isReal input = 0 ∨ isReal input = 1)

end SP1Clean.LoadByteChip
