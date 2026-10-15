import SP1Clean.Native.Chips.LoadByteChip.Defs
import Clean.Gadgets.ByteLookup

/-! # LoadByte with two fixed-byte lookups

A separately named alternative to `LoadByteChip.main`. Inputs, output columns and all
arithmetic constraints are unchanged. Only the selected-limb U8Range channel occurrence
is replaced by two lookups in Clean's fixed 256-row `Bytes` table. Multiplying both
lookup inputs by `isReal` preserves the original inactive-row byte freedom.
-/

namespace SP1Clean.LoadByteStaticChip

open Circuit
open LoadByteChip (Inputs Columns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 512) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Original LoadByte arithmetic and readers, with the selected pair checked by fixed lookups. -/
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
  lookup Gadgets.ByteTable (is_real * input.selected_limb_low_byte)
  lookup Gadgets.ByteTable (is_real * high)
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
  channelsLawful := by preserve_tactic_target; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, Readers.RegisterWrite.circuit]
  localLength _ := 3 + 1
  localLength_eq := by preserve_tactic_target; intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, Readers.RegisterWrite.circuit]
  output input i0 :=
    ⟨input.state, input.adapter,
      ⟨⟨varFromOffset (fields 3) i0⟩, var ⟨i0 + 3⟩⟩,
      input.memory_access, input.offset_bit, input.selected_limb, input.selected_limb_low_byte,
      input.selected_byte, input.msb, input.is_lb, input.is_lbu⟩
  output_eq := by preserve_tactic_target; intro input n; simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit, Readers.MemoryAccess.circuit, Readers.RegisterWrite.circuit]
  -- `programChannel` joins the structural `RowSpec` propagated from `ITypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `MemoryAccess`'s read pulls + `RegisterWrite`'s op_a write push (W11 memory flip).
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]


/-- The alternative allocates exactly the same cells and returns the original row layout. -/
theorem output_eq_original (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (LoadByteChip.elaborated (p := p)).output input offset := rfl

end SP1Clean.LoadByteStaticChip
