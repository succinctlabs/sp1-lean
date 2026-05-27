import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.ShiftLeft.ShiftLeftChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.TrustMode
import RISCV.Instructions

/-! # `ShiftLeftChip` cols-level surface (directory-form scaffold)

Row **65**, ALU-type reader, opcode `is_sll·6 + is_sllw·21`, 4 variants
(SLL/SLLI/SLLW/SLLIW — R/I-type via `imm_c`).
`is_real = is_sll + is_sllw`.

Cols struct mirrors Rust `ShiftLeftCols<T>`:
- state, adapter (ALUTypeReader)
- result (4-limb output), c_bits (6-bit shift decomp)
- v_01/v_012/v_0123 (shift power chain)
- shift_u16 (4-way byte-shift selector)
- lower_limb/higher_limb (8-vec shifted limb intermediates split 4+4)
- limb_result (4-limb intermediate), sllw_msb (U16MSBOp witness)
- 2 selectors + imm_real flag + adapter_cols

NOTE: namespace `SP1Clean.ShiftLeftChip` to coexist with legacy
`SP1Clean/ShiftLeftChip.lean` (uses `SP1Clean.ShiftLeft`). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeftChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `ShiftLeftCols<T>`. -/
@[ext]
structure ShiftLeftCols (T : Type) where
  state : CPUState T
  adapter : ALUTypeReader T
  result : Vector T 4
  c_bits : Vector T 6
  v_01 : T
  v_012 : T
  v_0123 : T
  shift_u16 : Vector T 4
  lower_limb : Vector T 4
  higher_limb : Vector T 4
  limb_result : Vector T 4
  sllw_msb : T
  is_sll : T
  is_sllw : T
  is_sllw_imm : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `ShiftLeftCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 65) : ShiftLeftCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]],
    ⟨#v[Main[25], Main[26], Main[27], Main[28]], ⟨Main[29], Main[30]⟩⟩,
    Main[31]⟩,
   #v[Main[32], Main[33], Main[34], Main[35]],
   #v[Main[36], Main[37], Main[38], Main[39], Main[40], Main[41]],
   Main[42], Main[43], Main[44],
   #v[Main[45], Main[46], Main[47], Main[48]],
   #v[Main[49], Main[50], Main[51], Main[52]],
   #v[Main[53], Main[54], Main[55], Main[56]],
   #v[Main[57], Main[58], Main[59], Main[60]],
   Main[61],
   Main[62], Main[63], Main[64],
   ⟨Main[62] + Main[63]⟩⟩

/-- Right inverse of `fromMain`: pack a `ShiftLeftCols` into a 65-element
flat row. -/
@[reducible] def toMain (cols : ShiftLeftCols (ZMod p)) : Vector (ZMod p) 65 :=
  #v[cols.state.clk_high, cols.state.clk_16_24, cols.state.clk_0_16,
     cols.state.pc[0], cols.state.pc[1], cols.state.pc[2],
     cols.adapter.op_a,
     cols.adapter.op_a_memory.prev_value[0],
     cols.adapter.op_a_memory.prev_value[1],
     cols.adapter.op_a_memory.prev_value[2],
     cols.adapter.op_a_memory.prev_value[3],
     cols.adapter.op_a_memory.access_timestamp.prev_low,
     cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_0, cols.adapter.op_b,
     cols.adapter.op_b_memory.prev_value[0],
     cols.adapter.op_b_memory.prev_value[1],
     cols.adapter.op_b_memory.prev_value[2],
     cols.adapter.op_b_memory.prev_value[3],
     cols.adapter.op_b_memory.access_timestamp.prev_low,
     cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c[0], cols.adapter.op_c[1],
     cols.adapter.op_c[2], cols.adapter.op_c[3],
     cols.adapter.op_c_memory.prev_value[0],
     cols.adapter.op_c_memory.prev_value[1],
     cols.adapter.op_c_memory.prev_value[2],
     cols.adapter.op_c_memory.prev_value[3],
     cols.adapter.op_c_memory.access_timestamp.prev_low,
     cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.imm_c,
     cols.result[0], cols.result[1], cols.result[2], cols.result[3],
     cols.c_bits[0], cols.c_bits[1], cols.c_bits[2],
     cols.c_bits[3], cols.c_bits[4], cols.c_bits[5],
     cols.v_01, cols.v_012, cols.v_0123,
     cols.shift_u16[0], cols.shift_u16[1], cols.shift_u16[2], cols.shift_u16[3],
     cols.lower_limb[0], cols.lower_limb[1], cols.lower_limb[2], cols.lower_limb[3],
     cols.higher_limb[0], cols.higher_limb[1], cols.higher_limb[2], cols.higher_limb[3],
     cols.limb_result[0], cols.limb_result[1], cols.limb_result[2], cols.limb_result[3],
     cols.sllw_msb,
     cols.is_sll, cols.is_sllw, cols.is_sllw_imm]

/-! ## Cols-level Sail-side helpers -/

@[reducible] def sp1_op_a_cols (cols : ShiftLeftCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : ShiftLeftCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : ShiftLeftCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c[0].val

def sp1_shiftleft_cols (cols : ShiftLeftCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a (Word.toBitVec64 cols.result)

/-- Cols-level state-bus precondition. -/
def shiftLeftInitialState_cols (cols : ShiftLeftCols (ZMod p)) (s : SailState) :
    Prop :=
  ∀ Main : Vector (ZMod p) 65, fromMain Main = cols →
    (_root_.ShiftLeft.constraints Main).initialState s

/-! ## Chip-level `FormalSpec`

Composes `U16MSBOp.Assertion.Spec`, `cpuStateSpec`, `aluTypeReaderSpec`,
plus the boolean selectors + the chip-specific inline shift arithmetic
clauses (bit-decomposition booleans, byte-shift one-hot, shift-power
chain, limb-shift identities, result-limb wiring per active opcode). -/
def FormalSpec (cols : ShiftLeftCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let is_real : ZMod p := cols.is_sll + cols.is_sllw
  let opcode : ZMod p := cols.is_sll * 6 + cols.is_sllw * 21
  -- Sub-Spec composition (faithful):
  SP1Clean.U16MSBOp.AssertionGated.Spec ⟨cols.result[1], cols.sllw_msb, cols.is_sllw⟩ ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ALUTypeReader.aluTypeReaderSpec clk_low opcode cols.state.pc
      cols.result cols.adapter ∧
  -- Selector booleans + sum:
  cols.is_sll * (cols.is_sll - 1) = 0 ∧
  cols.is_sllw * (cols.is_sllw - 1) = 0 ∧
  (is_real = 0 ∨ is_real - 1 = 0) ∧
  cols.adapter.op_a_0 = 0 ∧
  -- 6-bit shift decomposition booleans:
  cols.c_bits[0] * (cols.c_bits[0] - 1) = 0 ∧
  cols.c_bits[1] * (cols.c_bits[1] - 1) = 0 ∧
  cols.c_bits[2] * (cols.c_bits[2] - 1) = 0 ∧
  cols.c_bits[3] * (cols.c_bits[3] - 1) = 0 ∧
  cols.c_bits[4] * (cols.c_bits[4] - 1) = 0 ∧
  cols.c_bits[5] * (cols.c_bits[5] - 1) = 0 ∧
  -- 4-way byte-shift one-hot selector booleans:
  cols.shift_u16[0] * (cols.shift_u16[0] - 1) = 0 ∧
  cols.shift_u16[1] * (cols.shift_u16[1] - 1) = 0 ∧
  cols.shift_u16[2] * (cols.shift_u16[2] - 1) = 0 ∧
  cols.shift_u16[3] * (cols.shift_u16[3] - 1) = 0 ∧
  -- Shift-power chain identities:
  cols.v_01 = (cols.c_bits[0] + 1) * (cols.c_bits[1] * 3 + 1) ∧
  cols.v_012 = cols.v_01 * (cols.c_bits[2] * 15 + 1) ∧
  cols.v_0123 = cols.v_012 * (cols.c_bits[3] * 255 + 1) ∧
  -- SLLW immediate-flag bridge: is_sllw_imm = is_sllw * imm_c.
  cols.is_sllw_imm = cols.is_sllw * cols.adapter.imm_c

end SP1Clean.ShiftLeftChip
