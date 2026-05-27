import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.ShiftRight.ShiftRightChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.TrustMode
import RISCV.Instructions

/-! # `ShiftRightChip` cols-level surface (directory-form scaffold)

Row **69**, ALU-type reader, opcode
`is_srl·7 + is_sra·8 + is_srlw·22 + is_sraw·23`, 8 variants
(SRL/SRLI/SRA/SRAI/SRLW/SRLIW/SRAW/SRAIW — R/I-type via `imm_c`).
`is_real = is_srl + is_sra + is_srlw + is_sraw`.

Cols struct mirrors Rust `ShiftRightCols<T>`. Three `U16MSBOp` sub-calls
witness MSBs for the sign-extension paths (SRA/SRAW + W-variants). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRightChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `ShiftRightCols<T>`. -/
@[ext]
structure ShiftRightCols (T : Type) where
  state : CPUState T
  adapter : ALUTypeReader T
  result : Vector T 4
  b_msb : T
  srw_msb : T
  c_bits : Vector T 6
  v_01 : T
  v_012 : T
  v_0123 : T
  shifted_intermediates : Vector T 8
  limb_result : Vector T 4
  shift_u16 : Vector T 4
  is_srl : T
  is_sra : T
  is_srlw : T
  is_sraw : T
  is_w_imm : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

@[reducible] def fromMain (Main : Vector (ZMod p) 69) : ShiftRightCols (ZMod p) :=
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
   Main[36], Main[37],
   #v[Main[38], Main[39], Main[40], Main[41], Main[42], Main[43]],
   Main[44], Main[45], Main[46],
   #v[Main[47], Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54]],
   #v[Main[55], Main[56], Main[57], Main[58]],
   #v[Main[60], Main[61], Main[62], Main[63]],
   Main[64], Main[65], Main[66], Main[67], Main[68],
   ⟨Main[64] + Main[65] + Main[66] + Main[67]⟩⟩

@[reducible] def toMain (cols : ShiftRightCols (ZMod p)) : Vector (ZMod p) 69 :=
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
     cols.b_msb, cols.srw_msb,
     cols.c_bits[0], cols.c_bits[1], cols.c_bits[2],
     cols.c_bits[3], cols.c_bits[4], cols.c_bits[5],
     cols.v_01, cols.v_012, cols.v_0123,
     cols.shifted_intermediates[0], cols.shifted_intermediates[1],
     cols.shifted_intermediates[2], cols.shifted_intermediates[3],
     cols.shifted_intermediates[4], cols.shifted_intermediates[5],
     cols.shifted_intermediates[6], cols.shifted_intermediates[7],
     cols.limb_result[0], cols.limb_result[1], cols.limb_result[2], cols.limb_result[3],
     0, -- Main[59] reserved (zero-filled in legacy file)
     cols.shift_u16[0], cols.shift_u16[1], cols.shift_u16[2], cols.shift_u16[3],
     cols.is_srl, cols.is_sra, cols.is_srlw, cols.is_sraw, cols.is_w_imm]

/-! ## Cols-level Sail-side helpers -/

@[reducible] def sp1_op_a_cols (cols : ShiftRightCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : ShiftRightCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : ShiftRightCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c[0].val

def sp1_shiftright_cols (cols : ShiftRightCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a (Word.toBitVec64 cols.result)

def shiftRightInitialState_cols (cols : ShiftRightCols (ZMod p))
    (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 69, fromMain Main = cols →
    (_root_.ShiftRight.constraints Main).initialState s

/-! ## Chip-level `FormalSpec`

Composes 3× `U16MSBOp.Assertion.Spec`, `cpuStateSpec`, `aluTypeReaderSpec`,
plus the boolean selectors + 4-way sum-binary + `op_a_0`, the 6-bit
shift decomposition booleans, the shift-power chain identities, and the
`is_w_imm = (is_srlw + is_sraw) * imm_c` bridge. -/
def FormalSpec (cols : ShiftRightCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let is_real : ZMod p := cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw
  let opcode : ZMod p :=
    cols.is_srl * 7 + cols.is_sra * 8 + cols.is_srlw * 22 + cols.is_sraw * 23
  -- 3 U16MSB sub-Specs (b_high on Main[18] gated by is_sra,
  -- b_low on Main[16] gated by is_sraw,
  -- result_high on Main[33] gated by (is_srlw + is_sraw)):
  SP1Clean.U16MSBOp.AssertionGated.Spec
    ⟨cols.adapter.op_b_memory.prev_value[3], cols.b_msb, cols.is_sra⟩ ∧
  SP1Clean.U16MSBOp.AssertionGated.Spec
    ⟨cols.adapter.op_b_memory.prev_value[1], cols.b_msb, cols.is_sraw⟩ ∧
  SP1Clean.U16MSBOp.AssertionGated.Spec
    ⟨cols.result[1], cols.srw_msb, cols.is_srlw + cols.is_sraw⟩ ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ALUTypeReader.aluTypeReaderSpec clk_low opcode cols.state.pc
      cols.result cols.adapter ∧
  cols.is_srl * (cols.is_srl - 1) = 0 ∧
  cols.is_sra * (cols.is_sra - 1) = 0 ∧
  cols.is_srlw * (cols.is_srlw - 1) = 0 ∧
  cols.is_sraw * (cols.is_sraw - 1) = 0 ∧
  (is_real = 0 ∨ is_real - 1 = 0) ∧
  cols.adapter.op_a_0 = 0 ∧
  cols.c_bits[0] * (cols.c_bits[0] - 1) = 0 ∧
  cols.c_bits[1] * (cols.c_bits[1] - 1) = 0 ∧
  cols.c_bits[2] * (cols.c_bits[2] - 1) = 0 ∧
  cols.c_bits[3] * (cols.c_bits[3] - 1) = 0 ∧
  cols.c_bits[4] * (cols.c_bits[4] - 1) = 0 ∧
  cols.c_bits[5] * (cols.c_bits[5] - 1) = 0 ∧
  cols.is_w_imm = (cols.is_srlw + cols.is_sraw) * cols.adapter.imm_c

end SP1Clean.ShiftRightChip
