import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.ShiftLeft.ShiftLeftChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `ShiftLeftChip` cols-level surface (2-variant: `sll`, `sllw`). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeft

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

@[reducible] def sp1_op_a_cols (cols : ShiftLeftCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : ShiftLeftCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : ShiftLeftCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c[0].val

def shiftLeftInitialState_cols (cols : ShiftLeftCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 65, fromMain Main = cols →
    (_root_.ShiftLeft.constraints Main).initialState s

/-- Pack a `ShiftLeftCols` back into the raw 65-column row. Inverse of
`fromMain` modulo the derived `adapter_cols.is_trusted` cell (which is not a
real column — it aliases `is_sll + is_sllw`; see `fromMain_toMain`). -/
@[reducible] def toMain (cols : ShiftLeftCols (ZMod p)) : Vector (ZMod p) 65 :=
  #v[cols.state.clk_high, cols.state.clk_16_24, cols.state.clk_0_16,
     cols.state.pc[0], cols.state.pc[1], cols.state.pc[2],
     cols.adapter.op_a,
     cols.adapter.op_a_memory.prev_value[0], cols.adapter.op_a_memory.prev_value[1],
     cols.adapter.op_a_memory.prev_value[2], cols.adapter.op_a_memory.prev_value[3],
     cols.adapter.op_a_memory.access_timestamp.prev_low,
     cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_0, cols.adapter.op_b,
     cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
     cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3],
     cols.adapter.op_b_memory.access_timestamp.prev_low,
     cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c[0], cols.adapter.op_c[1], cols.adapter.op_c[2], cols.adapter.op_c[3],
     cols.adapter.op_c_memory.prev_value[0], cols.adapter.op_c_memory.prev_value[1],
     cols.adapter.op_c_memory.prev_value[2], cols.adapter.op_c_memory.prev_value[3],
     cols.adapter.op_c_memory.access_timestamp.prev_low,
     cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.imm_c,
     cols.result[0], cols.result[1], cols.result[2], cols.result[3],
     cols.c_bits[0], cols.c_bits[1], cols.c_bits[2], cols.c_bits[3], cols.c_bits[4], cols.c_bits[5],
     cols.v_01, cols.v_012, cols.v_0123,
     cols.shift_u16[0], cols.shift_u16[1], cols.shift_u16[2], cols.shift_u16[3],
     cols.lower_limb[0], cols.lower_limb[1], cols.lower_limb[2], cols.lower_limb[3],
     cols.higher_limb[0], cols.higher_limb[1], cols.higher_limb[2], cols.higher_limb[3],
     cols.limb_result[0], cols.limb_result[1], cols.limb_result[2], cols.limb_result[3],
     cols.sllw_msb.msb,
     cols.is_sll, cols.is_sllw, cols.is_sllw_imm]

/-- Chip-level Sail computation: advances `nextPC` then writes the 4-limb
shifted result to `op_a`. Mirrors `_root_.ShiftLeft.sp1_shift_left`. -/
def sp1_shift_left_cols (cols : ShiftLeftCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a
    (Word.toBitVec64 #v[cols.result[0], cols.result[1], cols.result[2], cols.result[3]])

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 65) :
    sp1_op_a_cols (fromMain Main) = _root_.ShiftLeft.sp1_op_a Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 65) :
    sp1_op_b_cols (fromMain Main) = _root_.ShiftLeft.sp1_op_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 65) :
    sp1_op_c_cols (fromMain Main) = _root_.ShiftLeft.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_shift_left_cols_fromMain (Main : Vector (ZMod p) 65) :
    sp1_shift_left_cols (fromMain Main) = _root_.ShiftLeft.sp1_shift_left Main := rfl

end SP1Clean.ShiftLeft
