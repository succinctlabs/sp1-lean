import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Operations.Operation.BitwiseU16Operation.BitwiseU16Operation
import SP1Chips.Bitwise.BitwiseChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.BitwiseOperation
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `BitwiseChip` cols-level surface

Mirrors `SP1Clean/Chips/ALU/AddChip/Cols.lean` for the 3-variant
(`xor`/`or`/`and`, R-type only in the Path-2 `FormalSpec`) bitwise
chip. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Bitwise

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

@[reducible] def sp1_op_a_cols (cols : BitwiseCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : BitwiseCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : BitwiseCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c[0].val

/-- Chip-level Sail computation. Mirrors `_root_.Bitwise.sp1_bitwise`. -/
def sp1_bitwise_cols (cols : BitwiseCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  let bres := cols.bitwise_operation.bitwise_operation.result
  let op_a_write_value : Word (ZMod p) :=
    #v[bres[0] + bres[1] * 256,
       bres[2] + bres[3] * 256,
       bres[4] + bres[5] * 256,
       bres[6] + bres[7] * 256]
  Sail.write_reg op_a (Word.toBitVec64 op_a_write_value)

def bitwiseInitialState_cols (cols : BitwiseCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 51, fromMain Main = cols →
    (_root_.Bitwise.constraints Main).initialState s

end SP1Clean.Bitwise
