import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.ShiftRight.ShiftRightChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `ShiftRightChip` cols-level surface (4 variants: `srl`, `sra`,
`srlw`, `sraw`). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRight

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

@[reducible] def sp1_op_a_cols (cols : ShiftRightCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : ShiftRightCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : ShiftRightCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c[0].val

def shiftRightInitialState_cols (cols : ShiftRightCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 69, fromMain Main = cols →
    (_root_.ShiftRight.constraints Main).initialState s

end SP1Clean.ShiftRight
