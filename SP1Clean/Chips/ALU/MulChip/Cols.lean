import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Chips.Mul.MulChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.MulOperation
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `MulChip` cols-level surface (5 variants:
`mul`/`mulh`/`mulhu`/`mulhsu`/`mulw`). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Mul

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

@[reducible] def sp1_op_a_cols (cols : MulCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : MulCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : MulCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c.val

def mulInitialState_cols (cols : MulCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 82, fromMain Main = cols →
    (_root_.Mul.constraints Main).initialState s

end SP1Clean.Mul
