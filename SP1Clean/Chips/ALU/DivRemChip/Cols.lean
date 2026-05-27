import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.DivRem.Constraints
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `DivRemChip` cols-level surface (8 variants:
`div`/`divu`/`rem`/`remu`/`divw`/`remw`/`divuw`/`remuw`). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRem

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

@[reducible] def sp1_op_a_cols (cols : DivRemCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : DivRemCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : DivRemCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c.val

def divRemInitialState_cols (cols : DivRemCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 246, fromMain Main = cols →
    (_root_.DivRem.constraints Main).initialState s

end SP1Clean.DivRem
