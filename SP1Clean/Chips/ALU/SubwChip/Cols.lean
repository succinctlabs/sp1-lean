import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Subw.SubwChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.SubwOperation
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `SubwChip` cols-level surface (directory-form scaffold)

Entry-point module for `SP1Clean.Subw`: defines the `SubwCols` column
struct, `fromMain`/`toMain` projections, and cols-level Sail-side helpers.

**Important divergence from `AddwChip`:** Subw uses `RTypeReader`, NOT
`ALUTypeReader`. There is no `SUBIW` pseudo-instruction in RV64I, so the
chip has a single variant (SUBW only). Row width: **32** (one less than
AddwChip's 36, due to the missing `op_c` 4-limb immediate slot and
`imm_c` column). `is_real = Main[31]`. Opcode index `20` (SUBW).

The 32-bit result is stored as 2 limbs (`Main[28..29]`) plus a `subw_msb`
column (`Main[30]`). The 4-limb `op_a_write_value` fed into RTypeReader
is reconstructed as `[subw_value[0], subw_value[1], subw_msb * 65535,
subw_msb * 65535]` (sign-extension).

Mirrors the `SP1Clean.Subw` template 1-for-1 (RType reader, opcode 20). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Subw

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail-side helpers -/

@[reducible] def sp1_op_a_cols (cols : SubwCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : SubwCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : SubwCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c.val

def sp1_subw_cols (cols : SubwCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a
    (Word.toBitVec64 #v[cols.subw_value[0], cols.subw_value[1],
                        cols.subw_msb * 65535, cols.subw_msb * 65535])

/-- The cols-level state-bus precondition for the per-row Sail clause. -/
def subwInitialState_cols (cols : SubwCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 32, fromMain Main = cols →
    (_root_.Subw.constraints Main).initialState s

/-! ### Round-trip lemmas -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 32) :
    sp1_op_a_cols (fromMain Main) = _root_.Subw.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 32) :
    sp1_op_b_cols (fromMain Main) = _root_.Subw.sp1_op_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 32) :
    sp1_op_c_cols (fromMain Main) = _root_.Subw.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_subw_cols_fromMain (Main : Vector (ZMod p) 32) :
    sp1_subw_cols (fromMain Main) = _root_.Subw.sp1_subw Main := rfl

end SP1Clean.Subw
