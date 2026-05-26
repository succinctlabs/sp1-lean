import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.Addw.AddwChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.AddwOperation
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `AddwChip` cols-level surface

Entry-point module for `SP1Clean.AddwChip`: defines the `AddwCols` column
struct (mirroring SP1's Rust `AddwCols<T, M: TrustMode>` under
`M = UserMode`), the `fromMain`/`toMain` projections between the flat
SP1 row and the structured `AddwCols` view, and the `cols`-level Sail-side
helpers (`sp1_op_{a,b,c}_cols`, `sp1_addw_cols`, `addwInitialState_cols`)
that mirror `_root_.Addw`'s Main-level definitions but project off
`AddwCols` fields directly.

The Addw chip bundles two RV64IM variants (`addw` R-type and `addiw`
I-type) into a single 36-column trace, distinguished by the shared
`ALUTypeReader`'s `imm_c` flag at `Main[31]`. The 32-bit result is
stored in two limbs (`Main[32..33]`) plus a `msb` column (`Main[34]`)
that seeds the high-bit decomposition; the 4-limb `op_a_write_value`
fed into the reader is reconstructed as `[addw_value[0], addw_value[1],
msb * 65535, msb * 65535]`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addw

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail-side helpers

Mirror the Main-level `_root_.Addw.sp1_op_{a,b,c}` and `_root_.Addw.sp1_addw`/
`sp1_addiw` projections directly off `AddwCols` fields. Each helper is
`@[reducible]` so the round-trip lemma `<helper>_cols (fromMain Main) =
Addw.<helper> Main` closes by `rfl`. -/

@[reducible] def sp1_op_a_cols (cols : AddwCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : AddwCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

/-- For ADDW, op_c is a register index (5 bits from op_c[0]). -/
@[reducible] def sp1_op_c_cols (cols : AddwCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c[0].val

/-- For ADDIW, op_c carries a 12-bit immediate in limb 0. -/
@[reducible] def sp1_op_c_imm_cols (cols : AddwCols (ZMod p)) : BitVec 12 :=
  BitVec.ofNat 12 cols.adapter.op_c[0].val

def sp1_addw_cols (cols : AddwCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a
    (Word.toBitVec64 #v[cols.addw_value[0], cols.addw_value[1],
                        cols.addw_msb * 65535, cols.addw_msb * 65535])

/-- The cols-level state-bus precondition for the per-row Sail clause. -/
def addwInitialState_cols (cols : AddwCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 36, fromMain Main = cols →
    (_root_.Addw.constraints Main).initialState s

/-! ### Round-trip lemmas -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 36) :
    sp1_op_a_cols (fromMain Main) = _root_.Addw.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 36) :
    sp1_op_b_cols (fromMain Main) = _root_.Addw.sp1_op_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 36) :
    sp1_op_c_cols (fromMain Main) = _root_.Addw.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_addw_cols_fromMain (Main : Vector (ZMod p) 36) :
    sp1_addw_cols (fromMain Main) = _root_.Addw.sp1_addw Main := rfl

end SP1Clean.Addw
