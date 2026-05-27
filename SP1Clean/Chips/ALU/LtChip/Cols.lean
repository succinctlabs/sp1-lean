import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Chips.Lt.LtChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `LtChip` cols-level surface

Entry-point module for `SP1Clean.Lt`: defines the `LtCols` column
struct (via re-export from `SP1Clean/Chips/Structs.lean`), the
`fromMain`/`toMain` projections, and the cols-level Sail helpers
(`sp1_op_{a,b,c}_cols` for both `slt` and `sltu` variants;
`sp1_lt_cols`; `ltInitialState_cols`).

Mirrors the `SP1Clean.Add` / `SP1Clean.Sub` templates with the
ALUTypeReader (44-col row) reader composition. The chip bundles 4
RV64I variants (`slt`/`sltu`/`slti`/`sltiu`) but the Path-2
`FormalSpec` in `Chips/Spec.lean` covers only the R-type
`slt`/`sltu` pair; I-type `slti`/`sltiu` are deferred.

Imported (in order) by:
- `SP1Clean.Lt.Lemmas` — cols→Main bridges + structural midpoint.
- `SP1Clean.Lt.Circuit` — `Assertion.main`, soundness/completeness,
  `assertion : FormalAssertion`.
- `SP1Clean.Lt.SailBridge` — external `sail_correct_*_of_formalSpec`
  Sail-equivalence bridges (one per variant). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Lt

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail-side helpers (R-type variants) -/

@[reducible] def sp1_op_a_cols (cols : LtCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : LtCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : LtCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c[0].val

/-- Chip-level Sail computation: writes the compare bit (packed into
the low limb of a zero-padded 4-limb Word) to `op_a` and advances
`nextPC`. Mirrors `_root_.Lt.sp1_lt`. -/
def sp1_lt_cols (cols : LtCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a
    (Word.toBitVec64
      #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0])

/-- The cols-level state-bus precondition for the per-row Sail clause. -/
def ltInitialState_cols (cols : LtCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 44, fromMain Main = cols →
    (_root_.Lt.constraints Main).initialState s

/-! ### Round-trip lemmas -/

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_op_a_cols (fromMain Main) = _root_.Slt.sp1_op_a Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_op_b_cols (fromMain Main) = _root_.Slt.sp1_op_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_op_c_cols (fromMain Main) = _root_.Slt.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_lt_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_lt_cols (fromMain Main) = _root_.Lt.sp1_lt Main := rfl

end SP1Clean.Lt
