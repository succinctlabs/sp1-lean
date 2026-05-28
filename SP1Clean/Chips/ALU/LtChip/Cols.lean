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

/-! ### Register memory accesses (trace-level OfflineMemory aggregation) -/

/-- The op_a / op_b / op_c register accesses, exposed for trace-level
OfflineMemory aggregation. op_a writes the 4-limb boolean result
`#v[compare_bit, 0, 0, 0]`. -/
def opAMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_a, 0, 0],
    prev_value := cols.adapter.op_a_memory.prev_value,
    prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }

def opBMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_b, 0, 0],
    prev_value := cols.adapter.op_b_memory.prev_value,
    prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }

def opCMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_c[0], 0, 0],
    prev_value := cols.adapter.op_c_memory.prev_value,
    prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb }

end SP1Clean.Lt
