import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Sub.SubChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.SubOperation
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import RISCV.Instructions

/-! # `SubChip` cols-level surface (directory-form scaffold)

Entry-point module for `SP1Clean.Sub`: defines the `SubCols` column
struct (mirroring SP1's Rust `SubCols<T, M: TrustMode>` under
`M = UserMode`), the `fromMain`/`toMain` projections between the flat
SP1 row and the structured `SubCols` view, and the `cols`-level Sail-side
helpers (`sp1_op_{a,b,c}_cols`, `sp1_sub_cols`, `subInitialState_cols`).

NOTE: this directory currently uses namespace `SP1Clean.Sub` (matching
the module path) to coexist with the legacy single-file
`SP1Clean/SubChip.lean` whose namespace is `SP1Clean.Sub`. Once that file
is deleted, this namespace can be renamed to `SP1Clean.Sub` to match the
AddChip convention.

Mirrors the `SP1Clean.Add` template 1-for-1 (RType reader, opcode 2 swapping
in for opcode 0). Row width: **33** (`is_real = Main[32]`).

Imported (in order) by:
- `SP1Clean.Sub.Lemmas` — non-trivial lemmas about cols
  (`fromMain_toMain`, `allHold_iff_structural`).
- `SP1Clean.Sub.Circuit` — `Assertion.main`, `FormalSpec`,
  soundness/completeness, and the `assertion : FormalAssertion`.
- `SP1Clean.Sub.SailBridge` — the external
  `sail_correct_of_formalSpec` Sail-equivalence bridge. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Sub

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail-side helpers -/

@[reducible] def sp1_op_a_cols (cols : SubCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : SubCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : SubCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c.val

def sp1_sub_cols (cols : SubCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a (Word.toBitVec64 cols.op_a_write_value)

/-- The cols-level state-bus precondition for the per-row Sail clause. -/
def subInitialState_cols (cols : SubCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 33, fromMain Main = cols →
    (_root_.Sub.constraints Main).initialState s

/-! ### Round-trip lemmas -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_a_cols (fromMain Main) = _root_.Sub.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_b_cols (fromMain Main) = _root_.Sub.sp1_op_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_c_cols (fromMain Main) = _root_.Sub.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_sub_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_sub_cols (fromMain Main) = _root_.Sub.sp1_sub Main := rfl

/-! ## Chip-level `FormalSpec`

Mirrors `SP1Clean.Add.FormalSpec` swapping `AddOp` → `SubOp`, opcode `0`
→ `2`, `RV64.add` → `RV64.sub`. Semantic-only contract: the byte-borrow
decomposition that the SP1 `SubOperation` circuit threads internally is
*not* exposed here; it's the implementation detail of the `SubOp`
sub-circuit and is reconstructed on demand via
`SubOperation.iff_sp1_full` (see `Lemmas.lean`). The pure BitVec `RV64.sub`
semantic is the trailing conjunct (conditional on `is_real = 1`); the
monadic Sail equivalence to `_root_.Sub.spec_sub` is recovered externally
via `sail_correct_of_formalSpec` in `SailBridge.lean`. The standalone
`is_real * (is_real - 1) = 0` binary gate is absorbed into both
`CPUState.Gated.Assertion.Spec` and `RTypeReader.Gated.Assertion.Spec`'s
first conjuncts. -/
def FormalSpec (cols : SubCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, cols.is_real⟩ ∧
  SP1Clean.RTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, 2, cols.state.pc,
       cols.op_a_write_value, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.adapter.op_a_0 = 0 ∧
  (cols.is_real = 1 →
    Word.isU64 cols.op_a_write_value ∧
    Word.toBitVec64 cols.op_a_write_value =
      RV64.sub (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
               (Word.toBitVec64 cols.adapter.op_b_memory.prev_value))

end SP1Clean.Sub
