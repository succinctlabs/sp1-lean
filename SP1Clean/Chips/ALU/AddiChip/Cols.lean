import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ITypeReader.ITypeReader
import SP1Chips.Addi.AddiChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Operations.AddOperation
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `AddiChip` cols-level surface

Entry-point module for `SP1Clean.AddiChip`: defines the `AddiCols` column
struct (mirroring SP1's Rust `AddiCols<T, M: TrustMode>` under
`M = UserMode`), the `fromMain`/`toMain` projections between the flat
SP1 row and the structured `AddiCols` view, and the `cols`-level Sail-side
helpers (`sp1_op_{a,b,c}_cols`, `sp1_addi_cols`, `addiInitialState_cols`)
that mirror `_root_.Addi`'s Main-level definitions but project off
`AddiCols` fields directly.

Imported (in order) by:
- `SP1Clean.AddiChip.Lemmas` — non-trivial lemmas about cols
  (`fromMain_toMain`, `allHold_iff_structural`).
- `SP1Clean.AddiChip.Circuit` — `Assertion.main`, `FormalSpec`,
  soundness/completeness, and the `assertion : FormalAssertion`.
- `SP1Clean.AddiChip.SailBridge` — the external
  `sail_correct_of_formalSpec` Sail-equivalence bridge.

The aggregator `SP1Clean.AddiChip` re-exports all four. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addi

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail-side helpers

Mirror the Main-level `_root_.Addi.sp1_op_{a,b,c}` and `_root_.Addi.sp1_addi`
projections directly off `AddiCols` fields. Each helper is `@[reducible]` so
the round-trip lemma `<helper>_cols (fromMain Main) = Addi.<helper> Main`
closes by `rfl`. -/

@[reducible] def sp1_op_a_cols (cols : AddiCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : AddiCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

/-- The I-type 12-bit immediate, decoded from limb 0 of `op_c_imm`. Mirrors
`_root_.Addi.sp1_op_c` which uses `Main[21].val`. -/
@[reducible] def sp1_op_c_cols (cols : AddiCols (ZMod p)) : BitVec 12 :=
  BitVec.ofNat 12 cols.adapter.op_c_imm[0].val

def sp1_addi_cols (cols : AddiCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a (Word.toBitVec64 cols.op_a_write_value)

/-- The cols-level state-bus precondition for the per-row Sail clause:
universally lifted over any flat `Main` row that re-projects to the given
`cols`. Stated this way (rather than directly via `toMain cols`) so we
don't depend on a `fromMain (toMain cols) = cols` round-trip, which fails
by `rfl` due to `Vector` not having structural eta. Downstream consumers
that have `cols` in hand can specialize with `Main := toMain cols` (using
`SP1Clean.AddiChip.Lemmas.fromMain_toMain`). -/
def addiInitialState_cols (cols : AddiCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 30, fromMain Main = cols →
    (_root_.Addi.constraints Main).initialState s

/-! ### Round-trip lemmas

Each `cols`-level helper equals the corresponding `Main`-level def when
applied to `fromMain Main`. All hold by `rfl` thanks to `@[reducible]`. -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 30) :
    sp1_op_a_cols (fromMain Main) = _root_.Addi.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 30) :
    sp1_op_b_cols (fromMain Main) = _root_.Addi.sp1_op_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 30) :
    sp1_op_c_cols (fromMain Main) = _root_.Addi.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_addi_cols_fromMain (Main : Vector (ZMod p) 30) :
    sp1_addi_cols (fromMain Main) = _root_.Addi.sp1_addi Main := rfl

end SP1Clean.Addi
