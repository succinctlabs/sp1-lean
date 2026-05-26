import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Add.AddChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.AddOperation
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `AddChip` cols-level surface

Entry-point module for `SP1Clean.AddChip`: defines the `AddCols` column
struct (mirroring SP1's Rust `AddCols<T, M: TrustMode>` under
`M = UserMode`), the `fromMain`/`toMain` projections between the flat
SP1 row and the structured `AddCols` view, and the `cols`-level Sail-side
helpers (`sp1_op_{a,b,c}_cols`, `sp1_add_cols`, `addInitialState_cols`)
that mirror `_root_.Add`'s Main-level definitions but project off
`AddCols` fields directly.

Imported (in order) by:
- `SP1Clean.AddChip.Lemmas` — non-trivial lemmas about cols
  (`fromMain_toMain`, `allHold_iff_structural`).
- `SP1Clean.AddChip.Circuit` — `Assertion.main`, `FormalSpec`,
  soundness/completeness, and the `assertion : FormalAssertion`.
- `SP1Clean.AddChip.SailBridge` — the external
  `sail_correct_of_formalSpec` Sail-equivalence bridge.

The aggregator `SP1Clean.AddChip` re-exports all four. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Add

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail-side helpers

Mirror the Main-level `_root_.Add.sp1_op_{a,b,c}` and `_root_.Add.sp1_add`
projections directly off `AddCols` fields, so the chip-level `FormalSpec`
Sail clause stays cols-parameterized without requiring callers to construct
a `Main : Vector (ZMod p) 33`. Each helper is `@[reducible]` so the
round-trip lemma `<helper>_cols (fromMain Main) = Add.<helper> Main` closes
by `rfl`. -/

@[reducible] def sp1_op_a_cols (cols : AddCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : AddCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : AddCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c.val

def sp1_add_cols (cols : AddCols (ZMod p)) : SailM Unit := do
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
`SP1Clean.AddChip.Lemmas.fromMain_toMain`). -/
def addInitialState_cols (cols : AddCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 33, fromMain Main = cols →
    (_root_.Add.constraints Main).initialState s

/-! ### Round-trip lemmas

Each `cols`-level helper equals the corresponding `Main`-level def when
applied to `fromMain Main`. All hold by `rfl` thanks to `@[reducible]`. -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_a_cols (fromMain Main) = _root_.Add.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_b_cols (fromMain Main) = _root_.Add.sp1_op_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_c_cols (fromMain Main) = _root_.Add.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_add_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_add_cols (fromMain Main) = _root_.Add.sp1_add Main := rfl

end SP1Clean.Add
