import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.JTypeReader.JTypeReader
import SP1Chips.Jal.JalChip
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.JTypeReader
import SP1Clean.Reader.OperandAccess
import SP1Clean.Operations.AddOperation
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import RISCV.Instructions

/-! # `JalChip` cols-level surface (JAL)

Entry-point module for `SP1Clean.JalChip`: defines the cols-level Sail-side
helpers (`sp1_op_a_cols`, `sp1_op_b_cols`, `sp1_jal_cols`,
`jalInitialState_cols`) that mirror `_root_.Jal`'s Main-level definitions but
project off `JalCols` fields directly.

The `JalCols` column struct and the `fromMain` / `toMain` projections live in
`SP1Clean/Chips/Structs.lean`; this file re-uses them via the `open` of
`SP1Clean.Jal`.

Note that `_root_.Jal.sp1_op_a Main cstrs h_is_real : BitVec 5` is dependent on
the `allHold` proof (for the `< 32` register-index bound). The cols-level
`sp1_op_a_cols` is the non-dependent `BitVec.ofNat 5 cols.adapter.op_a.val`
form; the bound bridge is reconstructed inside `SailBridge.lean` via
`Jal.op_a_lt32_of_constraints` on the `h_allHold` produced by
`allHold_iff_structural`.

Imported (in order) by:
- `SP1Clean.JalChip.Lemmas` — non-trivial lemmas about cols
  (`fromMain_toMain`, `allHold_iff_structural`).
- `SP1Clean.JalChip.Circuit` — `Assertion.main`, `FormalSpec`,
  soundness/completeness, and the `assertion : FormalAssertion`.
- `SP1Clean.JalChip.SailBridge` — the external `sail_correct_of_formalSpec`
  Sail-equivalence bridge. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions BitVec Sail

namespace SP1Clean.Jal

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail-side helpers

Mirror the Main-level `_root_.Jal.sp1_op_a` / `sp1_op_b` / `sp1_jal` projections
directly off `JalCols` fields. The non-dependent `BitVec.ofNat 5 cols.adapter.op_a.val`
form drops the `< 32` bound carried by the Main-level dependent form
(`Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)`); the bound is
recovered on demand inside `SailBridge.lean` and the two forms agree as
`BitVec 5` values when `cols.adapter.op_a.val < 32`. -/

@[reducible] def sp1_op_a_cols (cols : JalCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

/-- The 21-bit J-type immediate, recovered from the two low limbs of the
constrained 4-limb sign-extended immediate stored in `op_b_imm`. Mirrors
`_root_.Jal.sp1_op_b`. -/
@[reducible] def sp1_op_b_cols (cols : JalCols (ZMod p)) : BitVec 21 :=
  BitVec.ofNat 21 (cols.adapter.op_b_imm[0].val + cols.adapter.op_b_imm[1].val * 65536)

/-- The SP1 implementation: writes `next_pc` to `Register.nextPC` and the
return-address Word `op_a_write_value` to the destination register
`sp1_op_a_cols cols`. Mirrors `_root_.Jal.sp1_jal`. -/
def sp1_jal_cols (cols : JalCols (ZMod p)) : SailM Unit := do
  let op_a := regidx.Regidx (sp1_op_a_cols cols)
  set_next_pc (Word.toBitVec64 cols.next_pc)
  wX_bits op_a (Word.toBitVec64 cols.op_a_write_value)

/-- The cols-level state-bus precondition for the per-row Sail clause:
universally lifted over any flat `Main` row that re-projects to the given
`cols`. Mirrors `SP1Clean.UType.utypeInitialState_cols`. -/
def jalInitialState_cols (cols : JalCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 31, fromMain Main = cols →
    (_root_.Jal.constraints Main).initialState s

/-! ### Round-trip lemmas

Each non-dependent `cols`-level helper equals the corresponding `Main`-level
def when applied to `fromMain Main`. All close by `rfl` thanks to
`@[reducible]`. The dependent `_root_.Jal.sp1_op_a Main cstrs h_is_real`
helper has no `_cols` analog here: its `< 32` bound is reconstructed inside
`SailBridge.lean` from `(_root_.Jal.constraints Main).allHold` via
`op_a_lt32_of_constraints`, and the two BitVec 5 values coincide
(`BitVec.ofNat 5 Main[6].val = Main[6].val#'h` under `Main[6].val < 32`). -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 31) :
    sp1_op_b_cols (fromMain Main) = _root_.Jal.sp1_op_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_jal_cols_fromMain (Main : Vector (ZMod p) 31) :
    sp1_jal_cols (fromMain Main) = _root_.Jal.sp1_jal Main := rfl

end SP1Clean.Jal
