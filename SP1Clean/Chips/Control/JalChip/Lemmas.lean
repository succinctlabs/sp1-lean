import SP1Clean.Chips.Control.JalChip.Cols
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Reader.JTypeReader.JTypeReader
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.JTypeReader
import SP1Clean.Operations.AddOperation
import SP1Chips.Jal.Common

/-! # `JalChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real`.
- `allHold_iff_structural` — bridges `(_root_.Jal.constraints Main).allHold`
  under `Main[30] = 1` to the canonical (a) structural conjunction over
  `fromMain Main`: `CPUState.Gated.Assertion.Spec`, two `AddOp.Assertion.Spec`
  (jump-target gated by `Main[30]`, return-address gated by `Main[30] - Main[13]
  = 1 - Main[13]`), `JTypeReader.Gated.Assertion.Spec` (with both `is_real` and
  `is_trusted` instantiated to `Main[30] = 1`), four scalar gates (`Main[25] = 0`
  next_pc[3]=0, `Main[29] = 0` op_a_write_value[3]=0, `Main[30] = 1 ∨ Main[13]
  = 0`, and the jump-target alignment Range14 consequence). Used downstream by
  `SailBridge.lean` to reconstruct SP1's `allHold` from the structural conjuncts
  of `FormalSpec`. **Structural sorry stub** for now (mirrors `UTypeChip/
  Circuit.lean`'s sorry'd soundness/completeness — both flow from the new
  canonical-(a) Spec shape and need the same proof restructuring); the
  one-directional `formalSpec_implies_allHold` direction can be reconstructed
  via the legacy `Jal.allHold_constraints_iff` (`SP1Chips/Jal/Common.lean:18`)
  plus `AddOperation.iff_sp1_full` plus `JTypeReader.Gated.Assertion.Spec_iff_sp1`
  using the operand `Word.isU64` bound from the JTypeReader's program-bus
  clause; that closure is mechanical but interacts with the inline-sends shape
  of `Jal.constraints` (no `CPUState.constraints` / `JTypeReader.constraints`
  sub-call envelope to bridge through directly). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Jal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. The precondition
captures `fromMain`'s aliasing of `is_trusted := Main[30] = is_real` (the chip
is UserMode). Recursive `ext` through `@[ext]`-marked `JalCols` / `CPUState` /
`JTypeReader` / `MemoryAccessInSharedCols` / `UserModeReaderCols` sub-structures
reduces to per-element `rfl`s via `Vector.ext` + `interval_cases`. -/
lemma fromMain_toMain (cols : JalCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, next_pc, op_a_write_value, is_real, adapter_cols⟩
  rcases state with ⟨clk_high, clk_16_24, clk_0_16, pc⟩
  rcases adapter with ⟨op_a, op_a_memory, op_a_0, op_b_imm, op_c_imm⟩
  rcases op_a_memory with ⟨prev_value, ts⟩
  rcases ts with ⟨prev_low, diff_low_limb⟩
  rcases adapter_cols with ⟨is_trusted⟩
  have : is_trusted = is_real := by simpa using h_trusted
  simp only [this, fromMain, toMain, JalCols.mk.injEq, CPUState.mk.injEq,
    JTypeReader.mk.injEq, MemoryAccessInSharedCols.mk.injEq,
    MemoryAccessInShardTimestamp.mk.injEq,
    UserModeReaderCols.mk.injEq, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, and_self, true_and,
    and_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply Vector.ext; intro i hi; interval_cases i <;> rfl)

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Jal.constraints Main` is exactly the canonical-(a) structural conjunction
under `is_real = Main[30] = 1`. Mirrors UTypeChip's `allHold_iff_structural`
in role.

**Structural sorry stub.** The forward direction is straightforward via
`Jal.allHold_constraints_iff` (`SP1Chips/Jal/Common.lean:18`) plus
`AddOperation.iff_sp1_full`. The reverse direction reconstructs the 24
inline propositional conjuncts of `Jal.constraints` from the four canonical
sub-circuit Specs — straightforward once the inline-send shape is mapped to
the `CPUState.Gated.Assertion.Spec` / `JTypeReader.Gated.Assertion.Spec`
conjuncts (no `CPUState.constraints` / `JTypeReader.constraints` sub-call
envelope to bridge through directly, unlike AddChip/UType). Closing this is
mechanical and tracked alongside the `UTypeChip/Circuit.lean` sorry'd
soundness/completeness. -/
theorem allHold_iff_structural
    (Main : Vector (ZMod p) 31) (h_is_real : Main[30] = 1) :
    (_root_.Jal.constraints Main).allHold ↔
      (SP1Clean.CPUState.Gated.Assertion.Spec
          ⟨{ clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
             pc := #v[Main[3], Main[4], Main[5]] },
           #v[Main[22], Main[23], Main[24]], 8, Main[30]⟩ ∧
       SP1Clean.AddOp.Assertion.Spec
          ⟨#v[Main[3], Main[4], Main[5], 0],
           #v[Main[14], Main[15], Main[16], Main[17]],
           #v[Main[22], Main[23], Main[24], Main[25]],
           Main[30]⟩ ∧
       SP1Clean.AddOp.Assertion.Spec
          ⟨#v[Main[3], Main[4], Main[5], 0],
           #v[4, 0, 0, 0],
           #v[Main[26], Main[27], Main[28], Main[29]],
           Main[30] - Main[13]⟩ ∧
       SP1Clean.JTypeReader.Gated.Assertion.Spec
          ⟨Main[0], Main[2] + Main[1] * 65536, 46,
           #v[Main[3], Main[4], Main[5]],
           #v[Main[26], Main[27], Main[28], Main[29]],
           { op_a := Main[6],
             op_a_memory :=
               { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                 access_timestamp :=
                   { prev_low := Main[11], diff_low_limb := Main[12] } },
             op_a_0 := Main[13],
             op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]],
             op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] },
           1, 1⟩ ∧
       Main[25] = 0 ∧
       Main[29] = 0 ∧
       (Main[30] = 1 ∨ Main[13] = 0) ∧
       (Main[30] = 1 → (Main[22] * (4 : ZMod p)⁻¹).val < 16384)) := by
  sorry

end SP1Clean.Jal
