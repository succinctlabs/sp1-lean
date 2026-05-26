import SP1Clean.UTypeChip.Cols
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Reader.JTypeReader.JTypeReader
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.JTypeReader
import SP1Chips.UType.Common

/-! # `UTypeChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real`.
- `allHold_iff_structural` — bridges `(_root_.UType.constraints Main).allHold`
  under `is_real = 1` to the structural conjunction (cpuStateSpec, AddOp
  `.allHold` raw, jtypeReaderSpec, six scalar gates) over `fromMain Main`.
  This is the chip's structural Spec minus the BitVec conjunct — used by
  `SailBridge.lean` to reconstruct SP1's `allHold` from `FormalSpec`.

The AddOp clause is kept in raw `.allHold` form on both sides because
`AddOperation.allHold_constraints_iff` is only stated at `is_real_arg = 1`,
and UType's AddOp gate is the conditional `is_real - op_a_0`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.UType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. The precondition
captures `fromMain`'s aliasing of `is_trusted := Main[30] = is_real` (which
matches the constraint compiler's emission — Main[30] is both `is_real` and
`is_trusted` because the chip is UserMode). -/
lemma fromMain_toMain (cols : UTypeCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, addend, add_result, is_auipc, is_real, adapter_cols⟩
  rcases state with ⟨clk_high, clk_16_24, clk_0_16, pc⟩
  rcases adapter with ⟨op_a, op_a_memory, op_a_0, op_b_imm, op_c_imm⟩
  rcases op_a_memory with ⟨prev_value, ts⟩
  rcases ts with ⟨prev_low, diff_low_limb⟩
  rcases adapter_cols with ⟨is_trusted⟩
  have : is_trusted = is_real := by simpa using h_trusted
  simp only [this, fromMain, toMain, UTypeCols.mk.injEq, CPUState.mk.injEq,
    JTypeReader.mk.injEq, MemoryAccessInSharedCols.mk.injEq,
    MemoryAccessInShardTimestamp.mk.injEq,
    UserModeReaderCols.mk.injEq, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, and_self, true_and,
    and_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply Vector.ext; intro i hi; interval_cases i <;> rfl)

set_option maxHeartbeats 800000 in
-- Higher heartbeats: the iff destructure unfolds the full UType
-- constraint list (CPUState ++ AddOperation ++ JTypeReader ++ 7 trailing
-- assertZeros) and applies the CPUState/JTypeReader Spec rewrites.
/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`UType.constraints Main` is exactly the conjunction of `cpuStateSpec`, the
raw `AddOperation` `.allHold`, `JTypeReader.Gated.Assertion.Spec` (with
both `is_real` and `is_trusted` instantiated to `Main[30]`), and four
scalar gates over `fromMain Main`, under `is_real = Main[30] = 1`. The
AddOperation clause stays in raw `.allHold` form on both sides because
its is_real argument is the conditional `Main[30] - Main[13]`
(= `is_real - op_a_0`), so the operation-level `iff_sp1` cannot fire. The
free chip-level `Main[30] * (Main[30] - 1) = 0` and `(Main[30] - 1) *
Main[13] = 0` gates are absorbed into `JTypeReader.Gated.Assertion.Spec`
(into its first conjunct and into `ProgramSpec`'s op_a_0 binary clause
respectively, both under `Main[30] = 1`). -/
theorem allHold_iff_structural
    (Main : Vector (ZMod p) 31) (h_is_real : Main[30] = 1) :
    (_root_.UType.constraints Main).allHold ↔
      (SP1Clean.CPUState.cpuStateSpec Main[2] Main[1] ∧
       (_root_.AddOperation.constraints (F := ZMod p)
           #v[Main[22], Main[23], Main[24], 0]
           #v[Main[14], Main[15], Main[16], Main[17]]
           { value := #v[Main[25], Main[26], Main[27], Main[28]] }
           (1 - Main[13])).allHold ∧
       SP1Clean.JTypeReader.Gated.Assertion.Spec
           ⟨Main[0], Main[2] + Main[1] * 65536,
            Main[29] * 48 + (1 - Main[29]) * 49,
            #v[Main[3], Main[4], Main[5]],
            #v[Main[25], Main[26], Main[27], Main[28]],
            { op_a := Main[6],
              op_a_memory :=
                { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                  access_timestamp :=
                    { prev_low := Main[11], diff_low_limb := Main[12] } },
              op_a_0 := Main[13],
              op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]],
              op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] },
            1, 1⟩ ∧
       Main[29] * (Main[29] - 1) = 0 ∧
       Main[22] - Main[29] * Main[3] = 0 ∧
       Main[23] - Main[29] * Main[4] = 0 ∧
       Main[24] - Main[29] * Main[5] = 0 ∧
       (1 - 1) * Main[13] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Step 1: expand UType.constraints into its 3 sub-`.allHold` pieces +
  -- 7 chip-level trailing scalar gates. Uses an inline `show` block (rather
  -- than `UType.allHold_constraints_iff` directly) so each sub-clause is
  -- in `.allHold` (not `List.Forall SP1Constraint.toProp`) form — needed
  -- for the `_iff_sp1` rewrites below to fire syntactically.
  rw [show (_root_.UType.constraints Main).allHold ↔
        ((_root_.CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[3] + 4, Main[4], Main[5]] 8 Main[30]).allHold ∧
          (_root_.AddOperation.constraints (F := ZMod p)
              #v[Main[22], Main[23], Main[24], 0]
              #v[Main[14], Main[15], Main[16], Main[17]]
              { value := #v[Main[25], Main[26], Main[27], Main[28]] }
              (Main[30] - Main[13])).allHold ∧
          (_root_.JTypeReader.constraints (F := ZMod p)
              Main[0] (Main[2] + Main[1] * 65536)
              #v[Main[3], Main[4], Main[5]]
              (Main[29] * 48 + (1 - Main[29]) * 49)
              #v[Main[25], Main[26], Main[27], Main[28]]
              { op_a := Main[6],
                op_a_memory :=
                  { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                    access_timestamp :=
                      { prev_low := Main[11], diff_low_limb := Main[12] } },
                op_a_0 := Main[13],
                op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]],
                op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] }
              Main[30] Main[30]).allHold ∧
          (Main[30] * (Main[30] - 1) = 0 ∧
           Main[29] * (Main[29] - 1) = 0 ∧
           Main[22] - (Main[29] * Main[3] + (1 - Main[29]) * 0) = 0 ∧
           Main[23] - (Main[29] * Main[4] + (1 - Main[29]) * 0) = 0 ∧
           Main[24] - (Main[29] * Main[5] + (1 - Main[29]) * 0) = 0 ∧
           (Main[30] - 1) * Main[13] = 0)) from by
      simp [_root_.UType.constraints, SP1ConstraintList.allHold,
        List.forall_append, List.Forall, SP1Constraint.toProp]]
  -- Step 2: apply h_is_real (Main[30] = 1) everywhere.
  rw [h_is_real]
  -- Step 3: apply CPUState semantic Spec + JTypeReader Gated Spec bridges.
  rw [SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.JTypeReader.Gated.Assertion.Spec_iff_sp1]
  -- Step 4: cleanup — fold redundant `1 * 0 = 0`, drop redundant
  -- `(1 - 1) * Main[13] = 0` (absorbed into Gated.Spec under Main[30] = 1),
  -- and fold the `(1 - Main[29]) * 0` away (3 addend gates).
  simp

end SP1Clean.UType
