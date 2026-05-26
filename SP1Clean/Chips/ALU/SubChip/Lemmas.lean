import SP1Clean.Chips.ALU.SubChip.Cols
import SP1Operations.Operation.SubOperation.SubOperation
import SP1Clean.Operations.SubOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Sub.Common

/-! # `SubChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real` (carried as the chip's
  `Assumptions` in `Circuit.lean`). Closes via recursive `ext` through the
  `@[ext]`-marked nested sub-structures plus `Vector.ext` reducing to
  per-element `rfl`s.
- `allHold_iff_structural` — bridges `(_root_.Sub.constraints Main).allHold`
  under `is_real = 1` to the conjunction of `SubOp.Spec`, `cpu.Gated.Spec`,
  `rtype.Gated.Spec`, and the trailing `Main[13] = 0` op_a_0 gate. Used
  downstream by `SailBridge.lean` to reconstruct `(Sub.constraints
  (toMain cols)).allHold` from the structural conjuncts of `FormalSpec`.

Mirrors `SP1Clean/AddChip/Lemmas.lean` 1-for-1, swapping `AddOp`/`AddOperation`
→ `SubOp`/`SubOperation` and opcode `0` → `2`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Sub

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. -/
lemma fromMain_toMain (cols : SubCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, op_a_write_value, is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  simp [this, SubCols.ext_iff, CPUState.ext_iff,
    RTypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Sub.constraints Main` is exactly the conjunction of
`CPUState.Gated.Assertion.Spec`, `RTypeReader.Gated.Assertion.Spec`,
`Main[13] = 0` (the chip-level `op_a_0` zero gate), and the semantic
RV64-sub conjunct (`isU64` of the result + the BitVec equation), under
`is_real = Main[32] = 1`. The byte-borrow decomposition that SP1's
`SubOperation` threads internally is *not* exposed in the RHS — it's
reconstructed from the BitVec equation and the `isU64` bounds of op_b /
op_c (available from `RTypeReader.Gated.Spec`'s `RegisterAccess.Spec`
sub-conjuncts) via `SubOperation.iff_sp1_full`. Used inside the Sail
clause's external bridge (`SailBridge.sail_correct_of_formalSpec`) to
construct an `allHold` from the structural pieces of `FormalSpec`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Sub.constraints Main).allHold ↔
      (SP1Clean.CPUState.Gated.Assertion.Spec
          ⟨{ clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
             pc := #v[Main[3], Main[4], Main[5]] },
           #v[Main[3] + 4, Main[4], Main[5]], 8, Main[32]⟩ ∧
       SP1Clean.RTypeReader.Gated.Assertion.Spec
          ⟨Main[0], Main[2] + Main[1] * 65536, 2,
           #v[Main[3], Main[4], Main[5]],
           #v[Main[28], Main[29], Main[30], Main[31]],
           { op_a := Main[6],
             op_a_memory :=
               { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                 access_timestamp :=
                   { prev_low := Main[11], diff_low_limb := Main[12] } },
             op_a_0 := Main[13], op_b := Main[14],
             op_b_memory :=
               { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                 access_timestamp :=
                   { prev_low := Main[19], diff_low_limb := Main[20] } },
             op_c := Main[21],
             op_c_memory :=
               { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                 access_timestamp :=
                   { prev_low := Main[26], diff_low_limb := Main[27] } } },
           Main[32], Main[32]⟩ ∧
       Main[13] = 0 ∧
       Word.isU64 #v[Main[28], Main[29], Main[30], Main[31]] ∧
       Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] =
         RV64.sub (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]])
                  (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [_root_.Sub.allHold_constraints_iff Main, h_is_real,
      SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1,
      SP1Clean.RTypeReader.Gated.Assertion.Spec_iff_sp1]
  refine ⟨?_, ?_⟩
  · -- Forward: allHold → structural conjuncts + (isU64 ∧ RV64.sub eq).
    rintro ⟨h_op, h_cpu, h_rtr, _, h_op_a_0⟩
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_isU64_b : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] :=
      (h_rtr.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_isU64_c : Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] :=
      (h_rtr.2.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have ⟨h_isU64_v, h_bv⟩ :=
      (SubOperation.iff_sp1_full h_isU64_b h_isU64_c).mp h_op
    refine ⟨h_cpu, h_rtr, h_op_a_0, h_isU64_v, ?_⟩
    -- `h_bv : v.toBitVec64 = execute_RTYPE_pure_w op_b op_c .SUB`
    --       = op_b.toBitVec64 - op_c.toBitVec64`.
    -- Goal: `v.toBitVec64 = RV64.sub op_c.toBitVec64 op_b.toBitVec64`
    --       = `op_b.toBitVec64 - op_c.toBitVec64`. Closes by `RV64.sub` defeq.
    simp only [RV64.sub]
    exact h_bv
  · -- Backward: structural conjuncts + (isU64 ∧ RV64.sub eq) → allHold.
    rintro ⟨h_cpu, h_rtr, h_op_a_0, h_isU64_v, h_bv⟩
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_isU64_b : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] :=
      (h_rtr.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_isU64_c : Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] :=
      (h_rtr.2.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_bv' : Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] =
        execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]]
                             #v[Main[22], Main[23], Main[24], Main[25]] .SUB := by
      simp only [RV64.sub] at h_bv
      exact h_bv
    have h_op :=
      (SubOperation.iff_sp1_full h_isU64_b h_isU64_c).mpr ⟨h_isU64_v, h_bv'⟩
    refine ⟨h_op, h_cpu, h_rtr, ?_, h_op_a_0⟩
    ring

end SP1Clean.Sub
