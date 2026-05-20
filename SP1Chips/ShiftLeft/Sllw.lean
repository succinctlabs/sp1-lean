import SP1Chips.ShiftLeft.Common

namespace ShiftLeft

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
set_option maxHeartbeats 100000000
set_option linter.style.longLine false


section sllw_poly

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

-- ============================================================================
-- RESTRUCTURE SKETCH for spec.sllw_poly (see /home/dtumad/.claude/plans/
--   sllw_poly_restructure_sketch.md for the design rationale).
--
-- The naive inline approach to spec.sllw_poly hangs past 17 min during
-- elaboration (vs. spec.sll_poly's ~80s baseline for 64 sub-cases). The
-- bottleneck is the goal-manipulation chain (`simp only [execute_RTYPEW_pure_w_poly,
-- ..., sign_extend, signExtend]` followed by `change ...`) compounding inside
-- one lemma with the 32 sub-case helper applications.
--
-- The plan: split into 3 lemmas. The two private branch lemmas elaborate
-- within their own heartbeat budgets without compounding.
-- ============================================================================

/-- Branch lemma for `spec.sllw_poly`'s `cb4 = 0` (byte_shift=0) case.
Takes destructured cstrs facts as flat arguments; runs the 16-way cb0..3
split internally; concludes the post-`simp [execute_RTYPEW_pure_w_poly,
execute_RTYPEW_pure_32_w_poly, sign_extend, signExtend]` form of the goal
(with `Word.low_poly` already reduced to the 2-limb HWord form). -/
private lemma spec.sllw_poly_cb4_zero (Main : Vector (ZMod p) 65)
    (b0_16 : Main[15].val < 65536) (b1_16 : Main[16].val < 65536)
    (c0_16 : Main[25].val < 65536) (c1_16 : Main[26].val < 65536)
    (b_cb0 : Main[36] = 0 ∨ Main[36] = 1)
    (b_cb1 : Main[37] = 0 ∨ Main[37] = 1)
    (b_cb2 : Main[38] = 0 ∨ Main[38] = 1)
    (b_cb3 : Main[39] = 0 ∨ Main[39] = 1)
    (hcb4 : Main[40] = 0)
    (h_su161 : Main[46] = 0 ∨ Main[40] = 1)
    (h_su45_46_sum : Main[45] + Main[46] = 1)
    (eq_v01 : Main[42] = (Main[36] + 1) * (Main[37] * 3 + 1))
    (eq_v012 : Main[43] = Main[42] * (Main[38] * 15 + 1))
    (eq_v0123 : Main[44] = Main[43] * (Main[39] * 255 + 1))
    (lt_ll0 : Main[49].val < 2 ^ ((16 : ZMod p) -
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val)
    (lt_lh0 : Main[53].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 : ZMod p).val)
    (lt_ll1 : Main[50].val < 2 ^ ((16 : ZMod p) -
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val)
    (lt_lh1 : Main[54].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 : ZMod p).val)
    (h_b0_dec : Main[15] * Main[44] = Main[53] * 65536 + Main[49] * Main[44])
    (h_b1_dec : Main[16] * Main[44] = Main[54] * 65536 + Main[50] * Main[44])
    (eq_lr0 : Main[57] = Main[49] * Main[44])
    (eq_lr1 : Main[58] = Main[50] * Main[44] + Main[53])
    (w_00' : Main[45] = 0 ∨ Main[32] = Main[57])
    (w_01' : Main[45] = 0 ∨ Main[33] = Main[58])
    (h_a2_eq : Main[61] * 65535 = Main[34])
    (h_a3_eq : Main[61] * 65535 = Main[35])
    (h_msb_a1 : List.Forall SP1Constraint.toProp
      (U16MSBOperation.constraints Main[33] { msb := Main[61] } 1))
    (h_c_mod_32 : Main[25].val % 32 =
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16).val) :
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
      BitVec.signExtend 64 (HWord.toBitVec32_poly #v[Main[15], Main[16]] <<<
        BitVec.setWidth 5 (HWord.toBitVec32_poly #v[Main[25], Main[26]])) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_v0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_v1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_1_ne_0 : (1 : ZMod p) ≠ 0 := by
    intro h; rw [h] at h_v1_val; rw [h_v0_val] at h_v1_val; exact zero_ne_one h_v1_val
  -- Derive h_46_eq from h_su161 (cb4 = 0 forces left disjunct).
  have h_46_eq : Main[46] = 0 := by
    rcases h_su161 with h | h
    · exact h
    · exfalso; rw [hcb4] at h; exact h_1_ne_0 h.symm
  -- Derive h_45_eq.
  have h_45_eq : Main[45] = 1 := by
    have := h_su45_46_sum; rw [h_46_eq] at this; linear_combination this
  -- Extract a0 = lr0, a1 = lr1 from w_00', w_01'.
  have h_45_ne_0 : Main[45] ≠ 0 := by rw [h_45_eq]; exact h_1_ne_0
  have h_a0_eq : Main[32] = Main[57] := w_00'.resolve_left h_45_ne_0
  have h_a1_eq : Main[33] = Main[58] := w_01'.resolve_left h_45_ne_0
  -- Substitute a0, a1 in goal and h_msb_a1.
  rw [h_a0_eq, h_a1_eq, eq_lr0, eq_lr1]
  rw [h_a1_eq, eq_lr1] at h_msb_a1
  -- 16-way cb0..3 split + per-sub-case helper application.
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
  · -- (0,0,0,0): S=0, M=1, N=65536
    have hv0123_val : Main[44].val = 1 := by
      have h : Main[44] = 1 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact h_v1_val
    exact sllw_subcase_cb4_zero 0 (by omega) 1 65536 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,0,0,1): S=8, M=256, N=256
    have hv0123_val : Main[44].val = 256 := by
      have h : Main[44] = 256 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_256_zmod_p
    exact sllw_subcase_cb4_zero 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,0,1,0): S=4, M=16, N=4096
    have hv0123_val : Main[44].val = 16 := by
      have h : Main[44] = 16 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_16_zmod_p
    exact sllw_subcase_cb4_zero 4 (by omega) 16 4096 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,0,1,1): S=12, M=4096, N=16
    have hv0123_val : Main[44].val = 4096 := by
      have h : Main[44] = 4096 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_4096_zmod_p
    exact sllw_subcase_cb4_zero 12 (by omega) 4096 16 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,1,0,0): S=2, M=4, N=16384
    have hv0123_val : Main[44].val = 4 := by
      have h : Main[44] = 4 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_4_zmod_p
    exact sllw_subcase_cb4_zero 2 (by omega) 4 16384 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,1,0,1): S=10, M=1024, N=64
    have hv0123_val : Main[44].val = 1024 := by
      have h : Main[44] = 1024 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_1024_zmod_p
    exact sllw_subcase_cb4_zero 10 (by omega) 1024 64 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,1,1,0): S=6, M=64, N=1024
    have hv0123_val : Main[44].val = 64 := by
      have h : Main[44] = 64 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_64_zmod_p
    exact sllw_subcase_cb4_zero 6 (by omega) 64 1024 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,1,1,1): S=14, M=16384, N=4
    have hv0123_val : Main[44].val = 16384 := by
      have h : Main[44] = 16384 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_16384_zmod_p
    exact sllw_subcase_cb4_zero 14 (by omega) 16384 4 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,0,0,0): S=1, M=2, N=32768
    have hv0123_val : Main[44].val = 2 := by
      have h : Main[44] = 2 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_2_zmod_p
    exact sllw_subcase_cb4_zero 1 (by omega) 2 32768 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,0,0,1): S=9, M=512, N=128
    have hv0123_val : Main[44].val = 512 := by
      have h : Main[44] = 512 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_512_zmod_p
    exact sllw_subcase_cb4_zero 9 (by omega) 512 128 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,0,1,0): S=5, M=32, N=2048
    have hv0123_val : Main[44].val = 32 := by
      have h : Main[44] = 32 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_32_zmod_p
    exact sllw_subcase_cb4_zero 5 (by omega) 32 2048 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,0,1,1): S=13, M=8192, N=8
    have hv0123_val : Main[44].val = 8192 := by
      have h : Main[44] = 8192 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_8192_zmod_p
    exact sllw_subcase_cb4_zero 13 (by omega) 8192 8 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,1,0,0): S=3, M=8, N=8192
    have hv0123_val : Main[44].val = 8 := by
      have h : Main[44] = 8 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_8_zmod_p
    exact sllw_subcase_cb4_zero 3 (by omega) 8 8192 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,1,0,1): S=11, M=2048, N=32
    have hv0123_val : Main[44].val = 2048 := by
      have h : Main[44] = 2048 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_2048_zmod_p
    exact sllw_subcase_cb4_zero 11 (by omega) 2048 32 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,1,1,0): S=7, M=128, N=512
    have hv0123_val : Main[44].val = 128 := by
      have h : Main[44] = 128 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_128_zmod_p
    exact sllw_subcase_cb4_zero 7 (by omega) 128 512 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,1,1,1): S=15, M=32768, N=2
    have hv0123_val : Main[44].val = 32768 := by
      have h : Main[44] = 32768 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_32768_zmod_p
    exact sllw_subcase_cb4_zero 15 (by omega) 32768 2 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32

/-- Mirror of `spec.sllw_poly_cb4_zero` for the `cb4 = 1` (byte_shift=1) branch.
a0 substitutes to 0, a1 substitutes to lr0 = ll0 * v0123. -/
private lemma spec.sllw_poly_cb4_one (Main : Vector (ZMod p) 65)
    (b0_16 : Main[15].val < 65536) (b1_16 : Main[16].val < 65536)
    (c0_16 : Main[25].val < 65536) (c1_16 : Main[26].val < 65536)
    (b_cb0 : Main[36] = 0 ∨ Main[36] = 1)
    (b_cb1 : Main[37] = 0 ∨ Main[37] = 1)
    (b_cb2 : Main[38] = 0 ∨ Main[38] = 1)
    (b_cb3 : Main[39] = 0 ∨ Main[39] = 1)
    (hcb4 : Main[40] = 1)
    (h_su160 : Main[45] = 0 ∨ Main[40] = 0)
    (h_su45_46_sum : Main[45] + Main[46] = 1)
    (eq_v01 : Main[42] = (Main[36] + 1) * (Main[37] * 3 + 1))
    (eq_v012 : Main[43] = Main[42] * (Main[38] * 15 + 1))
    (eq_v0123 : Main[44] = Main[43] * (Main[39] * 255 + 1))
    (lt_ll0 : Main[49].val < 2 ^ ((16 : ZMod p) -
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val)
    (lt_lh0 : Main[53].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 : ZMod p).val)
    (lt_ll1 : Main[50].val < 2 ^ ((16 : ZMod p) -
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val)
    (lt_lh1 : Main[54].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 : ZMod p).val)
    (h_b0_dec : Main[15] * Main[44] = Main[53] * 65536 + Main[49] * Main[44])
    (h_b1_dec : Main[16] * Main[44] = Main[54] * 65536 + Main[50] * Main[44])
    (eq_lr0 : Main[57] = Main[49] * Main[44])
    (w_02' : Main[46] = 0 ∨ Main[32] = 0)
    (w_03' : Main[46] = 0 ∨ Main[33] = Main[57])
    (h_a2_eq : Main[61] * 65535 = Main[34])
    (h_a3_eq : Main[61] * 65535 = Main[35])
    (h_msb_a1 : List.Forall SP1Constraint.toProp
      (U16MSBOperation.constraints Main[33] { msb := Main[61] } 1))
    (h_c_mod_32 : Main[25].val % 32 =
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16).val) :
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
      BitVec.signExtend 64 (HWord.toBitVec32_poly #v[Main[15], Main[16]] <<<
        BitVec.setWidth 5 (HWord.toBitVec32_poly #v[Main[25], Main[26]])) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_v0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_v1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_1_ne_0 : (1 : ZMod p) ≠ 0 := by
    intro h; rw [h] at h_v1_val; rw [h_v0_val] at h_v1_val; exact zero_ne_one h_v1_val
  -- Derive h_45_eq from h_su160 (cb4 = 1 forces left disjunct).
  have h_45_eq : Main[45] = 0 := by
    rcases h_su160 with h | h
    · exact h
    · exfalso; rw [hcb4] at h; exact h_1_ne_0 h
  -- Derive h_46_eq.
  have h_46_eq : Main[46] = 1 := by
    have := h_su45_46_sum; rw [h_45_eq] at this; linear_combination this
  -- Extract a0 = 0, a1 = lr0 from w_02', w_03'.
  have h_46_ne_0 : Main[46] ≠ 0 := by rw [h_46_eq]; exact h_1_ne_0
  have h_a0_eq : Main[32] = 0 := w_02'.resolve_left h_46_ne_0
  have h_a1_eq : Main[33] = Main[57] := w_03'.resolve_left h_46_ne_0
  -- Substitute a0, a1 in goal and h_msb_a1.
  rw [h_a0_eq, h_a1_eq, eq_lr0]
  rw [h_a1_eq, eq_lr0] at h_msb_a1
  -- 16-way cb0..3 split + per-sub-case helper application.
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
  · -- (0,0,0,0): S=0, M=1, N=65536, total shift = 16
    have hv0123_val : Main[44].val = 1 := by
      have h : Main[44] = 1 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact h_v1_val
    exact sllw_subcase_cb4_one 0 (by omega) 1 65536 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,0,0,1): S=8, M=256, N=256, total shift = 24
    have hv0123_val : Main[44].val = 256 := by
      have h : Main[44] = 256 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_256_zmod_p
    exact sllw_subcase_cb4_one 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,0,1,0): S=4, M=16, N=4096
    have hv0123_val : Main[44].val = 16 := by
      have h : Main[44] = 16 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_16_zmod_p
    exact sllw_subcase_cb4_one 4 (by omega) 16 4096 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,0,1,1): S=12, M=4096, N=16
    have hv0123_val : Main[44].val = 4096 := by
      have h : Main[44] = 4096 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_4096_zmod_p
    exact sllw_subcase_cb4_one 12 (by omega) 4096 16 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,1,0,0): S=2, M=4, N=16384
    have hv0123_val : Main[44].val = 4 := by
      have h : Main[44] = 4 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_4_zmod_p
    exact sllw_subcase_cb4_one 2 (by omega) 4 16384 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,1,0,1): S=10, M=1024, N=64
    have hv0123_val : Main[44].val = 1024 := by
      have h : Main[44] = 1024 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_1024_zmod_p
    exact sllw_subcase_cb4_one 10 (by omega) 1024 64 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,1,1,0): S=6, M=64, N=1024
    have hv0123_val : Main[44].val = 64 := by
      have h : Main[44] = 64 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_64_zmod_p
    exact sllw_subcase_cb4_one 6 (by omega) 64 1024 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (0,1,1,1): S=14, M=16384, N=4
    have hv0123_val : Main[44].val = 16384 := by
      have h : Main[44] = 16384 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_16384_zmod_p
    exact sllw_subcase_cb4_one 14 (by omega) 16384 4 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,0,0,0): S=1, M=2, N=32768
    have hv0123_val : Main[44].val = 2 := by
      have h : Main[44] = 2 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_2_zmod_p
    exact sllw_subcase_cb4_one 1 (by omega) 2 32768 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,0,0,1): S=9, M=512, N=128
    have hv0123_val : Main[44].val = 512 := by
      have h : Main[44] = 512 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_512_zmod_p
    exact sllw_subcase_cb4_one 9 (by omega) 512 128 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,0,1,0): S=5, M=32, N=2048
    have hv0123_val : Main[44].val = 32 := by
      have h : Main[44] = 32 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_32_zmod_p
    exact sllw_subcase_cb4_one 5 (by omega) 32 2048 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,0,1,1): S=13, M=8192, N=8
    have hv0123_val : Main[44].val = 8192 := by
      have h : Main[44] = 8192 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_8192_zmod_p
    exact sllw_subcase_cb4_one 13 (by omega) 8192 8 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,1,0,0): S=3, M=8, N=8192
    have hv0123_val : Main[44].val = 8 := by
      have h : Main[44] = 8 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_8_zmod_p
    exact sllw_subcase_cb4_one 3 (by omega) 8 8192 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,1,0,1): S=11, M=2048, N=32
    have hv0123_val : Main[44].val = 2048 := by
      have h : Main[44] = 2048 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_2048_zmod_p
    exact sllw_subcase_cb4_one 11 (by omega) 2048 32 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,1,1,0): S=7, M=128, N=512
    have hv0123_val : Main[44].val = 128 := by
      have h : Main[44] = 128 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_128_zmod_p
    exact sllw_subcase_cb4_one 7 (by omega) 128 512 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32
  · -- (1,1,1,1): S=15, M=32768, N=2
    have hv0123_val : Main[44].val = 32768 := by
      have h : Main[44] = 32768 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
      rw [h]; exact val_32768_zmod_p
    exact sllw_subcase_cb4_one 15 (by omega) 32768 2 (by decide) (by omega) rfl rfl
      hv0123_val
      (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
      (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      b0_16 b1_16 c0_16 c1_16 h_msb_a1 h_a2_eq h_a3_eq h_c_mod_32

/-- Outer `spec.sllw_poly`: destructure cstrs, derive bounds, h_c_mod_32, w_*'
resolution; manually unfold `Word.low_poly` (avoiding the expensive `change`
tactic from the failed inline approach); dispatch on `cb4` to the two branch
lemmas above. -/
lemma spec.sllw_poly (Main : Vector (ZMod p) 65) (h : is_sllw_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SLLW := by
  intro cstrs
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨eq_sllw, _eq_imm⟩ := h
  have h_real := is_real_eq_one_of_sllw Main cstrs eq_sllw
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  obtain ⟨b0_16, b1_16, _b2_16, _b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨c0_16, c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  obtain ⟨_sop_1, sop_2⟩ := single_op_poly Main cstrs
  have h_no_sll : Main[62] = 0 := sop_2 eq_sllw
  -- Open the iff_poly.
  change List.Forall SP1Constraint.toProp (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨h_msb_a1, _cpu, _alu, _one_of_ops,
           _b_sll, _b_sllw,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
           h_su160, _b_su160, h_su161, _b_su161, h_su162, _b_su162, h_su163, _b_su163, one_of_su16s,
           eq_v01, eq_v012, eq_v0123,
           lt_ll0', lt_lh0', h_b0_dec, lt_ll1', lt_lh1', h_b1_dec,
           lt_ll2', lt_lh2', h_b2_dec, lt_ll3', lt_lh3', h_b3_dec,
           eq_lr0, eq_lr1, eq_lr2, eq_lr3, rest⟩ := cstrs
  have h_sum_ne : ¬ Main[62] + Main[63] = 0 := by
    intro hh; rw [hh] at h_real; exact zero_ne_one h_real
  have diff' := diff h_sum_ne
  have lt_ll0 := lt_ll0' h_sum_ne
  have lt_lh0 := lt_lh0' h_sum_ne
  have lt_ll1 := lt_ll1' h_sum_ne
  have lt_lh1 := lt_lh1' h_sum_ne
  -- Bridges
  have h_v1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_v0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_1_ne_0 : (1 : ZMod p) ≠ 0 := by
    intro h; rw [h] at h_v1_val; rw [h_v0_val] at h_v1_val; exact zero_ne_one h_v1_val
  -- Bridges to normalize Lean's `↑N` (Nat cast) form back to the OfNat literal form.
  -- The cb_sum_lt chain below uses these via `simp only [...] at *` to keep
  -- `Main[i] * 2` etc. consistent across hypothesis/goal across `rw [ZMod.val_add_of_lt]`.
  have h_2_cast : ((2 : ℕ) : ZMod p) = 2 := by push_cast; rfl
  have h_4_cast : ((4 : ℕ) : ZMod p) = 4 := by push_cast; rfl
  have h_8_cast : ((8 : ℕ) : ZMod p) = 8 := by push_cast; rfl
  have h_16_cast : ((16 : ℕ) : ZMod p) = 16 := by push_cast; rfl
  -- cb_sum bound (6-bit, mirror spec.sll_poly).
  have h_cb_sum_lt : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16
                       + Main[41] * 32).val < 64 := by
    have hcb0 : Main[36].val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb1 : Main[37].val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb2 : Main[38].val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb3 : Main[39].val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb4 : Main[40].val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb5 : Main[41].val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have h_v2 : (2 : ZMod p).val = 2 := val_2_zmod_p
    have h_v4 : (4 : ZMod p).val = 4 := val_4_zmod_p
    have h_v8 : (8 : ZMod p).val = 8 := val_8_zmod_p
    have h_v16 : (16 : ZMod p).val = 16 := val_16_zmod_p
    have h_v32 : (32 : ZMod p).val = 32 := val_32_zmod_p
    have h_m1 : (Main[37] * 2).val ≤ 2 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v2]; have := hcb1; omega
      · rw [h_v2]; have := hcb1; omega
    have h_m2 : (Main[38] * 4).val ≤ 4 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v4]; have := hcb2; omega
      · rw [h_v4]; have := hcb2; omega
    have h_m3 : (Main[39] * 8).val ≤ 8 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v8]; have := hcb3; omega
      · rw [h_v8]; have := hcb3; omega
    have h_m4 : (Main[40] * 16).val ≤ 16 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v16]; have := hcb4; omega
      · rw [h_v16]; have := hcb4; omega
    have h_m5 : (Main[41] * 32).val ≤ 32 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v32]; have := hcb5; omega
      · rw [h_v32]; have := hcb5; omega
    have h_s1 : (Main[36] + Main[37] * 2).val ≤ 3 := by
      rw [ZMod.val_add_of_lt]
      · have := hcb0; have := h_m1; omega
      · have := hcb0; have := h_m1; have := hp; omega
    have h_s2 : (Main[36] + Main[37] * 2 + Main[38] * 4).val ≤ 7 := by
      rw [ZMod.val_add_of_lt]
      all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
                 have := h_s1; have := h_m2; have := hp; omega)
    have h_s3 : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val ≤ 15 := by
      rw [ZMod.val_add_of_lt]
      all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
                 have := h_s2; have := h_m3; have := hp; omega)
    have h_s4 : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16).val ≤ 31 := by
      rw [ZMod.val_add_of_lt]
      all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
                 have := h_s3; have := h_m4; have := hp; omega)
    rw [ZMod.val_add_of_lt]
    all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
               have := h_s4; have := h_m5; have := hp; omega)
  -- is_mod_64_poly: c0.val % 64 = (cb_sum_6).val
  have h_c_mod_64 : Main[25].val % 64 = (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                                          + Main[40] * 16 + Main[41] * 32).val := by
    apply is_mod_64_poly (m := (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                                + Main[40] * 16 + Main[41] * 32 : ZMod p))
    · exact h_cb_sum_lt
    · exact c0_16
    · have h_v10 : (10 : ZMod p).val = 10 := by
        rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) from by push_cast; rfl]
        exact ZMod.val_natCast_of_lt (by omega)
      have h_diff_eq : ((Main[25] - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                          + Main[40] * 16 + Main[41] * 32)) * (64 : ZMod p)⁻¹).val < 1024 := by
        have := diff'; rw [h_v10] at this; convert this using 1
      exact h_diff_eq
  -- Project to c0.val % 32 = (cb_sum_5).val.
  have h_cb_sum_5_lt : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                         + Main[40] * 16).val ≤ 31 := by
    have hcb0 : Main[36].val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb1 : Main[37].val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb2 : Main[38].val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb3 : Main[39].val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb4 : Main[40].val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have h_v2 : (2 : ZMod p).val = 2 := val_2_zmod_p
    have h_v4 : (4 : ZMod p).val = 4 := val_4_zmod_p
    have h_v8 : (8 : ZMod p).val = 8 := val_8_zmod_p
    have h_v16 : (16 : ZMod p).val = 16 := val_16_zmod_p
    have h_m1 : (Main[37] * 2).val ≤ 2 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v2]; have := hcb1; omega
      · rw [h_v2]; have := hcb1; omega
    have h_m2 : (Main[38] * 4).val ≤ 4 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v4]; have := hcb2; omega
      · rw [h_v4]; have := hcb2; omega
    have h_m3 : (Main[39] * 8).val ≤ 8 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v8]; have := hcb3; omega
      · rw [h_v8]; have := hcb3; omega
    have h_m4 : (Main[40] * 16).val ≤ 16 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v16]; have := hcb4; omega
      · rw [h_v16]; have := hcb4; omega
    have h_s1 : (Main[36] + Main[37] * 2).val ≤ 3 := by
      rw [ZMod.val_add_of_lt]
      · have := hcb0; have := h_m1; omega
      · have := hcb0; have := h_m1; have := hp; omega
    have h_s2 : (Main[36] + Main[37] * 2 + Main[38] * 4).val ≤ 7 := by
      rw [ZMod.val_add_of_lt]
      all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
                 have := h_s1; have := h_m2; have := hp; omega)
    have h_s3 : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val ≤ 15 := by
      rw [ZMod.val_add_of_lt]
      all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
                 have := h_s2; have := h_m3; have := hp; omega)
    rw [ZMod.val_add_of_lt]
    all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
               have := h_s3; have := h_m4; have := hp; omega)
  have h_cb5_val : (Main[41] * 32).val = 0 ∨ (Main[41] * 32).val = 32 := by
    rcases b_cb5 with h | h
    · left; rw [h, zero_mul]; exact h_v0_val
    · right
      rw [h, one_mul]
      rw [show (32 : ZMod p) = ((32 : ℕ) : ZMod p) from by push_cast; rfl]
      exact ZMod.val_natCast_of_lt (by omega)
  have h_cb_sum_split : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16
                          + Main[41] * 32).val
                      = (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                          + Main[40] * 16).val + (Main[41] * 32).val := by
    apply ZMod.val_add_of_lt
    simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
    rcases h_cb5_val with h | h
    · rw [h]; have := h_cb_sum_5_lt; have := hp; omega
    · rw [h]; have := h_cb_sum_5_lt; have := hp; omega
  have h_c_mod_32 : Main[25].val % 32 = (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                                          + Main[40] * 16).val := by
    have : Main[25].val % 32 = (Main[25].val % 64) % 32 := by omega
    rw [this, h_c_mod_64, h_cb_sum_split]
    rcases h_cb5_val with h | h
    · rw [h]; have := h_cb_sum_5_lt; omega
    · rw [h]; have := h_cb_sum_5_lt; omega
  -- Resolve w_*' and h_a2_eq, h_a3_eq.
  have h_sllw_ne_0 : Main[63] ≠ 0 := by rw [eq_sllw]; exact h_1_ne_0
  -- Drop Main[62] from h_su16i selectors (Main[62] = 0 substitution).
  rw [h_no_sll] at h_su160 h_su161 h_su162 h_su163
  simp only [mul_zero, add_zero] at h_su160 h_su161 h_su162 h_su163
  have h_su_sum : Main[45] + Main[46] + Main[47] + Main[48] = 1 := one_of_su16s.resolve_left h_sum_ne
  have h_47_eq : Main[47] = 0 := by
    rcases h_su162 with h | h
    · exact h
    · exfalso
      rcases b_cb4 with h4 | h4
      · rw [h4] at h; have : (2 : ZMod p) = 0 := by linear_combination -h
        exact val_2_ne_zero this
      · rw [h4] at h; have : (1 : ZMod p) = 0 := by linear_combination -h
        exact h_1_ne_0 this
  have h_48_eq : Main[48] = 0 := by
    rcases h_su163 with h | h
    · exact h
    · exfalso
      rcases b_cb4 with h4 | h4
      · rw [h4] at h; have : (3 : ZMod p) = 0 := by linear_combination -h
        exact val_3_ne_zero this
      · rw [h4] at h; have : (2 : ZMod p) = 0 := by linear_combination -h
        exact val_2_ne_zero this
  have h_su45_46_sum : Main[45] + Main[46] = 1 := by
    have := h_su_sum; rw [h_47_eq, h_48_eq] at this; linear_combination this
  -- Extract w_00..w_05 from rest.
  obtain ⟨_nw_00, _nw_01, _nw_02, _nw_03, _nw_04, _nw_05, _nw_06, _nw_07, _nw_08, _nw_09,
          _nw_10, _nw_11, _nw_12, _nw_13, _nw_14, _nw_15,
          w_00, w_01, w_02, w_03, w_04, w_05, _eq_m64, _h_M13⟩ := rest
  have w_00' := w_00.resolve_left h_sllw_ne_0
  have w_01' := w_01.resolve_left h_sllw_ne_0
  have w_02' := w_02.resolve_left h_sllw_ne_0
  have w_03' := w_03.resolve_left h_sllw_ne_0
  have h_a2_eq := w_04.resolve_left h_sllw_ne_0
  have h_a3_eq := w_05.resolve_left h_sllw_ne_0
  -- Substitute eq_sllw in h_msb_a1 (replace Main[63] with 1).
  rw [eq_sllw] at h_msb_a1
  -- Goal manipulation: avoid `change`. Use simp + explicit rfl-rewrites for Word.low_poly.
  simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly,
    LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
  rw [show Word.low_poly (#v[Main[15], Main[16], Main[17], Main[18]] : Word (ZMod p))
        = #v[Main[15], Main[16]] from rfl,
      show Word.low_poly (#v[Main[25], Main[26], Main[27], Main[28]] : Word (ZMod p))
        = #v[Main[25], Main[26]] from rfl]
  -- Dispatch on cb4.
  rcases b_cb4 with hcb4 | hcb4
  · exact spec.sllw_poly_cb4_zero Main
      b0_16 b1_16 c0_16 c1_16 b_cb0 b_cb1 b_cb2 b_cb3 hcb4
      h_su161 h_su45_46_sum
      eq_v01 eq_v012 eq_v0123
      lt_ll0 lt_lh0 lt_ll1 lt_lh1
      h_b0_dec h_b1_dec
      eq_lr0 eq_lr1
      w_00' w_01' h_a2_eq h_a3_eq h_msb_a1 h_c_mod_32
  · exact spec.sllw_poly_cb4_one Main
      b0_16 b1_16 c0_16 c1_16 b_cb0 b_cb1 b_cb2 b_cb3 hcb4
      h_su160 h_su45_46_sum
      eq_v01 eq_v012 eq_v0123
      lt_ll0 lt_lh0 lt_ll1 lt_lh1
      h_b0_dec h_b1_dec
      eq_lr0
      w_02' w_03' h_a2_eq h_a3_eq h_msb_a1 h_c_mod_32

lemma spec.slliw_poly (Main : Vector (ZMod p) 65) (h : is_slliw_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SLLW := by
  -- Clone of spec.sllw_poly's outer; both proofs share the same branch lemmas
  -- (they only consume the SLLW opcode flag, not the imm flag).
  intro cstrs
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨eq_slliw, _eq_imm⟩ := h
  have h_real := is_real_eq_one_of_sllw Main cstrs eq_slliw
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  obtain ⟨b0_16, b1_16, _b2_16, _b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨c0_16, c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  obtain ⟨_sop_1, sop_2⟩ := single_op_poly Main cstrs
  have h_no_sll : Main[62] = 0 := sop_2 eq_slliw
  change List.Forall SP1Constraint.toProp (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨h_msb_a1, _cpu, _alu, _one_of_ops,
           _b_sll, _b_sllw,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
           h_su160, _b_su160, h_su161, _b_su161, h_su162, _b_su162, h_su163, _b_su163, one_of_su16s,
           eq_v01, eq_v012, eq_v0123,
           lt_ll0', lt_lh0', h_b0_dec, lt_ll1', lt_lh1', h_b1_dec,
           lt_ll2', lt_lh2', h_b2_dec, lt_ll3', lt_lh3', h_b3_dec,
           eq_lr0, eq_lr1, eq_lr2, eq_lr3, rest⟩ := cstrs
  have h_sum_ne : ¬ Main[62] + Main[63] = 0 := by
    intro hh; rw [hh] at h_real; exact zero_ne_one h_real
  have diff' := diff h_sum_ne
  have lt_ll0 := lt_ll0' h_sum_ne
  have lt_lh0 := lt_lh0' h_sum_ne
  have lt_ll1 := lt_ll1' h_sum_ne
  have lt_lh1 := lt_lh1' h_sum_ne
  have h_v1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_v0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_1_ne_0 : (1 : ZMod p) ≠ 0 := by
    intro h; rw [h] at h_v1_val; rw [h_v0_val] at h_v1_val; exact zero_ne_one h_v1_val
  -- Cast-normalization bridges (see spec.sllw_poly).
  have h_2_cast : ((2 : ℕ) : ZMod p) = 2 := by push_cast; rfl
  have h_4_cast : ((4 : ℕ) : ZMod p) = 4 := by push_cast; rfl
  have h_8_cast : ((8 : ℕ) : ZMod p) = 8 := by push_cast; rfl
  have h_16_cast : ((16 : ℕ) : ZMod p) = 16 := by push_cast; rfl
  -- cb_sum bound (6-bit).
  have h_cb_sum_lt : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16
                       + Main[41] * 32).val < 64 := by
    have hcb0 : Main[36].val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb1 : Main[37].val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb2 : Main[38].val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb3 : Main[39].val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb4 : Main[40].val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb5 : Main[41].val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have h_v2 : (2 : ZMod p).val = 2 := val_2_zmod_p
    have h_v4 : (4 : ZMod p).val = 4 := val_4_zmod_p
    have h_v8 : (8 : ZMod p).val = 8 := val_8_zmod_p
    have h_v16 : (16 : ZMod p).val = 16 := val_16_zmod_p
    have h_v32 : (32 : ZMod p).val = 32 := val_32_zmod_p
    have h_m1 : (Main[37] * 2).val ≤ 2 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v2]; have := hcb1; omega
      · rw [h_v2]; have := hcb1; omega
    have h_m2 : (Main[38] * 4).val ≤ 4 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v4]; have := hcb2; omega
      · rw [h_v4]; have := hcb2; omega
    have h_m3 : (Main[39] * 8).val ≤ 8 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v8]; have := hcb3; omega
      · rw [h_v8]; have := hcb3; omega
    have h_m4 : (Main[40] * 16).val ≤ 16 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v16]; have := hcb4; omega
      · rw [h_v16]; have := hcb4; omega
    have h_m5 : (Main[41] * 32).val ≤ 32 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v32]; have := hcb5; omega
      · rw [h_v32]; have := hcb5; omega
    have h_s1 : (Main[36] + Main[37] * 2).val ≤ 3 := by
      rw [ZMod.val_add_of_lt]
      · have := hcb0; have := h_m1; omega
      · have := hcb0; have := h_m1; have := hp; omega
    have h_s2 : (Main[36] + Main[37] * 2 + Main[38] * 4).val ≤ 7 := by
      rw [ZMod.val_add_of_lt]
      all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
                 have := h_s1; have := h_m2; have := hp; omega)
    have h_s3 : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val ≤ 15 := by
      rw [ZMod.val_add_of_lt]
      all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
                 have := h_s2; have := h_m3; have := hp; omega)
    have h_s4 : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16).val ≤ 31 := by
      rw [ZMod.val_add_of_lt]
      all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
                 have := h_s3; have := h_m4; have := hp; omega)
    rw [ZMod.val_add_of_lt]
    all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
               have := h_s4; have := h_m5; have := hp; omega)
  -- is_mod_64_poly: c0.val % 64 = (cb_sum_6).val
  have h_c_mod_64 : Main[25].val % 64 = (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                                          + Main[40] * 16 + Main[41] * 32).val := by
    apply is_mod_64_poly (m := (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                                + Main[40] * 16 + Main[41] * 32 : ZMod p))
    · exact h_cb_sum_lt
    · exact c0_16
    · have h_v10 : (10 : ZMod p).val = 10 := by
        rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) from by push_cast; rfl]
        exact ZMod.val_natCast_of_lt (by omega)
      have h_diff_eq : ((Main[25] - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                          + Main[40] * 16 + Main[41] * 32)) * (64 : ZMod p)⁻¹).val < 1024 := by
        have := diff'; rw [h_v10] at this; convert this using 1
      exact h_diff_eq
  -- 5-bit cb sum bound (for % 32).
  have h_cb_sum_5_lt : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                         + Main[40] * 16).val ≤ 31 := by
    have hcb0 : Main[36].val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb1 : Main[37].val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb2 : Main[38].val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb3 : Main[39].val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have hcb4 : Main[40].val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h]
                                       · rw [h_v0_val]; omega
                                       · rw [h_v1_val]
    have h_v2 : (2 : ZMod p).val = 2 := val_2_zmod_p
    have h_v4 : (4 : ZMod p).val = 4 := val_4_zmod_p
    have h_v8 : (8 : ZMod p).val = 8 := val_8_zmod_p
    have h_v16 : (16 : ZMod p).val = 16 := val_16_zmod_p
    have h_m1 : (Main[37] * 2).val ≤ 2 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v2]; have := hcb1; omega
      · rw [h_v2]; have := hcb1; omega
    have h_m2 : (Main[38] * 4).val ≤ 4 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v4]; have := hcb2; omega
      · rw [h_v4]; have := hcb2; omega
    have h_m3 : (Main[39] * 8).val ≤ 8 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v8]; have := hcb3; omega
      · rw [h_v8]; have := hcb3; omega
    have h_m4 : (Main[40] * 16).val ≤ 16 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v16]; have := hcb4; omega
      · rw [h_v16]; have := hcb4; omega
    have h_s1 : (Main[36] + Main[37] * 2).val ≤ 3 := by
      rw [ZMod.val_add_of_lt]
      · have := hcb0; have := h_m1; omega
      · have := hcb0; have := h_m1; have := hp; omega
    have h_s2 : (Main[36] + Main[37] * 2 + Main[38] * 4).val ≤ 7 := by
      rw [ZMod.val_add_of_lt]
      all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
                 have := h_s1; have := h_m2; have := hp; omega)
    have h_s3 : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val ≤ 15 := by
      rw [ZMod.val_add_of_lt]
      all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
                 have := h_s2; have := h_m3; have := hp; omega)
    rw [ZMod.val_add_of_lt]
    all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
               have := h_s3; have := h_m4; have := hp; omega)
  have h_cb5_val : (Main[41] * 32).val = 0 ∨ (Main[41] * 32).val = 32 := by
    rcases b_cb5 with h | h
    · left; rw [h, zero_mul]; exact h_v0_val
    · right
      rw [h, one_mul]
      rw [show (32 : ZMod p) = ((32 : ℕ) : ZMod p) from by push_cast; rfl]
      exact ZMod.val_natCast_of_lt (by omega)
  have h_cb_sum_split : (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16
                          + Main[41] * 32).val
                      = (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                          + Main[40] * 16).val + (Main[41] * 32).val := by
    apply ZMod.val_add_of_lt
    simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
    rcases h_cb5_val with h | h
    · rw [h]; have := h_cb_sum_5_lt; have := hp; omega
    · rw [h]; have := h_cb_sum_5_lt; have := hp; omega
  have h_c_mod_32 : Main[25].val % 32 = (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8
                                          + Main[40] * 16).val := by
    have : Main[25].val % 32 = (Main[25].val % 64) % 32 := by omega
    rw [this, h_c_mod_64, h_cb_sum_split]
    rcases h_cb5_val with h | h
    · rw [h]; have := h_cb_sum_5_lt; omega
    · rw [h]; have := h_cb_sum_5_lt; omega
  have h_sllw_ne_0 : Main[63] ≠ 0 := by rw [eq_slliw]; exact h_1_ne_0
  rw [h_no_sll] at h_su160 h_su161 h_su162 h_su163
  simp only [mul_zero, add_zero] at h_su160 h_su161 h_su162 h_su163
  have h_su_sum : Main[45] + Main[46] + Main[47] + Main[48] = 1 := one_of_su16s.resolve_left h_sum_ne
  have h_47_eq : Main[47] = 0 := by
    rcases h_su162 with h | h
    · exact h
    · exfalso
      rcases b_cb4 with h4 | h4
      · rw [h4] at h; have : (2 : ZMod p) = 0 := by linear_combination -h
        exact val_2_ne_zero this
      · rw [h4] at h; have : (1 : ZMod p) = 0 := by linear_combination -h
        exact h_1_ne_0 this
  have h_48_eq : Main[48] = 0 := by
    rcases h_su163 with h | h
    · exact h
    · exfalso
      rcases b_cb4 with h4 | h4
      · rw [h4] at h; have : (3 : ZMod p) = 0 := by linear_combination -h
        exact val_3_ne_zero this
      · rw [h4] at h; have : (2 : ZMod p) = 0 := by linear_combination -h
        exact val_2_ne_zero this
  have h_su45_46_sum : Main[45] + Main[46] = 1 := by
    have := h_su_sum; rw [h_47_eq, h_48_eq] at this; linear_combination this
  obtain ⟨_nw_00, _nw_01, _nw_02, _nw_03, _nw_04, _nw_05, _nw_06, _nw_07, _nw_08, _nw_09,
          _nw_10, _nw_11, _nw_12, _nw_13, _nw_14, _nw_15,
          w_00, w_01, w_02, w_03, w_04, w_05, _eq_m64, _h_M13⟩ := rest
  have w_00' := w_00.resolve_left h_sllw_ne_0
  have w_01' := w_01.resolve_left h_sllw_ne_0
  have w_02' := w_02.resolve_left h_sllw_ne_0
  have w_03' := w_03.resolve_left h_sllw_ne_0
  have h_a2_eq := w_04.resolve_left h_sllw_ne_0
  have h_a3_eq := w_05.resolve_left h_sllw_ne_0
  rw [eq_slliw] at h_msb_a1
  simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly,
    LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
  rw [show Word.low_poly (#v[Main[15], Main[16], Main[17], Main[18]] : Word (ZMod p))
        = #v[Main[15], Main[16]] from rfl,
      show Word.low_poly (#v[Main[25], Main[26], Main[27], Main[28]] : Word (ZMod p))
        = #v[Main[25], Main[26]] from rfl]
  rcases b_cb4 with hcb4 | hcb4
  · exact spec.sllw_poly_cb4_zero Main
      b0_16 b1_16 c0_16 c1_16 b_cb0 b_cb1 b_cb2 b_cb3 hcb4
      h_su161 h_su45_46_sum
      eq_v01 eq_v012 eq_v0123
      lt_ll0 lt_lh0 lt_ll1 lt_lh1
      h_b0_dec h_b1_dec
      eq_lr0 eq_lr1
      w_00' w_01' h_a2_eq h_a3_eq h_msb_a1 h_c_mod_32
  · exact spec.sllw_poly_cb4_one Main
      b0_16 b1_16 c0_16 c1_16 b_cb0 b_cb1 b_cb2 b_cb3 hcb4
      h_su160 h_su45_46_sum
      eq_v01 eq_v012 eq_v0123
      lt_ll0 lt_lh0 lt_ll1 lt_lh1
      h_b0_dec h_b1_dec
      eq_lr0
      w_02' w_03' h_a2_eq h_a3_eq h_msb_a1 h_c_mod_32

end sllw_poly

end ShiftLeft
