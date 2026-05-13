import SP1Chips.ShiftLeft.Common

namespace ShiftLeft

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 65)

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
    (eq_sllw : Main[63] = 1) (h_no_sll : Main[62] = 0)
    (b0_16 : Main[15].val < 65536) (b1_16 : Main[16].val < 65536)
    (c0_16 : Main[25].val < 65536) (c1_16 : Main[26].val < 65536)
    (b_cb0 : Main[36] = 0 ∨ Main[36] = 1)
    (b_cb1 : Main[37] = 0 ∨ Main[37] = 1)
    (b_cb2 : Main[38] = 0 ∨ Main[38] = 1)
    (b_cb3 : Main[39] = 0 ∨ Main[39] = 1)
    (hcb4 : Main[40] = 0)
    (h_su161 : Main[46] = 0 ∨ Main[40] + Main[41] * 2 * 0 = 1)
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
    (lt_ll2 : Main[51].val < 2 ^ ((16 : ZMod p) -
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val)
    (lt_lh2 : Main[55].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 : ZMod p).val)
    (lt_ll3 : Main[52].val < 2 ^ ((16 : ZMod p) -
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val)
    (lt_lh3 : Main[56].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 : ZMod p).val)
    (h_b0_dec : Main[15] * Main[44] = Main[53] * 65536 + Main[49] * Main[44])
    (h_b1_dec : Main[16] * Main[44] = Main[54] * 65536 + Main[50] * Main[44])
    (h_b2_dec : Main[17] * Main[44] = Main[55] * 65536 + Main[51] * Main[44])
    (h_b3_dec : Main[18] * Main[44] = Main[56] * 65536 + Main[52] * Main[44])
    (eq_lr0 : Main[57] = Main[49] * Main[44])
    (eq_lr1 : Main[58] = Main[50] * Main[44] + Main[53])
    (eq_lr2 : Main[59] = Main[51] * Main[44] + Main[54])
    (eq_lr3 : Main[60] = Main[52] * Main[44] + Main[55])
    (w_00' : Main[45] = 0 ∨ Main[32] = Main[57])
    (w_01' : Main[45] = 0 ∨ Main[33] = Main[58])
    (h_a2_eq : Main[61] * 65535 = Main[34])
    (h_a3_eq : Main[61] * 65535 = Main[35])
    (h_msb_a1 : List.Forall SP1Constraint.toProp_poly
      (U16MSBOperation.constraints Main[33] { msb := Main[61] } 1))
    (h_c_mod_32 : Main[25].val % 32 =
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16).val) :
    Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
      BitVec.signExtend 64 (HWord.toBitVec32_poly #v[Main[15], Main[16]] <<<
        BitVec.setWidth 5 (HWord.toBitVec32_poly #v[Main[25], Main[26]])) := by
  -- TODO: derive h_46_eq, h_45_eq, h_a0_eq, h_a1_eq;
  -- substitute in goal + h_msb_a1; 16-way cb0..3 split + sllw_subcase_cb4_zero apps.
  sorry

/-- Mirror of `spec.sllw_poly_cb4_zero` for the `cb4 = 1` (byte_shift=1) branch.
a0 substitutes to 0, a1 substitutes to lr0 = ll0 * v0123. -/
private lemma spec.sllw_poly_cb4_one (Main : Vector (ZMod p) 65)
    (eq_sllw : Main[63] = 1) (h_no_sll : Main[62] = 0)
    (b0_16 : Main[15].val < 65536) (b1_16 : Main[16].val < 65536)
    (c0_16 : Main[25].val < 65536) (c1_16 : Main[26].val < 65536)
    (b_cb0 : Main[36] = 0 ∨ Main[36] = 1)
    (b_cb1 : Main[37] = 0 ∨ Main[37] = 1)
    (b_cb2 : Main[38] = 0 ∨ Main[38] = 1)
    (b_cb3 : Main[39] = 0 ∨ Main[39] = 1)
    (hcb4 : Main[40] = 1)
    (h_su160 : Main[45] = 0 ∨ Main[40] + Main[41] * 2 * 0 = 0)
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
    (lt_ll2 : Main[51].val < 2 ^ ((16 : ZMod p) -
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val)
    (lt_lh2 : Main[55].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 : ZMod p).val)
    (lt_ll3 : Main[52].val < 2 ^ ((16 : ZMod p) -
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val)
    (lt_lh3 : Main[56].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 : ZMod p).val)
    (h_b0_dec : Main[15] * Main[44] = Main[53] * 65536 + Main[49] * Main[44])
    (h_b1_dec : Main[16] * Main[44] = Main[54] * 65536 + Main[50] * Main[44])
    (h_b2_dec : Main[17] * Main[44] = Main[55] * 65536 + Main[51] * Main[44])
    (h_b3_dec : Main[18] * Main[44] = Main[56] * 65536 + Main[52] * Main[44])
    (eq_lr0 : Main[57] = Main[49] * Main[44])
    (eq_lr1 : Main[58] = Main[50] * Main[44] + Main[53])
    (eq_lr2 : Main[59] = Main[51] * Main[44] + Main[54])
    (eq_lr3 : Main[60] = Main[52] * Main[44] + Main[55])
    (w_02' : Main[46] = 0 ∨ Main[32] = 0)
    (w_03' : Main[46] = 0 ∨ Main[33] = Main[57])
    (h_a2_eq : Main[61] * 65535 = Main[34])
    (h_a3_eq : Main[61] * 65535 = Main[35])
    (h_msb_a1 : List.Forall SP1Constraint.toProp_poly
      (U16MSBOperation.constraints Main[33] { msb := Main[61] } 1))
    (h_c_mod_32 : Main[25].val % 32 =
      (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16).val) :
    Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
      BitVec.signExtend 64 (HWord.toBitVec32_poly #v[Main[15], Main[16]] <<<
        BitVec.setWidth 5 (HWord.toBitVec32_poly #v[Main[25], Main[26]])) := by
  -- TODO: derive h_45_eq, h_46_eq, h_a0_eq (a0 = 0), h_a1_eq (a1 = lr0);
  -- substitute in goal + h_msb_a1; 16-way cb0..3 split + sllw_subcase_cb4_one apps.
  sorry

/-- Outer `spec.sllw_poly`: destructure cstrs, derive bounds, h_c_mod_32, w_*'
resolution; manually unfold `Word.low_poly` (avoiding the expensive `change`
tactic from the failed inline approach); dispatch on `cb4` to the two branch
lemmas above. -/
lemma spec.sllw_poly (Main : Vector (ZMod p) 65) (h : is_sllw_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SLLW := by
  -- TODO: outer setup (~250 lines) replicating the gathered facts the branch
  -- lemmas need, then:
  --   simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly,
  --     LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
  --   rw [show #v[Main[15], Main[16], Main[17], Main[18]].low_poly = #v[Main[15], Main[16]] from rfl,
  --       show #v[Main[25], Main[26], Main[27], Main[28]].low_poly = #v[Main[25], Main[26]] from rfl]
  --   rcases b_cb4 with hcb4 | hcb4
  --   · exact spec.sllw_poly_cb4_zero ... (35 args)
  --   · exact spec.sllw_poly_cb4_one  ... (35 args)
  sorry

lemma spec.slliw_poly (Main : Vector (ZMod p) 65) (h : is_slliw_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SLLW := by
  -- TODO: structurally same as spec.sllw_poly but with imm_zeros substitution
  -- (Main[26..28] = 0, Main[21] = Main[25] from bounds_poly's imm = 1 path).
  -- Branch lemmas should be reusable once Main[26..28] are substituted away.
  sorry

end sllw_poly

section sllw

lemma spec.sllw (h : is_sllw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLLW
  := by
    have _ := h
    intro cstrs
    obtain ⟨eq_sllw, eq_imm⟩ := h
    have ⟨h0, h1, h2, hpc, is_U64_b, is_U64_c, h3, h4⟩ := bounds Main cstrs (sllw_real Main eq_sllw)
    clear h0 h1 h2 h3 h4
    obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨c0_16, c1_16, c2_16, c3_16⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨sop_1, sop_2⟩ := single_op Main cstrs
    rw [allHold_constraints_iff] at cstrs
    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set cb0 := Main[36]
    set cb1 := Main[37]
    set cb2 := Main[38]
    set cb3 := Main[39]
    set cb4 := Main[40]
    set cb5 := Main[41]
    set v01 := Main[42]
    set v012 := Main[43]
    set v0123 := Main[44]
    set su160 := Main[45]
    set su161 := Main[46]
    set su162 := Main[47]
    set su163 := Main[48]
    set ll0 := Main[49]
    set ll1 := Main[50]
    set ll2 := Main[51]
    set ll3 := Main[52]
    set hl0 := Main[53]
    set hl1 := Main[54]
    set hl2 := Main[55]
    set hl3 := Main[56]
    set lr0 := Main[57]
    set lr1 := Main[58]
    set lr2 := Main[59]
    set lr3 := Main[60]
    set msb := Main[61]
    set sll := Main[62]
    set sllw := Main[63]
    obtain ⟨h_msb_a1, cpu, alu, one_of_ops,
             b_sll, b_sllw,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
             lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05,
             eq_m64⟩ := cstrs
    clear cpu alu
    simp_all
    have is_U32_b : HWord.isU32 #v[ b0, b1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_c : HWord.isU32 #v[ c0, c1 ] := by apply HWord.isU32_of_cases <;> assumption
    have : ((Word.low #v[c0, c1, c2, c3]).toBitVec32.toNat % 32) = c0.val % 32 := by
      simp [Word.low, HWord.toBitVec32_toNat is_U32_c, HWord.toNat];
      omega
    rw [this]; clear this
    simp [Word.low]
    have c0_mod_64 : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · omega
      · exact diff
    clear diff
    have : c0.val % 32 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
      trans (c0.val % 64) % 32
      · omega
      · rw [c0_mod_64]
        clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
    clear c0_mod_64
    have h_isU32_a : HWord.isU32 #v[ a0, a1 ] := by
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
      rcases b_cb3 <;> rcases b_cb4 <;> simp_all <;>
      apply HWord.isU32_of_cases <;> simp_all [Fin.val_add, Fin.val_mul] <;>
      (repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]) <;>
      omega
    have ⟨_, _⟩ := HWord.lt_cases_of_isU32 h_isU32_a
    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      rw [← w_04] at *
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      · unfold HWord.isNegative; split_ifs <;> simp_all; omega
      · congr; rw [HWord.isNegative_msb h_isU32_a]
    · suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = (HWord.toBitVec32 #v[b0, b1] <<< (c0.val % 32))
      · rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      · rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        rw [HWord.toBitVec32_toNat h_isU32_a, HWord.toBitVec32_toNat is_U32_b]
        rw [this]; clear this h_a3
        cases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
        rcases b_cb3 <;> rcases b_cb4 <;> simp_all
        all_goals {
          (try apply cancel_mul_65536 (by simp) at h_b0_dec)
          (try apply cancel_mul_65536 (by simp) at h_b1_dec)
          (try apply cancel_mul_65536 (by simp) at h_b2_dec)
          (try apply cancel_mul_65536 (by simp) at h_b3_dec)
          simp_all [HWord.toNat]
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          omega
        }

end sllw

section slliw

lemma spec.slliw (h : is_slliw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLLW
  := by
    have _ := h
    intro cstrs
    obtain ⟨eq_sllw, eq_imm⟩ := h
    have ⟨h0, h1, h2, hpc, is_U64_b, is_U64_c, imm_zeros, h3⟩ := bounds Main cstrs (sllw_real Main eq_sllw)
    clear h0 h1 h2 h3
    rw [eq_imm] at imm_zeros; simp_all
    obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨eq_c0, eq_c1, eq_c2, eq_c3, lt_c0, h0⟩ := imm_zeros
    obtain ⟨sop_1, sop_2⟩ := single_op Main cstrs
    rw [allHold_constraints_iff] at cstrs
    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set cb0 := Main[36]
    set cb1 := Main[37]
    set cb2 := Main[38]
    set cb3 := Main[39]
    set cb4 := Main[40]
    set cb5 := Main[41]
    set v01 := Main[42]
    set v012 := Main[43]
    set v0123 := Main[44]
    set su160 := Main[45]
    set su161 := Main[46]
    set su162 := Main[47]
    set su163 := Main[48]
    set ll0 := Main[49]
    set ll1 := Main[50]
    set ll2 := Main[51]
    set ll3 := Main[52]
    set hl0 := Main[53]
    set hl1 := Main[54]
    set hl2 := Main[55]
    set hl3 := Main[56]
    set lr0 := Main[57]
    set lr1 := Main[58]
    set lr2 := Main[59]
    set lr3 := Main[60]
    set msb := Main[61]
    set sll := Main[62]
    set sllw := Main[63]
    obtain ⟨h_msb_a1, cpu, alu, one_of_ops,
             b_sll, b_sllw,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
             lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05,
             eq_m64⟩ := cstrs
    clear cpu alu
    simp_all
    have is_U32_b : HWord.isU32 #v[ b0, b1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_c : HWord.isU32 #v[ c0, 0 ] := by apply HWord.isU32_of_cases <;> simp; omega
    have : ((Word.low #v[c0, 0, 0, 0]).toBitVec32.toNat % 32) = c0.val % 32 := by
      simp [Word.low, HWord.toBitVec32_toNat is_U32_c, HWord.toNat]
    rw [this]; clear this
    simp [Word.low]
    have c0_mod_64 : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · omega
      · exact diff
    clear diff
    have : c0.val % 32 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
      trans (c0.val % 64) % 32
      · omega
      · rw [c0_mod_64]
        clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
    clear c0_mod_64
    have h_isU32_a : HWord.isU32 #v[ a0, a1 ] := by
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
      rcases b_cb3 <;> rcases b_cb4 <;> simp_all <;>
      apply HWord.isU32_of_cases <;> simp_all [Fin.val_add, Fin.val_mul] <;>
      (repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]) <;>
      omega
    have ⟨_, _⟩ := HWord.lt_cases_of_isU32 h_isU32_a
    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      rw [← w_04] at *
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      · unfold HWord.isNegative; split_ifs <;> simp_all; omega
      · congr; rw [HWord.isNegative_msb h_isU32_a]
    · suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = (HWord.toBitVec32 #v[b0, b1] <<< (c0.val % 32))
      · rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      · rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        rw [HWord.toBitVec32_toNat h_isU32_a, HWord.toBitVec32_toNat is_U32_b]
        rw [this]; clear this h_a3
        cases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
        rcases b_cb3 <;> rcases b_cb4 <;> simp_all
        all_goals {
          (try apply cancel_mul_65536 (by simp) at h_b0_dec)
          (try apply cancel_mul_65536 (by simp) at h_b1_dec)
          (try apply cancel_mul_65536 (by simp) at h_b2_dec)
          (try apply cancel_mul_65536 (by simp) at h_b3_dec)
          simp_all [HWord.toNat]
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          omega
        }

end slliw

end ShiftLeft
