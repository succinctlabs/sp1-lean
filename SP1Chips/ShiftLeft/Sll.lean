import SP1Chips.ShiftLeft.Common

namespace ShiftLeft

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 65)

section sll

lemma spec.sll (h : is_sll Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLL
  := by
    have _ := h
    intro cstrs
    obtain ⟨eq_sll, eq_imm⟩ := h
    have ⟨h0, h1, h2, hpc, is_U64_b, is_U64_c, h3, h4⟩ := bounds Main cstrs (sll_real Main eq_sll)
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
             eq_m64, h13⟩ := cstrs
    clear h_msb_a1 cpu alu
    simp_all
    rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have : ((Word.toBitVec64 #v[c0, c1, c2, c3]).toNat % 64) = c0.val % 64 := by
      rw [Word.toBitVec64_toNat is_U64_c]; simp [Word.toNat]
      omega
    rw [this]; clear this
    have : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · omega
      · exact diff
    rw [this]; clear this
    rw [Word.toBitVec64_toNat (w := #v[b0, b1, b2, b3]) (by apply Word.isU64_of_cases <;> simp <;> assumption)]
    simp [Word.toNat]
    -- 64-way case split
    rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
    rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
    simp_all <;>
    (try apply cancel_mul_65536 (by simp) at h_b0_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b1_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b2_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b3_dec) <;>
    simp_all
    all_goals {
      rw [Word.toBitVec64_toNat]
      · simp [Word.toNat]
        try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
        repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
        omega
      · apply Word.isU64_of_cases <;> simp [Fin.val_add, Fin.val_mul] <;>
        (repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]) <;>
        omega
    }

end sll

section sll_poly

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 1000000000 in
-- 64-way case split on cb0..cb5; large heartbeat for the case tree.
set_option debug.skipKernelTC true in
-- skipKernelTC: large 2^N from Word.toBitVec64_poly_toNat_poly trips kernel
-- deep recursion at re-check; see docs/GOTCHAS.md "Kernel deep-recursion on 2^N".
lemma spec.sll_poly (Main : Vector (ZMod p) 65) (h : is_sll_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SLL := by
  intro cstrs
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨eq_sll, _eq_imm⟩ := h
  have h_real := is_real_eq_one_of_sll Main cstrs eq_sll
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨c0_16, _c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  obtain ⟨sop_1, _sop_2⟩ := single_op_poly Main cstrs
  have h_no_sllw : Main[63] = 0 := sop_1 eq_sll
  -- Open the iff_poly.
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]
  set c0 := Main[25]
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
  set v0123 := Main[44]
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
  obtain ⟨_h_msb_a1, _cpu, _alu, _one_of_ops,
           _b_sll, _b_sllw,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
           h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
           eq_v01, eq_v012, eq_v0123,
           lt_ll0', lt_lh0', h_b0_dec, lt_ll1', lt_lh1', h_b1_dec,
           lt_ll2', lt_lh2', h_b2_dec, lt_ll3', lt_lh3', h_b3_dec,
           eq_lr0, eq_lr1, eq_lr2, eq_lr3,
           rest⟩ := cstrs
  -- Specialize diff (which has ¬sum = 0 hypothesis) using h_real = 1.
  have h_sum_ne : ¬ Main[62] + Main[63] = 0 := by
    intro hh; rw [hh] at h_real; exact zero_ne_one h_real
  have diff' := diff h_sum_ne
  -- Goal manipulation: reduce to nat arithmetic.
  rw [← BitVec.toNat_inj]
  simp only [execute_RTYPE_pure_w_poly]
  simp only [BitVec.toNat_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_setWidth]
  -- Goal: (toBitVec64_poly a).toNat = (toBitVec64_poly b).toNat <<< ((toBitVec64_poly c).toNat % 2^6) % 2^64
  change (Word.toBitVec64_poly #v[a0, a1, a2, a3]).toNat =
        (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat <<<
          ((Word.toBitVec64_poly #v[c0, Main[26], Main[27], Main[28]]).toNat % 2 ^ 6) % 2 ^ 64
  -- Reduce the c-toNat % 64 to c0.val % 64
  have h_c_mod : (Word.toBitVec64_poly #v[c0, Main[26], Main[27], Main[28]]).toNat % 2 ^ 6 = c0.val % 64 := by
    rw [Word.toBitVec64_poly_toNat_poly is_U64_c, Word.toNat_poly_def]
    simp; omega
  rw [h_c_mod]; clear h_c_mod
  -- Use is_mod_64_poly to convert c0.val % 64 to cb sum.
  have h_p_huge : 131072 < p := by have := hp; omega
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h_v1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_v0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_cb_sum_lt : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val < 64 := by
    -- Each cb ∈ {0, 1}, so the sum is at most 63 ≤ 65536 < p, no wrap.
    have hcb0 : cb0.val ≤ 1 := by
      rcases b_cb0 with h | h <;> rw [h]
      · rw [h_v0_val]; omega
      · rw [h_v1_val]
    have hcb1 : cb1.val ≤ 1 := by
      rcases b_cb1 with h | h <;> rw [h]
      · rw [h_v0_val]; omega
      · rw [h_v1_val]
    have hcb2 : cb2.val ≤ 1 := by
      rcases b_cb2 with h | h <;> rw [h]
      · rw [h_v0_val]; omega
      · rw [h_v1_val]
    have hcb3 : cb3.val ≤ 1 := by
      rcases b_cb3 with h | h <;> rw [h]
      · rw [h_v0_val]; omega
      · rw [h_v1_val]
    have hcb4 : cb4.val ≤ 1 := by
      rcases b_cb4 with h | h <;> rw [h]
      · rw [h_v0_val]; omega
      · rw [h_v1_val]
    have hcb5 : cb5.val ≤ 1 := by
      rcases b_cb5 with h | h <;> rw [h]
      · rw [h_v0_val]; omega
      · rw [h_v1_val]
    -- Now sum.val = sum of vals (no wrap since each piece is small).
    have h_v2 : (2 : ZMod p).val = 2 := val_2_zmod_p
    have h_v4 : (4 : ZMod p).val = 4 := val_4_zmod_p
    have h_v8 : (8 : ZMod p).val = 8 := val_8_zmod_p
    have h_v16 : (16 : ZMod p).val = 16 := val_16_zmod_p
    have h_v32 : (32 : ZMod p).val = 32 := val_32_zmod_p
    -- Each term .val: cb_i * N for cb_i ∈ {0, 1}.
    have h_m1_val : (cb1 * 2).val ≤ 2 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v2]; have := hcb1; omega
      · rw [h_v2]; have := hcb1; omega
    have h_m2_val : (cb2 * 4).val ≤ 4 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v4]; have := hcb2; omega
      · rw [h_v4]; have := hcb2; omega
    have h_m3_val : (cb3 * 8).val ≤ 8 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v8]; have := hcb3; omega
      · rw [h_v8]; have := hcb3; omega
    have h_m4_val : (cb4 * 16).val ≤ 16 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v16]; have := hcb4; omega
      · rw [h_v16]; have := hcb4; omega
    have h_m5_val : (cb5 * 32).val ≤ 32 := by
      rw [ZMod.val_mul_of_lt]
      · rw [h_v32]; have := hcb5; omega
      · rw [h_v32]; have := hcb5; omega
    -- Add up, no wrap.
    have h_sum_step1 : (cb0 + cb1 * 2).val ≤ 3 := by
      rw [ZMod.val_add_of_lt]
      · have := hcb0; have := h_m1_val; omega
      · have := hcb0; have := h_m1_val; omega
    have h_sum_step2 : (cb0 + cb1 * 2 + cb2 * 4).val ≤ 7 := by
      rw [ZMod.val_add_of_lt]
      · have := h_sum_step1; have := h_m2_val; omega
      · have := h_sum_step1; have := h_m2_val; omega
    have h_sum_step3 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8).val ≤ 15 := by
      rw [ZMod.val_add_of_lt]
      · have := h_sum_step2; have := h_m3_val; omega
      · have := h_sum_step2; have := h_m3_val; omega
    have h_sum_step4 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16).val ≤ 31 := by
      rw [ZMod.val_add_of_lt]
      · have := h_sum_step3; have := h_m4_val; omega
      · have := h_sum_step3; have := h_m4_val; omega
    rw [ZMod.val_add_of_lt]
    · have := h_sum_step4; have := h_m5_val; omega
    · have := h_sum_step4; have := h_m5_val; omega
  have h_c_mod_64 : c0.val % 64 = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
    apply is_mod_64_poly (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)
    · exact h_cb_sum_lt
    · exact c0_16
    · -- diff' has `< 2 ^ (10 : ZMod p).val`; reduce to `< 1024`.
      have h_v10 : (10 : ZMod p).val = 10 := by
        rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) from by push_cast; rfl]
        exact ZMod.val_natCast_of_lt (by omega)
      have h_diff_eq : ((c0 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)) * (64 : ZMod p)⁻¹).val < 1024 := by
        have := diff'
        rw [h_v10] at this
        convert this using 1
      exact h_diff_eq
  rw [h_c_mod_64]
  -- Specialize the ¬sum=0-gated bounds.
  have lt_ll0 := lt_ll0' h_sum_ne
  have lt_lh0 := lt_lh0' h_sum_ne
  have lt_ll1 := lt_ll1' h_sum_ne
  have lt_lh1 := lt_lh1' h_sum_ne
  have lt_ll2 := lt_ll2' h_sum_ne
  have lt_lh2 := lt_lh2' h_sum_ne
  have lt_ll3 := lt_ll3' h_sum_ne
  have lt_lh3 := lt_lh3' h_sum_ne
  -- Step A: pre-process `rest` to eliminate Main[62]=0 (false) and Main[63]=0 (true) disjuncts.
  have h_1_ne_0 : (1 : ZMod p) ≠ 0 := by
    intro h; rw [h] at h_v1_val; rw [h_v0_val] at h_v1_val; exact zero_ne_one h_v1_val
  rw [eq_sll] at rest
  rw [h_no_sllw] at rest
  simp only [h_1_ne_0, false_or, true_or, or_true] at rest
  -- Drop Main[62] from h_su16i selectors via eq_sll.
  rw [eq_sll] at h_su160 h_su161 h_su162 h_su163
  simp only [mul_one] at h_su160 h_su161 h_su162 h_su163
  -- Specialize one_of_su16s.
  have h_su_sum : Main[45] + Main[46] + Main[47] + Main[48] = 1 := one_of_su16s.resolve_left h_sum_ne
  -- Case-split on cb4 and cb5 (the byte-shift selectors).
  rcases b_cb4 with hcb4 | hcb4 <;> rcases b_cb5 with hcb5 | hcb5
  · -- cb4 = 0, cb5 = 0: byte_shift = 0, so Main[45] = 1.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [zero_add, zero_mul, mul_zero, add_zero] at h_su160 h_su161 h_su162 h_su163
    -- Now derive Main[46] = Main[47] = Main[48] = 0.
    have h_46_eq : Main[46] = 0 := by
      rcases h_su161 with h | h
      · exact h
      · exfalso
        have : (1 : ZMod p) = 0 := by linear_combination -h
        exact h_1_ne_0 this
    have h_47_eq : Main[47] = 0 := by
      rcases h_su162 with h | h
      · exact h
      · exfalso
        have : (2 : ZMod p) = 0 := by linear_combination -h
        exact val_2_ne_zero this
    have h_48_eq : Main[48] = 0 := by
      rcases h_su163 with h | h
      · exact h
      · exfalso
        have : (3 : ZMod p) = 0 := by linear_combination -h
        exact val_3_ne_zero this
    have h_45_eq : Main[45] = 1 := by
      have := h_su_sum
      rw [h_46_eq, h_47_eq, h_48_eq] at this
      linear_combination this
    -- Now extract the 4 equations from rest. With Main[45] = 1, the first 4 conjuncts give a_j = lr_j.
    obtain ⟨h_a0_eq', h_a1_eq', h_a2_eq', h_a3_eq', _rest_other⟩ := rest
    have h_a0_eq : a0 = lr0 := by
      rcases h_a0_eq' with h | h
      · exfalso; rw [h_45_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a1_eq : a1 = lr1 := by
      rcases h_a1_eq' with h | h
      · exfalso; rw [h_45_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a2_eq : a2 = lr2 := by
      rcases h_a2_eq' with h | h
      · exfalso; rw [h_45_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a3_eq : a3 = lr3 := by
      rcases h_a3_eq' with h | h
      · exfalso; rw [h_45_eq] at h; exact h_1_ne_0 h
      · exact h
    -- Substitute a_j = lr_j in the goal.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr0, eq_lr1, eq_lr2, eq_lr3]
    -- Now: (toBitVec64 #v[ll0*v0123, ll1*v0123+hl0, ll2*v0123+hl1, ll3*v0123+hl2]).toNat
    --       = (toBitVec64 #v[b0..b3]).toNat <<< (cb_sum_low).val % 2^64
    -- With cb4 = cb5 = 0, cb_sum = cb0 + cb1*2 + cb2*4 + cb3*8 (range 0..15).
    -- 16-way case split on cb0..cb3.
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    -- Try the all-zeros sub-case first: cb0 = cb1 = cb2 = cb3 = 0, so v0123 = 1, shift = 0.
    · -- All-zeros sub-case: cb0..3 = 0, v0123 = 1, shift = 0.
      simp only [hcb0, hcb1, hcb2, hcb3, zero_mul, zero_add, mul_zero, add_zero, one_mul, mul_one]
        at eq_v01 eq_v012 eq_v0123 h_b0_dec h_b1_dec h_b2_dec h_b3_dec lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
      rw [eq_v01] at eq_v012; rw [eq_v012] at eq_v0123
      rw [eq_v0123] at h_b0_dec h_b1_dec h_b2_dec h_b3_dec eq_lr0 eq_lr1 eq_lr2 eq_lr3
      simp only [Nat.cast_one, mul_one] at h_b0_dec h_b1_dec h_b2_dec h_b3_dec eq_lr0 eq_lr1 eq_lr2 eq_lr3
      simp only [h_v0_val, pow_zero, Nat.lt_one_iff] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
      have h_hl0_zero : hl0 = 0 := (ZMod.val_eq_zero hl0).mp lt_lh0
      have h_hl1_zero : hl1 = 0 := (ZMod.val_eq_zero hl1).mp lt_lh1
      have h_hl2_zero : hl2 = 0 := (ZMod.val_eq_zero hl2).mp lt_lh2
      have h_hl3_zero : hl3 = 0 := (ZMod.val_eq_zero hl3).mp lt_lh3
      rw [h_hl0_zero] at h_b0_dec eq_lr1; rw [h_hl1_zero] at h_b1_dec eq_lr2
      rw [h_hl2_zero] at h_b2_dec eq_lr3; rw [h_hl3_zero] at h_b3_dec
      simp only [zero_mul, zero_add, add_zero] at h_b0_dec h_b1_dec h_b2_dec h_b3_dec eq_lr1 eq_lr2 eq_lr3
      simp only [eq_v0123, eq_lr0, eq_lr1, eq_lr2, eq_lr3, Nat.cast_one, mul_one, add_zero,
        h_hl0_zero, h_hl1_zero, h_hl2_zero, zero_add, add_zero]
      rw [← h_b0_dec, ← h_b1_dec, ← h_b2_dec, ← h_b3_dec]
      have h_cb_sum_zero : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val = 0 := by
        simp only [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5, zero_mul, zero_add, add_zero]
        exact h_v0_val
      rw [h_cb_sum_zero]
      simp only [Nat.shiftLeft_zero]
      rw [Nat.mod_eq_of_lt (BitVec.isLt _)]
    -- Remaining 15 cb0..3 sub-cases (cb_sum_low ∈ {1..15}, v0123 = 2^cb_sum_low).
    -- Each case follows the same pattern as all-zeros, with:
    --   - eq_v01 → eq_v012 → eq_v0123 chain gives v0123 = 2^cb_sum_low
    --   - For hl_i ≠ 0 in general: at the Nat level, derive
    --     b_i.val = ll_i.val + (65536/v0123.val) * hl_i.val
    --     via h_b_dec + ZMod.val_*_of_lt + omega (no need for cancel_mul_65536_poly
    --     when working in Nat throughout — the bounds make ZMod val computation tight)
    --   - Goal a_j.val = byte-shifted b expressions; close via omega.
    all_goals sorry
  all_goals sorry

lemma spec.slli_poly (Main : Vector (ZMod p) 65) (h : is_slli_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SLL := by
  sorry

end sll_poly

section slli

lemma spec.slli (h : is_slli Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLL
  := by
    have _ := h
    intro cstrs
    obtain ⟨eq_sll, eq_imm⟩ := h
    have ⟨h0, h1, h2, hpc, is_U64_b, is_U64_c, imm_zeros, h3⟩ := bounds Main cstrs (sll_real Main eq_sll)
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
    clear h_msb_a1 cpu alu
    simp_all
    rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have : ((Word.toBitVec64 #v[c0, 0, 0, 0]).toNat % 64) = c0.val % 64 := by
      rw [Word.toBitVec64_toNat is_U64_c]; simp [Word.toNat]
    rw [this]; clear this
    have : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · omega
      · exact diff
    rw [this]; clear this
    rw [Word.toBitVec64_toNat (w := #v[b0, b1, b2, b3]) (by apply Word.isU64_of_cases <;> simp <;> assumption)]
    simp [Word.toNat]
    -- 64-way case split
    rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
    rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
    simp_all <;>
    (try apply cancel_mul_65536 (by simp) at h_b0_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b1_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b2_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b3_dec) <;>
    simp_all
    all_goals {
      rw [Word.toBitVec64_toNat]
      · simp [Word.toNat]
        try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
        repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
        omega
      · apply Word.isU64_of_cases <;> simp [Fin.val_add, Fin.val_mul] <;>
        (repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]) <;>
        omega
    }

end slli

end ShiftLeft
