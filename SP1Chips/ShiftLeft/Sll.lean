import SP1Chips.ShiftLeft.Common

namespace ShiftLeft

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
set_option maxHeartbeats 100000000
set_option linter.style.longLine false


section sll

variable {p : ℕ} [Fact (Nat.Prime p)] [hp : Fact (2 ^ 17 < p)]

lemma spec.sll (Main : Vector (ZMod p) 65) (h : is_sll Main) :
    (constraints Main).allHold →
      Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SLL := by
  intro cstrs
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨eq_sll, _eq_imm⟩ := h
  have h_real := is_real_eq_one_of_sll Main cstrs eq_sll
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs h_real
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
  obtain ⟨c0_16, _c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64 is_U64_c
  obtain ⟨sop_1, _sop_2⟩ := single_op Main cstrs
  have h_no_sllw : Main[63] = 0 := sop_1 eq_sll
  -- Open the iff.
  change List.Forall SP1Constraint.toProp (constraints Main) at cstrs
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
  -- set su160 := Main[45]
  -- set su161 := Main[46]
  -- set su162 := Main[47]
  -- set su163 := Main[48]
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
  obtain ⟨_h_msb_a1, _cpu, _alu, _one_of_ops,
           _b_sll, _b_sllw,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
           h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
           eq_v01, eq_v012, eq_v0123,
           lt_ll0', lt_lh0', h_b0_dec, lt_ll1', lt_lh1', h_b1_dec,
           lt_ll2', lt_lh2', h_b2_dec, lt_ll3', lt_lh3', h_b3_dec,
           eq_lr0, eq_lr1, eq_lr2, eq_lr3,
           rest⟩ := cstrs
  have h_sum_ne : ¬ Main[62] + Main[63] = 0 := by
    intro hh; rw [hh] at h_real; exact zero_ne_one h_real
  have diff' := diff h_sum_ne
  -- Goal manipulation: reduce to nat arithmetic.
  rw [← BitVec.toNat_inj]
  simp only [execute_RTYPE_pure_w]
  rw [BitVec.shiftLeft_eq']
  simp only [BitVec.toNat_setWidth]
  -- Goal: (toBitVec64 a).toNat = (toBitVec64 b <<< ((toBitVec64 c).toNat % 2^6)).toNat
  -- (`BitVec.toNat_shiftLeft` is pushed into each `sll_close_cb4cb5_*_case` helper to
  -- isolate the kernel walk over `% 2^64` to a single olean.)
  change (Word.toBitVec64 #v[a0, a1, a2, a3]).toNat =
        (Word.toBitVec64 #v[b0, b1, b2, b3] <<<
          ((Word.toBitVec64 #v[c0, Main[26], Main[27], Main[28]]).toNat % 2 ^ 6)).toNat
  -- Reduce the c-toNat % 64 to c0.val % 64
  have h_c_mod : (Word.toBitVec64 #v[c0, Main[26], Main[27], Main[28]]).toNat % 2 ^ 6 = c0.val % 64 := by
    rw [Word.toBitVec64_toNat is_U64_c, Word.toNat_def]
    simp; omega
  rw [h_c_mod]; clear h_c_mod
  -- Use is_mod_64 to convert c0.val % 64 to cb sum.
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
    apply is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)
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
      simp only [BitVec.shiftLeft_zero]
    -- Remaining 15 cb0..3 sub-cases for cb4=cb5=0, in lex order over (cb0, cb1, cb2, cb3).
    · -- cb0=0, cb1=0, cb2=0, cb3=1: shift=8. M=256, N=256.
      have hv0123_val : v0123.val = 256 := by
        have h : v0123 = 256 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_256_zmod_p
      exact sll_close_cb4cb5_zero_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=0: shift=4. M=16, N=4096.
      have hv0123_val : v0123.val = 16 := by
        have h : v0123 = 16 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16_zmod_p
      exact sll_close_cb4cb5_zero_case 4 (by omega) 16 4096 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=1: shift=12. M=4096, N=16.
      have hv0123_val : v0123.val = 4096 := by
        have h : v0123 = 4096 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4096_zmod_p
      exact sll_close_cb4cb5_zero_case 12 (by omega) 4096 16 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=0: shift=2. M=4, N=16384.
      have hv0123_val : v0123.val = 4 := by
        have h : v0123 = 4 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4_zmod_p
      exact sll_close_cb4cb5_zero_case 2 (by omega) 4 16384 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=1: shift=10. M=1024, N=64.
      have hv0123_val : v0123.val = 1024 := by
        have h : v0123 = 1024 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_1024_zmod_p
      exact sll_close_cb4cb5_zero_case 10 (by omega) 1024 64 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=0: shift=6. M=64, N=1024.
      have hv0123_val : v0123.val = 64 := by
        have h : v0123 = 64 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_64_zmod_p
      exact sll_close_cb4cb5_zero_case 6 (by omega) 64 1024 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=1: shift=14. M=16384, N=4.
      have hv0123_val : v0123.val = 16384 := by
        have h : v0123 = 16384 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16384_zmod_p
      exact sll_close_cb4cb5_zero_case 14 (by omega) 16384 4 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=0: shift=1. M=2, N=32768.
      have hv0123_val : v0123.val = 2 := by
        have h : v0123 = 2 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2_zmod_p
      exact sll_close_cb4cb5_zero_case 1 (by omega) 2 32768 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=1: shift=9. M=512, N=128.
      have hv0123_val : v0123.val = 512 := by
        have h : v0123 = 512 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_512_zmod_p
      exact sll_close_cb4cb5_zero_case 9 (by omega) 512 128 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=0: shift=5. M=32, N=2048.
      have hv0123_val : v0123.val = 32 := by
        have h : v0123 = 32 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32_zmod_p
      exact sll_close_cb4cb5_zero_case 5 (by omega) 32 2048 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=1: shift=13. M=8192, N=8.
      have hv0123_val : v0123.val = 8192 := by
        have h : v0123 = 8192 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8192_zmod_p
      exact sll_close_cb4cb5_zero_case 13 (by omega) 8192 8 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=0: shift=3. M=8, N=8192.
      have hv0123_val : v0123.val = 8 := by
        have h : v0123 = 8 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8_zmod_p
      exact sll_close_cb4cb5_zero_case 3 (by omega) 8 8192 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=1: shift=11. M=2048, N=32.
      have hv0123_val : v0123.val = 2048 := by
        have h : v0123 = 2048 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2048_zmod_p
      exact sll_close_cb4cb5_zero_case 11 (by omega) 2048 32 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=0: shift=7. M=128, N=512.
      have hv0123_val : v0123.val = 128 := by
        have h : v0123 = 128 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_128_zmod_p
      exact sll_close_cb4cb5_zero_case 7 (by omega) 128 512 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=1: shift=15. M=32768, N=2.
      have hv0123_val : v0123.val = 32768 := by
        have h : v0123 = 32768 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32768_zmod_p
      exact sll_close_cb4cb5_zero_case 15 (by omega) 32768 2 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  · -- cb4 = 0, cb5 = 1: byte_shift = 2, Main[47] = 1.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul,
      mul_one] at h_su160 h_su161 h_su162 h_su163
    -- cb4 + cb5*2 = 0 + 2 = 2, so Main[47] = 1 (others = 0).
    have h_45_eq : Main[45] = 0 := by
      rcases h_su160 with h | h
      · exact h
      · exfalso; exact val_2_ne_zero h
    have h_46_eq : Main[46] = 0 := by
      rcases h_su161 with h | h
      · exact h
      · exfalso
        have : (1 : ZMod p) = 0 := by linear_combination h
        exact h_1_ne_0 this
    have h_48_eq : Main[48] = 0 := by
      rcases h_su163 with h | h
      · exact h
      · exfalso
        have : (1 : ZMod p) = 0 := by linear_combination -h
        exact h_1_ne_0 this
    have h_47_eq : Main[47] = 1 := by
      have := h_su_sum
      rw [h_45_eq, h_46_eq, h_48_eq] at this
      linear_combination this
    -- Destructure rest: positions 9-12 give Main[47]-based eqns.
    obtain ⟨_, _, _, _, _, _, _, _, h_a0_47, h_a1_47, h_a2_47, h_a3_47, _rest_other⟩ := rest
    have h_a0_eq : a0 = 0 := by
      rcases h_a0_47 with h | h
      · exfalso; rw [h_47_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a1_eq : a1 = 0 := by
      rcases h_a1_47 with h | h
      · exfalso; rw [h_47_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a2_eq : a2 = lr0 := by
      rcases h_a2_47 with h | h
      · exfalso; rw [h_47_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a3_eq : a3 = lr1 := by
      rcases h_a3_47 with h | h
      · exfalso; rw [h_47_eq] at h; exact h_1_ne_0 h
      · exact h
    -- Substitute a_j and expand lr_0, lr_1 in the goal.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr0, eq_lr1]
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- cb0..3 = 0000: S=0
      have hv0123_val : v0123.val = 1 := by
        have h : v0123 = 1 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact h_v1_val
      exact sll_close_cb4cb5_zero_one_case 0 (by omega) 1 65536 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0001: S=8
      have hv0123_val : v0123.val = 256 := by
        have h : v0123 = 256 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_256_zmod_p
      exact sll_close_cb4cb5_zero_one_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0010: S=4
      have hv0123_val : v0123.val = 16 := by
        have h : v0123 = 16 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16_zmod_p
      exact sll_close_cb4cb5_zero_one_case 4 (by omega) 16 4096 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0011: S=12
      have hv0123_val : v0123.val = 4096 := by
        have h : v0123 = 4096 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4096_zmod_p
      exact sll_close_cb4cb5_zero_one_case 12 (by omega) 4096 16 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0100: S=2
      have hv0123_val : v0123.val = 4 := by
        have h : v0123 = 4 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4_zmod_p
      exact sll_close_cb4cb5_zero_one_case 2 (by omega) 4 16384 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0101: S=10
      have hv0123_val : v0123.val = 1024 := by
        have h : v0123 = 1024 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_1024_zmod_p
      exact sll_close_cb4cb5_zero_one_case 10 (by omega) 1024 64 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0110: S=6
      have hv0123_val : v0123.val = 64 := by
        have h : v0123 = 64 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_64_zmod_p
      exact sll_close_cb4cb5_zero_one_case 6 (by omega) 64 1024 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0111: S=14
      have hv0123_val : v0123.val = 16384 := by
        have h : v0123 = 16384 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16384_zmod_p
      exact sll_close_cb4cb5_zero_one_case 14 (by omega) 16384 4 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1000: S=1
      have hv0123_val : v0123.val = 2 := by
        have h : v0123 = 2 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2_zmod_p
      exact sll_close_cb4cb5_zero_one_case 1 (by omega) 2 32768 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1001: S=9
      have hv0123_val : v0123.val = 512 := by
        have h : v0123 = 512 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_512_zmod_p
      exact sll_close_cb4cb5_zero_one_case 9 (by omega) 512 128 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1010: S=5
      have hv0123_val : v0123.val = 32 := by
        have h : v0123 = 32 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32_zmod_p
      exact sll_close_cb4cb5_zero_one_case 5 (by omega) 32 2048 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1011: S=13
      have hv0123_val : v0123.val = 8192 := by
        have h : v0123 = 8192 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8192_zmod_p
      exact sll_close_cb4cb5_zero_one_case 13 (by omega) 8192 8 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1100: S=3
      have hv0123_val : v0123.val = 8 := by
        have h : v0123 = 8 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8_zmod_p
      exact sll_close_cb4cb5_zero_one_case 3 (by omega) 8 8192 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1101: S=11
      have hv0123_val : v0123.val = 2048 := by
        have h : v0123 = 2048 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2048_zmod_p
      exact sll_close_cb4cb5_zero_one_case 11 (by omega) 2048 32 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1110: S=7
      have hv0123_val : v0123.val = 128 := by
        have h : v0123 = 128 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_128_zmod_p
      exact sll_close_cb4cb5_zero_one_case 7 (by omega) 128 512 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1111: S=15
      have hv0123_val : v0123.val = 32768 := by
        have h : v0123 = 32768 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32768_zmod_p
      exact sll_close_cb4cb5_zero_one_case 15 (by omega) 32768 2 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  · -- cb4 = 1, cb5 = 0: byte_shift = 1, Main[46] = 1.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul,
      mul_one] at h_su160 h_su161 h_su162 h_su163
    -- cb4 + cb5*2 = 1 + 0 = 1, so Main[46] = 1 (others = 0).
    have h_45_eq : Main[45] = 0 := by
      rcases h_su160 with h | h
      · exact h
      · exfalso; exact h_1_ne_0 h
    have h_47_eq : Main[47] = 0 := by
      rcases h_su162 with h | h
      · exact h
      · exfalso
        have : (1 : ZMod p) = 0 := by linear_combination -h
        exact h_1_ne_0 this
    have h_48_eq : Main[48] = 0 := by
      rcases h_su163 with h | h
      · exact h
      · exfalso
        have : (2 : ZMod p) = 0 := by linear_combination -h
        exact val_2_ne_zero this
    have h_46_eq : Main[46] = 1 := by
      have := h_su_sum
      rw [h_45_eq, h_47_eq, h_48_eq] at this
      linear_combination this
    -- Destructure rest: positions 5-8 give Main[46]-based eqns.
    obtain ⟨_, _, _, _, h_a0_46, h_a1_46, h_a2_46, h_a3_46, _rest_other⟩ := rest
    have h_a0_eq : a0 = 0 := by
      rcases h_a0_46 with h | h
      · exfalso; rw [h_46_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a1_eq : a1 = lr0 := by
      rcases h_a1_46 with h | h
      · exfalso; rw [h_46_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a2_eq : a2 = lr1 := by
      rcases h_a2_46 with h | h
      · exfalso; rw [h_46_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a3_eq : a3 = lr2 := by
      rcases h_a3_46 with h | h
      · exfalso; rw [h_46_eq] at h; exact h_1_ne_0 h
      · exact h
    -- Substitute a_j and expand lr_0, lr_1, lr_2 in the goal.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr0, eq_lr1, eq_lr2]
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- cb0..3 = 0000: S=0
      have hv0123_val : v0123.val = 1 := by
        have h : v0123 = 1 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact h_v1_val
      exact sll_close_cb4cb5_one_zero_case 0 (by omega) 1 65536 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0001: S=8
      have hv0123_val : v0123.val = 256 := by
        have h : v0123 = 256 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_256_zmod_p
      exact sll_close_cb4cb5_one_zero_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0010: S=4
      have hv0123_val : v0123.val = 16 := by
        have h : v0123 = 16 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16_zmod_p
      exact sll_close_cb4cb5_one_zero_case 4 (by omega) 16 4096 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0011: S=12
      have hv0123_val : v0123.val = 4096 := by
        have h : v0123 = 4096 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4096_zmod_p
      exact sll_close_cb4cb5_one_zero_case 12 (by omega) 4096 16 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0100: S=2
      have hv0123_val : v0123.val = 4 := by
        have h : v0123 = 4 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4_zmod_p
      exact sll_close_cb4cb5_one_zero_case 2 (by omega) 4 16384 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0101: S=10
      have hv0123_val : v0123.val = 1024 := by
        have h : v0123 = 1024 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_1024_zmod_p
      exact sll_close_cb4cb5_one_zero_case 10 (by omega) 1024 64 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0110: S=6
      have hv0123_val : v0123.val = 64 := by
        have h : v0123 = 64 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_64_zmod_p
      exact sll_close_cb4cb5_one_zero_case 6 (by omega) 64 1024 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0111: S=14
      have hv0123_val : v0123.val = 16384 := by
        have h : v0123 = 16384 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16384_zmod_p
      exact sll_close_cb4cb5_one_zero_case 14 (by omega) 16384 4 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1000: S=1
      have hv0123_val : v0123.val = 2 := by
        have h : v0123 = 2 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2_zmod_p
      exact sll_close_cb4cb5_one_zero_case 1 (by omega) 2 32768 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1001: S=9
      have hv0123_val : v0123.val = 512 := by
        have h : v0123 = 512 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_512_zmod_p
      exact sll_close_cb4cb5_one_zero_case 9 (by omega) 512 128 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1010: S=5
      have hv0123_val : v0123.val = 32 := by
        have h : v0123 = 32 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32_zmod_p
      exact sll_close_cb4cb5_one_zero_case 5 (by omega) 32 2048 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1011: S=13
      have hv0123_val : v0123.val = 8192 := by
        have h : v0123 = 8192 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8192_zmod_p
      exact sll_close_cb4cb5_one_zero_case 13 (by omega) 8192 8 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1100: S=3
      have hv0123_val : v0123.val = 8 := by
        have h : v0123 = 8 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8_zmod_p
      exact sll_close_cb4cb5_one_zero_case 3 (by omega) 8 8192 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1101: S=11
      have hv0123_val : v0123.val = 2048 := by
        have h : v0123 = 2048 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2048_zmod_p
      exact sll_close_cb4cb5_one_zero_case 11 (by omega) 2048 32 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1110: S=7
      have hv0123_val : v0123.val = 128 := by
        have h : v0123 = 128 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_128_zmod_p
      exact sll_close_cb4cb5_one_zero_case 7 (by omega) 128 512 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1111: S=15
      have hv0123_val : v0123.val = 32768 := by
        have h : v0123 = 32768 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32768_zmod_p
      exact sll_close_cb4cb5_one_zero_case 15 (by omega) 32768 2 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  · -- cb4 = 1, cb5 = 1: byte_shift = 3, Main[48] = 1. The all-ones case lives here.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [one_mul, mul_one] at h_su160 h_su161 h_su162 h_su163
    -- cb4 + cb5*2 = 1 + 2 = 3, so Main[48] = 1 (others = 0).
    have h_45_eq : Main[45] = 0 := by
      rcases h_su160 with h | h
      · exact h
      · exfalso
        have : (3 : ZMod p) = 0 := by linear_combination h
        exact val_3_ne_zero this
    have h_46_eq : Main[46] = 0 := by
      rcases h_su161 with h | h
      · exact h
      · exfalso
        have : (2 : ZMod p) = 0 := by linear_combination h
        exact val_2_ne_zero this
    have h_47_eq : Main[47] = 0 := by
      rcases h_su162 with h | h
      · exact h
      · exfalso
        have : (1 : ZMod p) = 0 := by linear_combination h
        exact h_1_ne_0 this
    have h_48_eq : Main[48] = 1 := by
      have := h_su_sum
      rw [h_45_eq, h_46_eq, h_47_eq] at this
      linear_combination this
    -- Extract from rest: with Main[48] = 1, the last 4 conjuncts (positions 13-16) give
    -- a0 = 0, a1 = 0, a2 = 0, a3 = lr0.
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h_a0_48, h_a1_48, h_a2_48, h_a3_48, _rest_other⟩ := rest
    have h_a0_eq : a0 = 0 := by
      rcases h_a0_48 with h | h
      · exfalso; rw [h_48_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a1_eq : a1 = 0 := by
      rcases h_a1_48 with h | h
      · exfalso; rw [h_48_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a2_eq : a2 = 0 := by
      rcases h_a2_48 with h | h
      · exfalso; rw [h_48_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a3_eq : a3 = lr0 := by
      rcases h_a3_48 with h | h
      · exfalso; rw [h_48_eq] at h; exact h_1_ne_0 h
      · exact h
    -- Substitute a_j and expand lr_0 in the goal.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr0]
    -- 16-way case split on cb0..cb3.
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- cb0..3 = 0000: S=0, M=1, N=65536.
      have hv0123_val : v0123.val = 1 := by
        have h : v0123 = 1 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact h_v1_val
      exact sll_close_cb4cb5_one_one_case 0 (by omega) 1 65536 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0001: S=8, M=256, N=256.
      have hv0123_val : v0123.val = 256 := by
        have h : v0123 = 256 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_256_zmod_p
      exact sll_close_cb4cb5_one_one_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0010: S=4, M=16, N=4096.
      have hv0123_val : v0123.val = 16 := by
        have h : v0123 = 16 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16_zmod_p
      exact sll_close_cb4cb5_one_one_case 4 (by omega) 16 4096 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0011: S=12, M=4096, N=16.
      have hv0123_val : v0123.val = 4096 := by
        have h : v0123 = 4096 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4096_zmod_p
      exact sll_close_cb4cb5_one_one_case 12 (by omega) 4096 16 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0100: S=2, M=4, N=16384.
      have hv0123_val : v0123.val = 4 := by
        have h : v0123 = 4 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4_zmod_p
      exact sll_close_cb4cb5_one_one_case 2 (by omega) 4 16384 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0101: S=10, M=1024, N=64.
      have hv0123_val : v0123.val = 1024 := by
        have h : v0123 = 1024 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_1024_zmod_p
      exact sll_close_cb4cb5_one_one_case 10 (by omega) 1024 64 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0110: S=6, M=64, N=1024.
      have hv0123_val : v0123.val = 64 := by
        have h : v0123 = 64 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_64_zmod_p
      exact sll_close_cb4cb5_one_one_case 6 (by omega) 64 1024 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0111: S=14, M=16384, N=4.
      have hv0123_val : v0123.val = 16384 := by
        have h : v0123 = 16384 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16384_zmod_p
      exact sll_close_cb4cb5_one_one_case 14 (by omega) 16384 4 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1000: S=1, M=2, N=32768.
      have hv0123_val : v0123.val = 2 := by
        have h : v0123 = 2 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2_zmod_p
      exact sll_close_cb4cb5_one_one_case 1 (by omega) 2 32768 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1001: S=9, M=512, N=128.
      have hv0123_val : v0123.val = 512 := by
        have h : v0123 = 512 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_512_zmod_p
      exact sll_close_cb4cb5_one_one_case 9 (by omega) 512 128 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1010: S=5, M=32, N=2048.
      have hv0123_val : v0123.val = 32 := by
        have h : v0123 = 32 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32_zmod_p
      exact sll_close_cb4cb5_one_one_case 5 (by omega) 32 2048 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1011: S=13, M=8192, N=8.
      have hv0123_val : v0123.val = 8192 := by
        have h : v0123 = 8192 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8192_zmod_p
      exact sll_close_cb4cb5_one_one_case 13 (by omega) 8192 8 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1100: S=3, M=8, N=8192.
      have hv0123_val : v0123.val = 8 := by
        have h : v0123 = 8 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8_zmod_p
      exact sll_close_cb4cb5_one_one_case 3 (by omega) 8 8192 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1101: S=11, M=2048, N=32.
      have hv0123_val : v0123.val = 2048 := by
        have h : v0123 = 2048 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2048_zmod_p
      exact sll_close_cb4cb5_one_one_case 11 (by omega) 2048 32 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1110: S=7, M=128, N=512.
      have hv0123_val : v0123.val = 128 := by
        have h : v0123 = 128 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_128_zmod_p
      exact sll_close_cb4cb5_one_one_case 7 (by omega) 128 512 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1111: S=15, M=32768, N=2.
      have hv0123_val : v0123.val = 32768 := by
        have h : v0123 = 32768 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32768_zmod_p
      exact sll_close_cb4cb5_one_one_case 15 (by omega) 32768 2 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec

lemma spec.slli (Main : Vector (ZMod p) 65) (h : is_slli Main) :
    (constraints Main).allHold →
      Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SLL := by
  intro cstrs
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨eq_slli, _eq_imm⟩ := h
  have h_real := is_real_eq_one_of_sll Main cstrs eq_slli
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs h_real
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
  obtain ⟨c0_16, _c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64 is_U64_c
  obtain ⟨sop_1, _sop_2⟩ := single_op Main cstrs
  have h_no_sllw : Main[63] = 0 := sop_1 eq_slli
  -- Open the iff.
  change List.Forall SP1Constraint.toProp (constraints Main) at cstrs
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
  -- set su160 := Main[45]
  -- set su161 := Main[46]
  -- set su162 := Main[47]
  -- set su163 := Main[48]
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
  obtain ⟨_h_msb_a1, _cpu, _alu, _one_of_ops,
           _b_sll, _b_sllw,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
           h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
           eq_v01, eq_v012, eq_v0123,
           lt_ll0', lt_lh0', h_b0_dec, lt_ll1', lt_lh1', h_b1_dec,
           lt_ll2', lt_lh2', h_b2_dec, lt_ll3', lt_lh3', h_b3_dec,
           eq_lr0, eq_lr1, eq_lr2, eq_lr3,
           rest⟩ := cstrs
  have h_sum_ne : ¬ Main[62] + Main[63] = 0 := by
    intro hh; rw [hh] at h_real; exact zero_ne_one h_real
  have diff' := diff h_sum_ne
  -- Goal manipulation: reduce to nat arithmetic.
  rw [← BitVec.toNat_inj]
  simp only [execute_RTYPE_pure_w]
  rw [BitVec.shiftLeft_eq']
  simp only [BitVec.toNat_setWidth]
  -- Goal: (toBitVec64 a).toNat = (toBitVec64 b <<< ((toBitVec64 c).toNat % 2^6)).toNat
  -- (`BitVec.toNat_shiftLeft` is pushed into each `sll_close_cb4cb5_*_case` helper to
  -- isolate the kernel walk over `% 2^64` to a single olean.)
  change (Word.toBitVec64 #v[a0, a1, a2, a3]).toNat =
        (Word.toBitVec64 #v[b0, b1, b2, b3] <<<
          ((Word.toBitVec64 #v[c0, Main[26], Main[27], Main[28]]).toNat % 2 ^ 6)).toNat
  -- Reduce the c-toNat % 64 to c0.val % 64
  have h_c_mod : (Word.toBitVec64 #v[c0, Main[26], Main[27], Main[28]]).toNat % 2 ^ 6 = c0.val % 64 := by
    rw [Word.toBitVec64_toNat is_U64_c, Word.toNat_def]
    simp; omega
  rw [h_c_mod]; clear h_c_mod
  -- Use is_mod_64 to convert c0.val % 64 to cb sum.
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
    apply is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)
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
  rw [eq_slli] at rest
  rw [h_no_sllw] at rest
  simp only [h_1_ne_0, false_or, true_or, or_true] at rest
  -- Drop Main[62] from h_su16i selectors via eq_slli.
  rw [eq_slli] at h_su160 h_su161 h_su162 h_su163
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
      simp only [BitVec.shiftLeft_zero]
    -- Remaining 15 cb0..3 sub-cases for cb4=cb5=0, in lex order over (cb0, cb1, cb2, cb3).
    · -- cb0=0, cb1=0, cb2=0, cb3=1: shift=8. M=256, N=256.
      have hv0123_val : v0123.val = 256 := by
        have h : v0123 = 256 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_256_zmod_p
      exact sll_close_cb4cb5_zero_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=0: shift=4. M=16, N=4096.
      have hv0123_val : v0123.val = 16 := by
        have h : v0123 = 16 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16_zmod_p
      exact sll_close_cb4cb5_zero_case 4 (by omega) 16 4096 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=1: shift=12. M=4096, N=16.
      have hv0123_val : v0123.val = 4096 := by
        have h : v0123 = 4096 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4096_zmod_p
      exact sll_close_cb4cb5_zero_case 12 (by omega) 4096 16 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=0: shift=2. M=4, N=16384.
      have hv0123_val : v0123.val = 4 := by
        have h : v0123 = 4 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4_zmod_p
      exact sll_close_cb4cb5_zero_case 2 (by omega) 4 16384 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=1: shift=10. M=1024, N=64.
      have hv0123_val : v0123.val = 1024 := by
        have h : v0123 = 1024 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_1024_zmod_p
      exact sll_close_cb4cb5_zero_case 10 (by omega) 1024 64 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=0: shift=6. M=64, N=1024.
      have hv0123_val : v0123.val = 64 := by
        have h : v0123 = 64 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_64_zmod_p
      exact sll_close_cb4cb5_zero_case 6 (by omega) 64 1024 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=1: shift=14. M=16384, N=4.
      have hv0123_val : v0123.val = 16384 := by
        have h : v0123 = 16384 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16384_zmod_p
      exact sll_close_cb4cb5_zero_case 14 (by omega) 16384 4 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=0: shift=1. M=2, N=32768.
      have hv0123_val : v0123.val = 2 := by
        have h : v0123 = 2 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2_zmod_p
      exact sll_close_cb4cb5_zero_case 1 (by omega) 2 32768 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=1: shift=9. M=512, N=128.
      have hv0123_val : v0123.val = 512 := by
        have h : v0123 = 512 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_512_zmod_p
      exact sll_close_cb4cb5_zero_case 9 (by omega) 512 128 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=0: shift=5. M=32, N=2048.
      have hv0123_val : v0123.val = 32 := by
        have h : v0123 = 32 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32_zmod_p
      exact sll_close_cb4cb5_zero_case 5 (by omega) 32 2048 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=1: shift=13. M=8192, N=8.
      have hv0123_val : v0123.val = 8192 := by
        have h : v0123 = 8192 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8192_zmod_p
      exact sll_close_cb4cb5_zero_case 13 (by omega) 8192 8 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=0: shift=3. M=8, N=8192.
      have hv0123_val : v0123.val = 8 := by
        have h : v0123 = 8 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8_zmod_p
      exact sll_close_cb4cb5_zero_case 3 (by omega) 8 8192 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=1: shift=11. M=2048, N=32.
      have hv0123_val : v0123.val = 2048 := by
        have h : v0123 = 2048 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2048_zmod_p
      exact sll_close_cb4cb5_zero_case 11 (by omega) 2048 32 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=0: shift=7. M=128, N=512.
      have hv0123_val : v0123.val = 128 := by
        have h : v0123 = 128 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_128_zmod_p
      exact sll_close_cb4cb5_zero_case 7 (by omega) 128 512 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=1: shift=15. M=32768, N=2.
      have hv0123_val : v0123.val = 32768 := by
        have h : v0123 = 32768 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32768_zmod_p
      exact sll_close_cb4cb5_zero_case 15 (by omega) 32768 2 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  · -- cb4 = 0, cb5 = 1: byte_shift = 2, Main[47] = 1.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul,
      mul_one] at h_su160 h_su161 h_su162 h_su163
    -- cb4 + cb5*2 = 0 + 2 = 2, so Main[47] = 1 (others = 0).
    have h_45_eq : Main[45] = 0 := by
      rcases h_su160 with h | h
      · exact h
      · exfalso; exact val_2_ne_zero h
    have h_46_eq : Main[46] = 0 := by
      rcases h_su161 with h | h
      · exact h
      · exfalso
        have : (1 : ZMod p) = 0 := by linear_combination h
        exact h_1_ne_0 this
    have h_48_eq : Main[48] = 0 := by
      rcases h_su163 with h | h
      · exact h
      · exfalso
        have : (1 : ZMod p) = 0 := by linear_combination -h
        exact h_1_ne_0 this
    have h_47_eq : Main[47] = 1 := by
      have := h_su_sum
      rw [h_45_eq, h_46_eq, h_48_eq] at this
      linear_combination this
    -- Destructure rest: positions 9-12 give Main[47]-based eqns.
    obtain ⟨_, _, _, _, _, _, _, _, h_a0_47, h_a1_47, h_a2_47, h_a3_47, _rest_other⟩ := rest
    have h_a0_eq : a0 = 0 := by
      rcases h_a0_47 with h | h
      · exfalso; rw [h_47_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a1_eq : a1 = 0 := by
      rcases h_a1_47 with h | h
      · exfalso; rw [h_47_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a2_eq : a2 = lr0 := by
      rcases h_a2_47 with h | h
      · exfalso; rw [h_47_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a3_eq : a3 = lr1 := by
      rcases h_a3_47 with h | h
      · exfalso; rw [h_47_eq] at h; exact h_1_ne_0 h
      · exact h
    -- Substitute a_j and expand lr_0, lr_1 in the goal.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr0, eq_lr1]
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- cb0..3 = 0000: S=0
      have hv0123_val : v0123.val = 1 := by
        have h : v0123 = 1 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact h_v1_val
      exact sll_close_cb4cb5_zero_one_case 0 (by omega) 1 65536 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0001: S=8
      have hv0123_val : v0123.val = 256 := by
        have h : v0123 = 256 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_256_zmod_p
      exact sll_close_cb4cb5_zero_one_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0010: S=4
      have hv0123_val : v0123.val = 16 := by
        have h : v0123 = 16 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16_zmod_p
      exact sll_close_cb4cb5_zero_one_case 4 (by omega) 16 4096 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0011: S=12
      have hv0123_val : v0123.val = 4096 := by
        have h : v0123 = 4096 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4096_zmod_p
      exact sll_close_cb4cb5_zero_one_case 12 (by omega) 4096 16 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0100: S=2
      have hv0123_val : v0123.val = 4 := by
        have h : v0123 = 4 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4_zmod_p
      exact sll_close_cb4cb5_zero_one_case 2 (by omega) 4 16384 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0101: S=10
      have hv0123_val : v0123.val = 1024 := by
        have h : v0123 = 1024 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_1024_zmod_p
      exact sll_close_cb4cb5_zero_one_case 10 (by omega) 1024 64 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0110: S=6
      have hv0123_val : v0123.val = 64 := by
        have h : v0123 = 64 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_64_zmod_p
      exact sll_close_cb4cb5_zero_one_case 6 (by omega) 64 1024 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0111: S=14
      have hv0123_val : v0123.val = 16384 := by
        have h : v0123 = 16384 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16384_zmod_p
      exact sll_close_cb4cb5_zero_one_case 14 (by omega) 16384 4 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1000: S=1
      have hv0123_val : v0123.val = 2 := by
        have h : v0123 = 2 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2_zmod_p
      exact sll_close_cb4cb5_zero_one_case 1 (by omega) 2 32768 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1001: S=9
      have hv0123_val : v0123.val = 512 := by
        have h : v0123 = 512 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_512_zmod_p
      exact sll_close_cb4cb5_zero_one_case 9 (by omega) 512 128 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1010: S=5
      have hv0123_val : v0123.val = 32 := by
        have h : v0123 = 32 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32_zmod_p
      exact sll_close_cb4cb5_zero_one_case 5 (by omega) 32 2048 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1011: S=13
      have hv0123_val : v0123.val = 8192 := by
        have h : v0123 = 8192 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8192_zmod_p
      exact sll_close_cb4cb5_zero_one_case 13 (by omega) 8192 8 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1100: S=3
      have hv0123_val : v0123.val = 8 := by
        have h : v0123 = 8 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8_zmod_p
      exact sll_close_cb4cb5_zero_one_case 3 (by omega) 8 8192 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1101: S=11
      have hv0123_val : v0123.val = 2048 := by
        have h : v0123 = 2048 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2048_zmod_p
      exact sll_close_cb4cb5_zero_one_case 11 (by omega) 2048 32 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1110: S=7
      have hv0123_val : v0123.val = 128 := by
        have h : v0123 = 128 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_128_zmod_p
      exact sll_close_cb4cb5_zero_one_case 7 (by omega) 128 512 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1111: S=15
      have hv0123_val : v0123.val = 32768 := by
        have h : v0123 = 32768 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32768_zmod_p
      exact sll_close_cb4cb5_zero_one_case 15 (by omega) 32768 2 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  · -- cb4 = 1, cb5 = 0: byte_shift = 1, Main[46] = 1.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul,
      mul_one] at h_su160 h_su161 h_su162 h_su163
    -- cb4 + cb5*2 = 1 + 0 = 1, so Main[46] = 1 (others = 0).
    have h_45_eq : Main[45] = 0 := by
      rcases h_su160 with h | h
      · exact h
      · exfalso; exact h_1_ne_0 h
    have h_47_eq : Main[47] = 0 := by
      rcases h_su162 with h | h
      · exact h
      · exfalso
        have : (1 : ZMod p) = 0 := by linear_combination -h
        exact h_1_ne_0 this
    have h_48_eq : Main[48] = 0 := by
      rcases h_su163 with h | h
      · exact h
      · exfalso
        have : (2 : ZMod p) = 0 := by linear_combination -h
        exact val_2_ne_zero this
    have h_46_eq : Main[46] = 1 := by
      have := h_su_sum
      rw [h_45_eq, h_47_eq, h_48_eq] at this
      linear_combination this
    -- Destructure rest: positions 5-8 give Main[46]-based eqns.
    obtain ⟨_, _, _, _, h_a0_46, h_a1_46, h_a2_46, h_a3_46, _rest_other⟩ := rest
    have h_a0_eq : a0 = 0 := by
      rcases h_a0_46 with h | h
      · exfalso; rw [h_46_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a1_eq : a1 = lr0 := by
      rcases h_a1_46 with h | h
      · exfalso; rw [h_46_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a2_eq : a2 = lr1 := by
      rcases h_a2_46 with h | h
      · exfalso; rw [h_46_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a3_eq : a3 = lr2 := by
      rcases h_a3_46 with h | h
      · exfalso; rw [h_46_eq] at h; exact h_1_ne_0 h
      · exact h
    -- Substitute a_j and expand lr_0, lr_1, lr_2 in the goal.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr0, eq_lr1, eq_lr2]
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- cb0..3 = 0000: S=0
      have hv0123_val : v0123.val = 1 := by
        have h : v0123 = 1 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact h_v1_val
      exact sll_close_cb4cb5_one_zero_case 0 (by omega) 1 65536 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0001: S=8
      have hv0123_val : v0123.val = 256 := by
        have h : v0123 = 256 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_256_zmod_p
      exact sll_close_cb4cb5_one_zero_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0010: S=4
      have hv0123_val : v0123.val = 16 := by
        have h : v0123 = 16 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16_zmod_p
      exact sll_close_cb4cb5_one_zero_case 4 (by omega) 16 4096 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0011: S=12
      have hv0123_val : v0123.val = 4096 := by
        have h : v0123 = 4096 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4096_zmod_p
      exact sll_close_cb4cb5_one_zero_case 12 (by omega) 4096 16 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0100: S=2
      have hv0123_val : v0123.val = 4 := by
        have h : v0123 = 4 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4_zmod_p
      exact sll_close_cb4cb5_one_zero_case 2 (by omega) 4 16384 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0101: S=10
      have hv0123_val : v0123.val = 1024 := by
        have h : v0123 = 1024 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_1024_zmod_p
      exact sll_close_cb4cb5_one_zero_case 10 (by omega) 1024 64 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0110: S=6
      have hv0123_val : v0123.val = 64 := by
        have h : v0123 = 64 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_64_zmod_p
      exact sll_close_cb4cb5_one_zero_case 6 (by omega) 64 1024 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0111: S=14
      have hv0123_val : v0123.val = 16384 := by
        have h : v0123 = 16384 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16384_zmod_p
      exact sll_close_cb4cb5_one_zero_case 14 (by omega) 16384 4 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1000: S=1
      have hv0123_val : v0123.val = 2 := by
        have h : v0123 = 2 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2_zmod_p
      exact sll_close_cb4cb5_one_zero_case 1 (by omega) 2 32768 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1001: S=9
      have hv0123_val : v0123.val = 512 := by
        have h : v0123 = 512 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_512_zmod_p
      exact sll_close_cb4cb5_one_zero_case 9 (by omega) 512 128 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1010: S=5
      have hv0123_val : v0123.val = 32 := by
        have h : v0123 = 32 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32_zmod_p
      exact sll_close_cb4cb5_one_zero_case 5 (by omega) 32 2048 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1011: S=13
      have hv0123_val : v0123.val = 8192 := by
        have h : v0123 = 8192 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8192_zmod_p
      exact sll_close_cb4cb5_one_zero_case 13 (by omega) 8192 8 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1100: S=3
      have hv0123_val : v0123.val = 8 := by
        have h : v0123 = 8 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8_zmod_p
      exact sll_close_cb4cb5_one_zero_case 3 (by omega) 8 8192 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1101: S=11
      have hv0123_val : v0123.val = 2048 := by
        have h : v0123 = 2048 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2048_zmod_p
      exact sll_close_cb4cb5_one_zero_case 11 (by omega) 2048 32 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1110: S=7
      have hv0123_val : v0123.val = 128 := by
        have h : v0123 = 128 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_128_zmod_p
      exact sll_close_cb4cb5_one_zero_case 7 (by omega) 128 512 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1111: S=15
      have hv0123_val : v0123.val = 32768 := by
        have h : v0123 = 32768 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32768_zmod_p
      exact sll_close_cb4cb5_one_zero_case 15 (by omega) 32768 2 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  · -- cb4 = 1, cb5 = 1: byte_shift = 3, Main[48] = 1. The all-ones case lives here.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [one_mul, mul_one] at h_su160 h_su161 h_su162 h_su163
    -- cb4 + cb5*2 = 1 + 2 = 3, so Main[48] = 1 (others = 0).
    have h_45_eq : Main[45] = 0 := by
      rcases h_su160 with h | h
      · exact h
      · exfalso
        have : (3 : ZMod p) = 0 := by linear_combination h
        exact val_3_ne_zero this
    have h_46_eq : Main[46] = 0 := by
      rcases h_su161 with h | h
      · exact h
      · exfalso
        have : (2 : ZMod p) = 0 := by linear_combination h
        exact val_2_ne_zero this
    have h_47_eq : Main[47] = 0 := by
      rcases h_su162 with h | h
      · exact h
      · exfalso
        have : (1 : ZMod p) = 0 := by linear_combination h
        exact h_1_ne_0 this
    have h_48_eq : Main[48] = 1 := by
      have := h_su_sum
      rw [h_45_eq, h_46_eq, h_47_eq] at this
      linear_combination this
    -- Extract from rest: with Main[48] = 1, the last 4 conjuncts (positions 13-16) give
    -- a0 = 0, a1 = 0, a2 = 0, a3 = lr0.
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h_a0_48, h_a1_48, h_a2_48, h_a3_48, _rest_other⟩ := rest
    have h_a0_eq : a0 = 0 := by
      rcases h_a0_48 with h | h
      · exfalso; rw [h_48_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a1_eq : a1 = 0 := by
      rcases h_a1_48 with h | h
      · exfalso; rw [h_48_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a2_eq : a2 = 0 := by
      rcases h_a2_48 with h | h
      · exfalso; rw [h_48_eq] at h; exact h_1_ne_0 h
      · exact h
    have h_a3_eq : a3 = lr0 := by
      rcases h_a3_48 with h | h
      · exfalso; rw [h_48_eq] at h; exact h_1_ne_0 h
      · exact h
    -- Substitute a_j and expand lr_0 in the goal.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr0]
    -- 16-way case split on cb0..cb3.
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- cb0..3 = 0000: S=0, M=1, N=65536.
      have hv0123_val : v0123.val = 1 := by
        have h : v0123 = 1 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact h_v1_val
      exact sll_close_cb4cb5_one_one_case 0 (by omega) 1 65536 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0001: S=8, M=256, N=256.
      have hv0123_val : v0123.val = 256 := by
        have h : v0123 = 256 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_256_zmod_p
      exact sll_close_cb4cb5_one_one_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0010: S=4, M=16, N=4096.
      have hv0123_val : v0123.val = 16 := by
        have h : v0123 = 16 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16_zmod_p
      exact sll_close_cb4cb5_one_one_case 4 (by omega) 16 4096 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0011: S=12, M=4096, N=16.
      have hv0123_val : v0123.val = 4096 := by
        have h : v0123 = 4096 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4096_zmod_p
      exact sll_close_cb4cb5_one_one_case 12 (by omega) 4096 16 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0100: S=2, M=4, N=16384.
      have hv0123_val : v0123.val = 4 := by
        have h : v0123 = 4 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_4_zmod_p
      exact sll_close_cb4cb5_one_one_case 2 (by omega) 4 16384 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0101: S=10, M=1024, N=64.
      have hv0123_val : v0123.val = 1024 := by
        have h : v0123 = 1024 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_1024_zmod_p
      exact sll_close_cb4cb5_one_one_case 10 (by omega) 1024 64 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0110: S=6, M=64, N=1024.
      have hv0123_val : v0123.val = 64 := by
        have h : v0123 = 64 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_64_zmod_p
      exact sll_close_cb4cb5_one_one_case 6 (by omega) 64 1024 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 0111: S=14, M=16384, N=4.
      have hv0123_val : v0123.val = 16384 := by
        have h : v0123 = 16384 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_16384_zmod_p
      exact sll_close_cb4cb5_one_one_case 14 (by omega) 16384 4 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1000: S=1, M=2, N=32768.
      have hv0123_val : v0123.val = 2 := by
        have h : v0123 = 2 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2_zmod_p
      exact sll_close_cb4cb5_one_one_case 1 (by omega) 2 32768 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1001: S=9, M=512, N=128.
      have hv0123_val : v0123.val = 512 := by
        have h : v0123 = 512 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_512_zmod_p
      exact sll_close_cb4cb5_one_one_case 9 (by omega) 512 128 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1010: S=5, M=32, N=2048.
      have hv0123_val : v0123.val = 32 := by
        have h : v0123 = 32 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32_zmod_p
      exact sll_close_cb4cb5_one_one_case 5 (by omega) 32 2048 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1011: S=13, M=8192, N=8.
      have hv0123_val : v0123.val = 8192 := by
        have h : v0123 = 8192 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8192_zmod_p
      exact sll_close_cb4cb5_one_one_case 13 (by omega) 8192 8 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1100: S=3, M=8, N=8192.
      have hv0123_val : v0123.val = 8 := by
        have h : v0123 = 8 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_8_zmod_p
      exact sll_close_cb4cb5_one_one_case 3 (by omega) 8 8192 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1101: S=11, M=2048, N=32.
      have hv0123_val : v0123.val = 2048 := by
        have h : v0123 = 2048 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_2048_zmod_p
      exact sll_close_cb4cb5_one_one_case 11 (by omega) 2048 32 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1110: S=7, M=128, N=512.
      have hv0123_val : v0123.val = 128 := by
        have h : v0123 = 128 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_128_zmod_p
      exact sll_close_cb4cb5_one_one_case 7 (by omega) 128 512 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0..3 = 1111: S=15, M=32768, N=2.
      have hv0123_val : v0123.val = 32768 := by
        have h : v0123 = 32768 := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
        rw [h]; exact val_32768_zmod_p
      exact sll_close_cb4cb5_one_one_case 15 (by omega) 32768 2 (by decide) (by omega) rfl rfl
        hv0123_val
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec

end sll

end ShiftLeft
