import SP1Chips.ShiftRight.Common

namespace ShiftRight

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
-- Unused variables expected because many proofs are currently stopped.
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000
set_option linter.style.longLine false


section srl

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 400000000 in
-- 400M heartbeats: 4-way byte_shift × 16-way cb0..cb3 rcases × per-case wrapper call.
-- Shared proof body for `spec.srl` and `spec.srli`.
private lemma spec.srl_common (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold) (eq_srl : Main[64] = 1) :
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
      execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[25], Main[26], Main[27], Main[28]] .SRL := by
  -- Setup.
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h_real := is_real_eq_one_of_srl Main cstrs eq_srl
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs h_real
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
  obtain ⟨c0_16, _c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64 is_U64_c
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ] at b0_16 b1_16 b2_16 b3_16 c0_16
  obtain ⟨sop_1, _, _, _⟩ := single_op Main cstrs
  have ⟨h_no_sra, h_no_srlw, h_no_sraw⟩ := sop_1 eq_srl
  -- Open the iff.
  change List.Forall SP1Constraint.toProp (constraints Main) at cstrs
  rw [allHold_constraints_iff] at cstrs
  -- Set up local names for Main[i] indices.
  set b0 := Main[15]; set b1 := Main[16]; set b2 := Main[17]; set b3 := Main[18]
  set c0 := Main[25]; set c1 := Main[26]; set c2 := Main[27]; set c3 := Main[28]
  set a0 := Main[32]; set a1 := Main[33]; set a2 := Main[34]; set a3 := Main[35]
  set msb_b := Main[36]; set msb_srw := Main[37]
  set cb0 := Main[38]; set cb1 := Main[39]; set cb2 := Main[40]
  set cb3 := Main[41]; set cb4 := Main[42]; set cb5 := Main[43]
  set smv := Main[44]; set v0123 := Main[45]; set v012 := Main[46]; set v01 := Main[47]
  set ll0 := Main[48]; set ll1 := Main[49]; set ll2 := Main[50]; set ll3 := Main[51]
  set hl0 := Main[52]; set hl1 := Main[53]; set hl2 := Main[54]; set hl3 := Main[55]
  set lr0 := Main[56]; set lr1 := Main[57]; set lr2 := Main[58]; set lr3 := Main[59]
  set su160 := Main[60]; set su161 := Main[61]; set su162 := Main[62]; set su163 := Main[63]
  -- Destructure.
  obtain ⟨_, _, _, _, _,
           _, _, _, _, _, _,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
           h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163,
           one_of_su16s,
           eq_v01, eq_v012, eq_v0123,
           lt_ll0', lt_lh0', h_b0_dec, lt_ll1', lt_lh1', h_b1_dec,
           lt_ll2', lt_lh2', h_b2_dec, lt_ll3', lt_lh3', h_b3_dec,
           eq_lr0, eq_lr1, eq_lr2, eq_lr3,
           w_msb_b, eq_smv, w_msb_srv,
           sr_00, sr_01, sr_02, sr_03,
           sr_10, sr_11, sr_12, sr_13,
           sr_20, sr_21, sr_22, sr_23,
           sr_30, sr_31, sr_32, sr_33,
           srw_00, srw_01, srw_10, srw_11,
           srw_w2, srw_w3,
           _h_M13⟩ := cstrs
  -- h_sum_ne and bound specializations.
  have h_v0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_v1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := by
    intro h; rw [h] at h_v1_val; rw [h_v0_val] at h_v1_val; exact zero_ne_one h_v1_val
  have h_sum_ne : ¬ Main[64] + Main[65] + Main[66] + Main[67] = 0 := by
    intro h
    rw [eq_srl, h_no_sra, h_no_srlw, h_no_sraw] at h
    simp only [add_zero] at h
    exact h_one_ne_zero h
  have lt_ll0 := lt_ll0' h_sum_ne
  have lt_lh0 := lt_lh0' h_sum_ne
  have lt_ll1 := lt_ll1' h_sum_ne
  have lt_lh1 := lt_lh1' h_sum_ne
  have lt_ll2 := lt_ll2' h_sum_ne
  have lt_lh2 := lt_lh2' h_sum_ne
  have lt_ll3 := lt_ll3' h_sum_ne
  have lt_lh3 := lt_lh3' h_sum_ne
  -- Goal manipulation: reduce to nat arithmetic.
  rw [← BitVec.toNat_inj]
  simp only [execute_RTYPE_pure_w]
  rw [BitVec.ushiftRight_eq']
  rw [BitVec.toNat_ushiftRight]
  simp only [BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  -- Reduce shift count `(toBitVec64 c).toNat % 2^6` to `c0.val % 64`.
  have h_shift_eq : (Word.toBitVec64 #v[c0, c1, c2, c3]).toNat % 2 ^ 6 = c0.val % 64 := by
    rw [Word.toBitVec64_toNat is_U64_c, Word.toNat_def]
    simp; omega
  rw [h_shift_eq]; clear h_shift_eq
  -- Reduce c0.val % 64 to (cb_sum_zmod).val via is_mod_64. Val-of-sum form for wrapper compatibility.
  have h_cb_sum_lt : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val < 64 := by
    have hb0 : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb1 : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb2 : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb3 : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb4 : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb5 : cb5.val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have h_eq := cb_sum_val_eq b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
    omega
  have h_val_10 : (10 : ZMod p).val = 10 := by
    rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have h_diff := diff h_sum_ne
  rw [h_val_10] at h_diff
  have h_c0_mod : c0.val % 64 = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val := by
    apply is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)
    · exact h_cb_sum_lt
    · exact c0_16
    · exact h_diff
  rw [h_c0_mod]; clear h_c0_mod h_diff h_cb_sum_lt
  -- De-gate h_b2_dec, h_b3_dec (LHS has `* (Main[64] + Main[65])` factor in iff;
  -- for SRL/SRA arm, this equals 1 and disappears).
  rw [h_no_sra, eq_srl] at h_b2_dec h_b3_dec
  simp only [add_zero, mul_one] at h_b2_dec h_b3_dec
  -- Pre-process disjunct gates: substitute h_no_sra/srlw/sraw and eq_srl.
  rw [h_no_sra] at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
                   sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
                   h_su160 h_su161 h_su162 h_su163 one_of_su16s
  rw [h_no_srlw] at w_msb_b w_msb_srv one_of_su16s
  rw [h_no_sraw] at w_msb_srv one_of_su16s
  rw [eq_srl] at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
                  sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
                  h_su160 h_su161 h_su162 h_su163 one_of_su16s w_msb_b
  -- Reduce `1 + 0 = 0` (False) and `0 + 0 = 1` (False) disjuncts.
  simp only [add_zero, zero_add] at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
                                     sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
                                     h_su160 h_su161 h_su162 h_su163 one_of_su16s
                                     w_msb_b w_msb_srv
  -- Drop the False `(1 : ZMod p) = 0` disjunct from sr_**, w_msb_b, one_of_su16s.
  simp only [show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
    at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
       sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
       w_msb_b one_of_su16s
  -- Drop the False `(0 : ZMod p) = 1` disjunct from w_msb_srv.
  have h_zero_ne_one : (0 : ZMod p) ≠ 1 := fun h => h_one_ne_zero h.symm
  simp only [show ((0 : ZMod p) = 1) ↔ False from ⟨h_zero_ne_one, False.elim⟩, false_or]
    at w_msb_srv
  -- Now w_msb_b is `msb_b = 0`, w_msb_srv is `msb_srw = 0`, one_of_su16s is `su_sum = 1`,
  -- and each sr_** is `su16_? = 0 ∨ a_? = lr_?_or_correction`.
  have h_msb_b_zero : msb_b = 0 := w_msb_b
  have _h_msb_srw_zero : msb_srw = 0 := w_msb_srv
  -- smv = 0 (from eq_smv: smv = msb_b * v0123 with msb_b = 0).
  rw [h_msb_b_zero, zero_mul] at eq_smv
  -- Specialize one_of_su16s.
  have h_su_sum : su160 + su161 + su162 + su163 = 1 := one_of_su16s
  -- Simplify mul_one in h_su16k.
  simp only [mul_one] at h_su160 h_su161 h_su162 h_su163
  -- Simplify correction terms in sr_** using msb_b = 0 and eq_smv (smv = 0).
  simp only [h_msb_b_zero, eq_smv, zero_mul, mul_zero, sub_zero, zero_sub, neg_zero,
             add_zero, sub_self] at sr_03 sr_12 sr_13 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
  -- BISECT: truncate body at outer rcases with sorry to see if trigger is in 4x16 case-split.
  rcases b_cb5 with hcb5 | hcb5 <;> rcases b_cb4 with hcb4 | hcb4
  · -- byte_shift = 0: cb4 = 0, cb5 = 0. su160 = 1, others = 0.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [zero_add, zero_mul, mul_zero, add_zero] at h_su160 h_su161 h_su162 h_su163
    -- h_su161: su161 = 0 ∨ (0 = 1); RHS False ⇒ su161 = 0.
    -- h_su162: su162 = 0 ∨ (0 = 2); RHS False ⇒ su162 = 0.
    -- h_su163: su163 = 0 ∨ (0 = 3); RHS False ⇒ su163 = 0.
    have h_su161_zero : su161 = 0 :=
      h_su161.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
    have h_su162_zero : su162 = 0 :=
      h_su162.resolve_right (fun h => val_2_ne_zero (by linear_combination -h))
    have h_su163_zero : su163 = 0 :=
      h_su163.resolve_right (fun h => val_3_ne_zero (by linear_combination -h))
    have h_su160_eq : su160 = 1 := by
      have := h_su_sum
      rw [h_su161_zero, h_su162_zero, h_su163_zero] at this
      linear_combination this
    -- Extract a_j = lr_j from sr_00..sr_03 (using su160 = 1).
    have h_a0_eq : a0 = lr0 :=
      sr_00.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
    have h_a1_eq : a1 = lr1 :=
      sr_01.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
    have h_a2_eq : a2 = lr2 :=
      sr_02.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
    have h_a3_eq : a3 = lr3 :=
      sr_03.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
    -- Substitute a_j = lr_j in goal, expand lr_j via eq_lr*.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr0, eq_lr1, eq_lr2, eq_lr3]
    -- 16-way rcases on cb0..cb3.
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- cb0=cb1=cb2=cb3=0: S=0, M=65536, N=1.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=0, cb3=1: S=8, M=256, N=256.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=0: S=4, M=4096, N=16.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=1: S=12, M=16, N=4096.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=0: S=2, M=16384, N=4.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=1: S=10, M=64, N=1024.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=0: S=6, M=1024, N=64.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=1: S=14, M=4, N=16384.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=0: S=1, M=32768, N=2.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=1: S=9, M=128, N=512.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=0: S=5, M=2048, N=32.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=1: S=13, M=8, N=8192.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=0: S=3, M=8192, N=8.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=1: S=11, M=32, N=2048.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=0: S=7, M=512, N=128.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=1: S=15, M=2, N=32768.
      exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  · -- byte_shift = 1: cb4 = 1, cb5 = 0. su161 = 1, others = 0.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul, mul_one] at h_su160 h_su161 h_su162 h_su163
    -- h_su160: su160 = 0 ∨ (1 = 0) ⇒ su160 = 0.
    -- h_su161: su161 = 0 ∨ (1 = 1) ⇒ trivially holds, no info.
    -- h_su162: su162 = 0 ∨ (1 = 2) ⇒ su162 = 0.
    -- h_su163: su163 = 0 ∨ (1 = 3) ⇒ su163 = 0.
    have h_su160_zero : su160 = 0 :=
      h_su160.resolve_right h_one_ne_zero
    have h_su162_zero : su162 = 0 :=
      h_su162.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
    have h_su163_zero : su163 = 0 :=
      h_su163.resolve_right (fun h => val_2_ne_zero (by linear_combination -h))
    have h_su161_eq : su161 = 1 := by
      have := h_su_sum
      rw [h_su160_zero, h_su162_zero, h_su163_zero] at this
      linear_combination this
    -- Extract a_j = lr_{j+1} from sr_10..sr_13. (a_3 = 0 for SRL).
    have h_a0_eq : a0 = lr1 :=
      sr_10.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
    have h_a1_eq : a1 = lr2 :=
      sr_11.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
    have h_a2_eq : a2 = lr3 :=
      sr_12.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
    have h_a3_eq : a3 = 0 :=
      sr_13.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
    -- Substitute a_j = lr_{j+1} (or 0) in goal, expand lr_j via eq_lr1, eq_lr2, eq_lr3.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr1, eq_lr2, eq_lr3]
    -- 16-way rcases on cb0..cb3.
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- cb0=cb1=cb2=cb3=0: S=0, M=65536, N=1.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=0, cb3=1: S=8, M=256, N=256.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=0: S=4, M=4096, N=16.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=1: S=12, M=16, N=4096.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=0: S=2, M=16384, N=4.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=1: S=10, M=64, N=1024.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=0: S=6, M=1024, N=64.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=1: S=14, M=4, N=16384.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=0: S=1, M=32768, N=2.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=1: S=9, M=128, N=512.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=0: S=5, M=2048, N=32.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=1: S=13, M=8, N=8192.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=0: S=3, M=8192, N=8.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=1: S=11, M=32, N=2048.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=0: S=7, M=512, N=128.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=1: S=15, M=2, N=32768.
      exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  · -- byte_shift = 2: cb5 = 1, cb4 = 0. su162 = 1, others = 0.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul, mul_one] at h_su160 h_su161 h_su162 h_su163
    -- cb4 + cb5*2 = 0 + 1*2 = 2.
    -- h_su160: su160 = 0 ∨ 2 = 0 ⇒ su160 = 0.
    -- h_su161: su161 = 0 ∨ 2 = 1 ⇒ su161 = 0.
    -- h_su162: su162 = 0 ∨ 2 = 2 ⇒ trivially holds.
    -- h_su163: su163 = 0 ∨ 2 = 3 ⇒ su163 = 0.
    have h_su160_zero : su160 = 0 :=
      h_su160.resolve_right val_2_ne_zero
    have h_su161_zero : su161 = 0 :=
      h_su161.resolve_right (fun h => h_one_ne_zero (by linear_combination h))
    have h_su163_zero : su163 = 0 :=
      h_su163.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
    have h_su162_eq : su162 = 1 := by
      have := h_su_sum
      rw [h_su160_zero, h_su161_zero, h_su163_zero] at this
      linear_combination this
    -- Extract a_j = lr_{j+2} from sr_20..sr_23. (a_2 = a_3 = 0 for SRL).
    have h_a0_eq : a0 = lr2 :=
      sr_20.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
    have h_a1_eq : a1 = lr3 :=
      sr_21.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
    have h_a2_eq : a2 = 0 :=
      sr_22.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
    have h_a3_eq : a3 = 0 :=
      sr_23.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
    -- Substitute a_j in goal, expand lr_2, lr_3.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr2, eq_lr3]
    -- 16-way rcases on cb0..cb3.
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- cb0=cb1=cb2=cb3=0: S=0, M=65536, N=1.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=0, cb3=1: S=8.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=0: S=4.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=1: S=12.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=0: S=2.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=1: S=10.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=0: S=6.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=1: S=14.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=0: S=1.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=1: S=9.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=0: S=5.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=1: S=13.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=0: S=3.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=1: S=11.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=0: S=7.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=1: S=15.
      exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  · -- byte_shift = 3: cb5 = 1, cb4 = 1. su163 = 1, others = 0.
    rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
    simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul, mul_one] at h_su160 h_su161 h_su162 h_su163
    -- cb4 + cb5*2 = 1 + 1*2 = 3.
    -- h_su160: su160 = 0 ∨ 3 = 0 ⇒ su160 = 0.
    -- h_su161: su161 = 0 ∨ 3 = 1 ⇒ su161 = 0.
    -- h_su162: su162 = 0 ∨ 3 = 2 ⇒ su162 = 0.
    -- h_su163: su163 = 0 ∨ 3 = 3 ⇒ trivially holds.
    have h_su160_zero : su160 = 0 :=
      h_su160.resolve_right (fun h => val_3_ne_zero (by linear_combination h))
    have h_su161_zero : su161 = 0 :=
      h_su161.resolve_right (fun h => val_2_ne_zero (by linear_combination h))
    have h_su162_zero : su162 = 0 :=
      h_su162.resolve_right (fun h => h_one_ne_zero (by linear_combination h))
    have h_su163_eq : su163 = 1 := by
      have := h_su_sum
      rw [h_su160_zero, h_su161_zero, h_su162_zero] at this
      linear_combination this
    -- Extract a_j = lr_3 (or 0) from sr_30..sr_33.
    have h_a0_eq : a0 = lr3 :=
      sr_30.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
    have h_a1_eq : a1 = 0 :=
      sr_31.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
    have h_a2_eq : a2 = 0 :=
      sr_32.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
    have h_a3_eq : a3 = 0 :=
      sr_33.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
    -- Substitute a_j in goal, expand lr_3.
    rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr3]
    -- 16-way rcases on cb0..cb3.
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- cb0=cb1=cb2=cb3=0: S=0.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=0, cb3=1: S=8.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=0: S=4.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=0, cb2=1, cb3=1: S=12.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=0: S=2.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=0, cb3=1: S=10.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=0: S=6.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=0, cb1=1, cb2=1, cb3=1: S=14.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=0: S=1.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=0, cb3=1: S=9.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=0: S=5.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=0, cb2=1, cb3=1: S=13.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=0: S=3.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=0, cb3=1: S=11.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=0: S=7.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- cb0=1, cb1=1, cb2=1, cb3=1: S=15.
      exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
        h_b0_dec h_b1_dec h_b2_dec h_b3_dec

lemma spec.srl (Main : Vector (ZMod p) 69) (h : is_srl Main) :
    (constraints Main).allHold →
      Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRL :=
  fun cstrs => spec.srl_common Main cstrs h.1

lemma spec.srli (Main : Vector (ZMod p) 69) (h : is_srli Main) :
    (constraints Main).allHold →
      Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRL :=
  fun cstrs => spec.srl_common Main cstrs h.1

end srl

end ShiftRight
