              have h_sign : HWord.toInt_poly #v[r0, r1] = 0 ∨
                  (HWord.toInt_poly #v[r0, r1]).sign = (HWord.toInt_poly #v[b0, b1]).sign := by
                rcases b_b_neg with b_msb_nneg | b_msb_neg
                · simp [b_msb_nneg] at *
                  simp [r_neg_b_neg] at *
                  by_cases rz : HWord.toInt_poly #v[r0, r1] = 0 <;> [ (left; exact rz); right ]
                  rw [HWord.sign_cases_poly is_U32_bl, HWord.sign_cases_poly is_U32_rl]
                  simp [HWord.isNegative_poly]
                  split_ifs with hr hb hw hb hw <;> try omega
                  have rpos : HWord.toInt_poly #v[r0, r1] > 0 := by
                    simp [HWord.toInt_poly, HWord.isNegative_poly, HWord.toNat_poly] at rz ⊢
                    split_ifs; omega
                  rw [h_prod] at hw
                  clear *- rpos h_abs hw
                  simp [Int.abs_cases] at h_abs; rw [if_pos (by omega)] at h_abs
                  set q := HWord.toInt_poly #v[q0, q1] with hq_def
                  set c := HWord.toInt_poly #v[c0, c1] with hc_def
                  set r := HWord.toInt_poly #v[r0, r1] with hr_def
                  apply Int.split_nzp q <;> intro hq <;> [ skip; simp_all; skip ]
                  all_goals
                    have : c * q > r := by split_ifs at * <;> nlinarith
                    nlinarith
                · -- b_msb_neg : msb_b = 1
                  have sign_b : (HWord.toInt_poly #v[b0, b1]).sign = -1 := sgn_msb_b b_msb_neg
                  rcases b_rem_neg with rem_nneg | rem_neg
                  · -- msb_rem = 0 ⇒ r2 = r3 = 0; r_pos_b_pos must give r_sum = 0
                    have hr2 : r2 = 0 := by rw [w_eq_r2_w, rem_nneg]; ring
                    have hr3 : r3 = 0 := by rw [w_eq_r3_w, rem_nneg]; ring
                    have hrz : r0 + r1 + r2 + r3 = 0 := by
                      rcases r_pos_b_pos with hrz | hrem | hb
                      · exact hrz
                      · rw [rem_nneg] at hrem; exact absurd hrem (by simp)
                      · rw [b_msb_neg] at hb; exact absurd hb (by simp)
                    rw [hr2, hr3, add_zero, add_zero] at hrz
                    have hp : r0.val + r1.val < p := by
                      have := Fact.out (p := 2 ^ 17 < p); omega
                    have hsum : r0.val + r1.val = 0 := by
                      have := congrArg ZMod.val hrz
                      rwa [ZMod.val_add_of_lt hp, ZMod.val_zero] at this
                    have hr0 : r0 = 0 := (ZMod.val_eq_zero r0).mp (by omega)
                    have hr1 : r1 = 0 := (ZMod.val_eq_zero r1).mp (by omega)
                    left
                    simp [HWord.toInt_poly, HWord.isNegative_poly, HWord.toNat_poly, hr0, hr1]
                  · -- msb_rem = 1: sgn_msb_rem fires, sign r = -1 = sign b
                    right
                    rw [sgn_msb_rem rem_neg, sign_b]
              rw [tdiv_tmod_unique_full cnz]
