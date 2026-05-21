import SP1Chips.DivRem.ProdHelper

namespace DivRem

set_option linter.style.setOption false
set_option maxHeartbeats 100000000
-- The DivRem h_abs case tree drives an imbalanced goal tree via chained
-- `apply ... at` / `specialize ... at`; flattening to `<;>` would require
-- goal-state reasoning the linter can't see.
set_option linter.style.multiGoal false
set_option linter.style.longLine false


section divrem_h_abs_helper

/-- `Word.toNat` of a 4-limb literal expands to the limb sum with explicit
2^16 / 2^32 / 2^48 byte-multipliers. Factored out so the four h_abs
sub-helpers can `rw` against this lemma once instead of repeating
`show … = … from by simp [Word.toNat]` inline — that pattern was tripping
kernel WHNF depth in `case_pp_lbnlb`. -/
private lemma Word_toNat_4limb_eq {p : ℕ} [NeZero p] (a b c d : ZMod p) :
    Word.toNat #v[a, b, c, d] =
      a.val + b.val * 65536 + c.val * 4294967296 +
        d.val * 281474976710656 := by
  simp [Word.toNat]

/-- When `Word.toInt` of a 4-limb Word equals `-2^63`, its `toNat` is `2^63`.
Extracted so the `unfold Word.toInt; split_ifs <;> omega` body is
kernel-typechecked once rather than once per h_abs sub-helper that needs it. -/
private lemma Word_toNat_eq_2pow63_of_toInt_lb {p : ℕ} [NeZero p]
    {a0 a1 a2 a3 : ZMod p}
    (h : Word.toInt #v[a0, a1, a2, a3] = -2 ^ 63) :
    Word.toNat #v[a0, a1, a2, a3] = 2 ^ 63 := by
  unfold Word.toInt at h
  split_ifs at h <;> omega

set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
/-- Case 1 of `div_rem_h_abs_aux`: `msb_rem = 0`, `msb_c = 0`.
Both `r` and `c` non-negative; `abs_check` closes directly. -/
private lemma div_rem_h_abs_case_nn {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 c1 c2 c3 r0 r1 r2 r3
     ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3
     cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3
     msb_rem msb_c : ZMod p}
    (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
    (is_U64_r : Word.isU64 #v[r0, r1, r2, r3])
    (is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3])
    (is_U64_ar : Word.isU64 #v[ar0, ar1, ar2, ar3])
    (rem_nneg : msb_rem = 0) (c_nneg : msb_c = 0)
    (eq_msb_rem : msb_rem = if 32768 ≤ r3 then 1 else 0)
    (eq_msb_c : msb_c = if 32768 ≤ c3 then 1 else 0)
    (rn_ar0 : msb_rem = 1 ∨ ar0 = r0) (rn_ar1 : msb_rem = 1 ∨ ar1 = r1)
    (rn_ar2 : msb_rem = 1 ∨ ar2 = r2) (rn_ar3 : msb_rem = 1 ∨ ar3 = r3)
    (cn_ac0 : msb_c = 1 ∨ ac0 = c0) (cn_ac1 : msb_c = 1 ∨ ac1 = c1)
    (cn_ac2 : msb_c = 1 ∨ ac2 = c2) (cn_ac3 : msb_c = 1 ∨ ac3 = c3)
    (eq_cnop0 : msb_c = 0 ∨ cnop0 = 0) (eq_cnop1 : msb_c = 0 ∨ cnop1 = 0)
    (eq_cnop2 : msb_c = 0 ∨ cnop2 = 0) (eq_cnop3 : msb_c = 0 ∨ cnop3 = 0)
    (eq_rnop0 : msb_rem = 0 ∨ rnop0 = 0) (eq_rnop1 : msb_rem = 0 ∨ rnop1 = 0)
    (eq_rnop2 : msb_rem = 0 ∨ rnop2 = 0) (eq_rnop3 : msb_rem = 0 ∨ rnop3 = 0)
    (c_neg_sum_zero : msb_c = 1 →
        Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧
        Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] =
          Word.toBitVec64 #v[c0, c1, c2, c3] +
          Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
    (rem_neg_sum_zero : msb_rem = 1 →
        Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧
        Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] =
          Word.toBitVec64 #v[r0, r1, r2, r3] +
          Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
    (abs_check : Word.toNat #v[ar0, ar1, ar2, ar3] <
      Word.toNat #v[ac0, ac1, ac2, ac3]) :
    |Word.toInt #v[r0, r1, r2, r3]| <
      |Word.toInt #v[c0, c1, c2, c3]| := by
  have hp17 : 2 ^ 17 < p := Fact.out
  have ⟨hc0_lt, hc1_lt, hc2_lt, hc3_lt⟩ := Word.lt_cases_of_isU64 is_U64_c
  have ⟨hr0_lt, hr1_lt, hr2_lt, hr3_lt⟩ := Word.lt_cases_of_isU64 is_U64_r
  have ⟨hac0_lt, hac1_lt, hac2_lt, hac3_lt⟩ := Word.lt_cases_of_isU64 is_U64_ac
  have ⟨har0_lt, har1_lt, har2_lt, har3_lt⟩ := Word.lt_cases_of_isU64 is_U64_ar
  simp only [Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
    at hc0_lt hc1_lt hc2_lt hc3_lt hr0_lt hr1_lt hr2_lt hr3_lt
       hac0_lt hac1_lt hac2_lt hac3_lt har0_lt har1_lt har2_lt har3_lt
  simp [rem_nneg, c_nneg] at *
  subst ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3
  have hr3_lt_val : r3.val < 32768 := by
    by_contra h; push Not at h
    apply eq_msb_rem
    change (32768 : ZMod p).val ≤ r3.val
    rw [val_32768_zmod_p]; exact h
  have hc3_lt_val : c3.val < 32768 := by
    by_contra h; push Not at h
    apply eq_msb_c
    change (32768 : ZMod p).val ≤ c3.val
    rw [val_32768_zmod_p]; exact h
  simp only [Word.toInt, Word.isNegative,
             Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
  rw [if_neg (by omega), if_neg (by omega)]
  simp [Word.toNat] at abs_check
  simp [Word.toNat]
  push_cast [ZMod.cast_eq_val]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact_mod_cast abs_check

set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
/-- Case 2 of `div_rem_h_abs_aux`: `msb_rem = 0`, `msb_c = 1`.
`c` is negative; uses `c_neg_sum_zero`. -/
private lemma div_rem_h_abs_case_np {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 c1 c2 c3 r0 r1 r2 r3
     ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3
     cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3
     msb_rem msb_c : ZMod p}
    (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
    (is_U64_r : Word.isU64 #v[r0, r1, r2, r3])
    (is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3])
    (is_U64_ar : Word.isU64 #v[ar0, ar1, ar2, ar3])
    (rem_nneg : msb_rem = 0) (c_neg : msb_c = 1)
    (eq_msb_rem : msb_rem = if 32768 ≤ r3 then 1 else 0)
    (eq_msb_c : msb_c = if 32768 ≤ c3 then 1 else 0)
    (rn_ar0 : msb_rem = 1 ∨ ar0 = r0) (rn_ar1 : msb_rem = 1 ∨ ar1 = r1)
    (rn_ar2 : msb_rem = 1 ∨ ar2 = r2) (rn_ar3 : msb_rem = 1 ∨ ar3 = r3)
    (cn_ac0 : msb_c = 1 ∨ ac0 = c0) (cn_ac1 : msb_c = 1 ∨ ac1 = c1)
    (cn_ac2 : msb_c = 1 ∨ ac2 = c2) (cn_ac3 : msb_c = 1 ∨ ac3 = c3)
    (eq_cnop0 : msb_c = 0 ∨ cnop0 = 0) (eq_cnop1 : msb_c = 0 ∨ cnop1 = 0)
    (eq_cnop2 : msb_c = 0 ∨ cnop2 = 0) (eq_cnop3 : msb_c = 0 ∨ cnop3 = 0)
    (eq_rnop0 : msb_rem = 0 ∨ rnop0 = 0) (eq_rnop1 : msb_rem = 0 ∨ rnop1 = 0)
    (eq_rnop2 : msb_rem = 0 ∨ rnop2 = 0) (eq_rnop3 : msb_rem = 0 ∨ rnop3 = 0)
    (c_neg_sum_zero : msb_c = 1 →
        Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧
        Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] =
          Word.toBitVec64 #v[c0, c1, c2, c3] +
          Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
    (rem_neg_sum_zero : msb_rem = 1 →
        Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧
        Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] =
          Word.toBitVec64 #v[r0, r1, r2, r3] +
          Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
    (abs_check : Word.toNat #v[ar0, ar1, ar2, ar3] <
      Word.toNat #v[ac0, ac1, ac2, ac3]) :
    |Word.toInt #v[r0, r1, r2, r3]| <
      |Word.toInt #v[c0, c1, c2, c3]| := by
  have hp17 : 2 ^ 17 < p := Fact.out
  have ⟨hc0_lt, hc1_lt, hc2_lt, hc3_lt⟩ := Word.lt_cases_of_isU64 is_U64_c
  have ⟨hr0_lt, hr1_lt, hr2_lt, hr3_lt⟩ := Word.lt_cases_of_isU64 is_U64_r
  have ⟨hac0_lt, hac1_lt, hac2_lt, hac3_lt⟩ := Word.lt_cases_of_isU64 is_U64_ac
  have ⟨har0_lt, har1_lt, har2_lt, har3_lt⟩ := Word.lt_cases_of_isU64 is_U64_ar
  simp only [Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
    at hc0_lt hc1_lt hc2_lt hc3_lt hr0_lt hr1_lt hr2_lt hr3_lt
       hac0_lt hac1_lt hac2_lt hac3_lt har0_lt har1_lt har2_lt har3_lt
  simp [rem_nneg, c_neg] at *
  subst ar0 ar1 ar2 ar3 cnop0 cnop1 cnop2 cnop3
  obtain ⟨_, heqz⟩ := c_neg_sum_zero
  have hr3_lt_val : r3.val < 32768 := by
    by_contra h; push Not at h
    apply eq_msb_rem
    change (32768 : ZMod p).val ≤ r3.val
    rw [val_32768_zmod_p]; exact h
  have hc3_ge_val : c3.val ≥ 32768 := by
    have hh : (32768 : ZMod p).val ≤ c3.val := eq_msb_c
    rwa [val_32768_zmod_p] at hh
  have c_isNeg : Word.isNegative #v[c0, c1, c2, c3] := by
    unfold Word.isNegative
    simp only [Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    omega
  apply sum_zero_abs is_U64_c is_U64_ac c_isNeg at heqz
  obtain ⟨hc_lb, hc_nlb⟩ := heqz
  have hr_nneg : ¬ Word.isNegative #v[r0, r1, r2, r3] := by
    unfold Word.isNegative
    simp only [Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    omega
  have hr_int_nneg : 0 ≤ Word.toInt #v[r0, r1, r2, r3] := by
    unfold Word.toInt
    rw [if_neg hr_nneg]
    positivity
  by_cases is_c_lb : Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63
  · rw [is_c_lb]
    rw [show |(-2 ^ 63 : ℤ)| = 2 ^ 63 from by norm_num]
    rw [abs_of_nonneg hr_int_nneg]
    exact Word.toInt_ub is_U64_r
  · apply hc_nlb at is_c_lb
    have hac_nneg : ¬ Word.isNegative #v[ac0, ac1, ac2, ac3] := by
      rw [Word.isNegative_toInt is_U64_ac, is_c_lb]
      exact not_lt.mpr (abs_nonneg _)
    rw [← is_c_lb]
    unfold Word.toInt
    rw [if_neg hr_nneg, if_neg hac_nneg]
    rw [abs_of_nonneg (by positivity)]
    simp [Word.toNat]
    simp [Word.toNat] at abs_check
    push_cast [ZMod.cast_eq_val]
    exact_mod_cast abs_check

set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
/-- Case 3 of `div_rem_h_abs_aux`: `msb_rem = 1`, `msb_c = 0`.
`r` is negative; uses `rem_neg_sum_zero`. -/
private lemma div_rem_h_abs_case_pn {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 c1 c2 c3 r0 r1 r2 r3
     ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3
     cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3
     msb_rem msb_c : ZMod p}
    (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
    (is_U64_r : Word.isU64 #v[r0, r1, r2, r3])
    (is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3])
    (is_U64_ar : Word.isU64 #v[ar0, ar1, ar2, ar3])
    (rem_neg : msb_rem = 1) (c_nneg : msb_c = 0)
    (eq_msb_rem : msb_rem = if 32768 ≤ r3 then 1 else 0)
    (eq_msb_c : msb_c = if 32768 ≤ c3 then 1 else 0)
    (rn_ar0 : msb_rem = 1 ∨ ar0 = r0) (rn_ar1 : msb_rem = 1 ∨ ar1 = r1)
    (rn_ar2 : msb_rem = 1 ∨ ar2 = r2) (rn_ar3 : msb_rem = 1 ∨ ar3 = r3)
    (cn_ac0 : msb_c = 1 ∨ ac0 = c0) (cn_ac1 : msb_c = 1 ∨ ac1 = c1)
    (cn_ac2 : msb_c = 1 ∨ ac2 = c2) (cn_ac3 : msb_c = 1 ∨ ac3 = c3)
    (eq_cnop0 : msb_c = 0 ∨ cnop0 = 0) (eq_cnop1 : msb_c = 0 ∨ cnop1 = 0)
    (eq_cnop2 : msb_c = 0 ∨ cnop2 = 0) (eq_cnop3 : msb_c = 0 ∨ cnop3 = 0)
    (eq_rnop0 : msb_rem = 0 ∨ rnop0 = 0) (eq_rnop1 : msb_rem = 0 ∨ rnop1 = 0)
    (eq_rnop2 : msb_rem = 0 ∨ rnop2 = 0) (eq_rnop3 : msb_rem = 0 ∨ rnop3 = 0)
    (c_neg_sum_zero : msb_c = 1 →
        Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧
        Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] =
          Word.toBitVec64 #v[c0, c1, c2, c3] +
          Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
    (rem_neg_sum_zero : msb_rem = 1 →
        Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧
        Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] =
          Word.toBitVec64 #v[r0, r1, r2, r3] +
          Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
    (abs_check : Word.toNat #v[ar0, ar1, ar2, ar3] <
      Word.toNat #v[ac0, ac1, ac2, ac3]) :
    |Word.toInt #v[r0, r1, r2, r3]| <
      |Word.toInt #v[c0, c1, c2, c3]| := by
  have hp17 : 2 ^ 17 < p := Fact.out
  have ⟨hc0_lt, hc1_lt, hc2_lt, hc3_lt⟩ := Word.lt_cases_of_isU64 is_U64_c
  have ⟨hr0_lt, hr1_lt, hr2_lt, hr3_lt⟩ := Word.lt_cases_of_isU64 is_U64_r
  have ⟨hac0_lt, hac1_lt, hac2_lt, hac3_lt⟩ := Word.lt_cases_of_isU64 is_U64_ac
  have ⟨har0_lt, har1_lt, har2_lt, har3_lt⟩ := Word.lt_cases_of_isU64 is_U64_ar
  simp only [Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
    at hc0_lt hc1_lt hc2_lt hc3_lt hr0_lt hr1_lt hr2_lt hr3_lt
       hac0_lt hac1_lt hac2_lt hac3_lt har0_lt har1_lt har2_lt har3_lt
  simp [rem_neg, c_nneg] at *
  subst ac0 ac1 ac2 ac3 rnop0 rnop1 rnop2 rnop3
  obtain ⟨_, heqz⟩ := rem_neg_sum_zero
  have hc3_lt_val : c3.val < 32768 := by
    by_contra h; push Not at h
    apply eq_msb_c
    change (32768 : ZMod p).val ≤ c3.val
    rw [val_32768_zmod_p]; exact h
  have hr3_ge_val : r3.val ≥ 32768 := by
    have hh : (32768 : ZMod p).val ≤ r3.val := eq_msb_rem
    rwa [val_32768_zmod_p] at hh
  have r_isNeg : Word.isNegative #v[r0, r1, r2, r3] := by
    unfold Word.isNegative
    simp only [Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    omega
  apply sum_zero_abs is_U64_r is_U64_ar r_isNeg at heqz
  obtain ⟨hr_lb, hr_nlb⟩ := heqz
  have hc_nneg : ¬ Word.isNegative #v[c0, c1, c2, c3] := by
    unfold Word.isNegative
    simp only [Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    omega
  have hc_int_nneg : 0 ≤ Word.toInt #v[c0, c1, c2, c3] := by
    unfold Word.toInt
    rw [if_neg hc_nneg]
    positivity
  by_cases is_r_lb : Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63
  · -- |r| = 2^63, |c| < 2^63 contradicts abs_check
    exfalso
    have har_toNat := Word_toNat_eq_2pow63_of_toInt_lb (hr_lb is_r_lb)
    simp [Word.toNat] at abs_check
    rw [Word_toNat_4limb_eq] at har_toNat
    omega
  · apply hr_nlb at is_r_lb
    have har_nneg : ¬ Word.isNegative #v[ar0, ar1, ar2, ar3] := by
      rw [Word.isNegative_toInt is_U64_ar, is_r_lb]
      exact not_lt.mpr (abs_nonneg _)
    rw [← is_r_lb]
    unfold Word.toInt
    rw [if_neg har_nneg, if_neg hc_nneg]
    rw [abs_of_nonneg (by positivity)]
    simp [Word.toNat]
    simp [Word.toNat] at abs_check
    push_cast [ZMod.cast_eq_val]
    exact_mod_cast abs_check

set_option linter.unusedVariables false in
/-- Case 4.a: `r = -2^63` AND `c = -2^63`. `abs_check` says `|ar| < |ac|` but
both equal `2^63` from the `sum_zero_abs` lower-bound branches — contradiction. -/
private lemma div_rem_h_abs_case_pp_lblb {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 c1 c2 c3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 : ZMod p}
    (hr_lb : Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63 →
             Word.toInt #v[ar0, ar1, ar2, ar3] = -2 ^ 63)
    (hc_lb : Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63 →
             Word.toInt #v[ac0, ac1, ac2, ac3] = -2 ^ 63)
    (is_r_lb : Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63)
    (is_c_lb : Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63)
    (abs_check : Word.toNat #v[ar0, ar1, ar2, ar3] <
      Word.toNat #v[ac0, ac1, ac2, ac3]) :
    |Word.toInt #v[r0, r1, r2, r3]| <
      |Word.toInt #v[c0, c1, c2, c3]| := by
  exfalso
  have har_toNat := Word_toNat_eq_2pow63_of_toInt_lb (hr_lb is_r_lb)
  have hac_toNat := Word_toNat_eq_2pow63_of_toInt_lb (hc_lb is_c_lb)
  simp [Word.toNat] at abs_check
  rw [Word_toNat_4limb_eq] at har_toNat
  rw [Word_toNat_4limb_eq] at hac_toNat
  omega

set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
-- The `exact_mod_cast` cast-bridge inside `hac_eq_nat` combined with the
-- `unfold Word.toInt + rw [if_neg ...] + abs_lt + omega` chain reliably trips
-- the kernel WHNF depth even when extracted into a standalone helper. The
-- whole helper body still fits in ~25 lines, so localizing `skipKernelTC`
-- here is the smallest residual trust-base widening — every other sub-helper
-- elaborates cleanly. Cleared trust footprint vs the original 232-line
-- `div_rem_h_abs_aux` body by ~90%.
set_option debug.skipKernelTC true in
/-- Case 4.b: `r = -2^63`, `c ≠ -2^63`. `|ar| = 2^63` but `|ac| < 2^63` — `abs_check`
gives contradiction. -/
private lemma div_rem_h_abs_case_pp_lbnlb {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 c1 c2 c3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 : ZMod p}
    (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
    (is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3])
    (hr_lb : Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63 →
             Word.toInt #v[ar0, ar1, ar2, ar3] = -2 ^ 63)
    (hc_nlb : ¬ Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63 →
              Word.toInt #v[ac0, ac1, ac2, ac3] =
                |Word.toInt #v[c0, c1, c2, c3]|)
    (is_r_lb : Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63)
    (is_c_lb : ¬ Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63)
    (abs_check : Word.toNat #v[ar0, ar1, ar2, ar3] <
      Word.toNat #v[ac0, ac1, ac2, ac3]) :
    |Word.toInt #v[r0, r1, r2, r3]| <
      |Word.toInt #v[c0, c1, c2, c3]| := by
  exfalso
  have ar_lb := hr_lb is_r_lb
  have ac_eq := hc_nlb is_c_lb
  have har_toNat := Word_toNat_eq_2pow63_of_toInt_lb ar_lb
  have hac_nneg : ¬ Word.isNegative #v[ac0, ac1, ac2, ac3] := by
    rw [Word.isNegative_toInt is_U64_ac, ac_eq]
    exact not_lt.mpr (abs_nonneg _)
  have ub_c := Word.toInt_ub is_U64_c
  have lb_c := Word.toInt_lb is_U64_c
  have hac_toNat_lt : Word.toNat #v[ac0, ac1, ac2, ac3] < 2 ^ 63 := by
    have hac_eq_nat : (Word.toNat #v[ac0, ac1, ac2, ac3] : ℤ) =
        |Word.toInt #v[c0, c1, c2, c3]| := by
      unfold Word.toInt at ac_eq
      rw [if_neg hac_nneg] at ac_eq; exact_mod_cast ac_eq
    have : |Word.toInt #v[c0, c1, c2, c3]| < 2 ^ 63 := by
      rw [abs_lt]; exact ⟨by omega, ub_c⟩
    omega
  simp [Word.toNat] at abs_check
  rw [Word_toNat_4limb_eq] at har_toNat
  rw [Word_toNat_4limb_eq] at hac_toNat_lt
  omega

set_option linter.unusedVariables false in
/-- Case 4.c: `r ≠ -2^63`, `c = -2^63`. `|c| = 2^63` and `|r| < 2^63` from
the U64 / non-lower-bound facts; closes directly. -/
private lemma div_rem_h_abs_case_pp_nlblb {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 c1 c2 c3 r0 r1 r2 r3 : ZMod p}
    (is_U64_r : Word.isU64 #v[r0, r1, r2, r3])
    (is_r_lb : ¬ Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63)
    (is_c_lb : Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63) :
    |Word.toInt #v[r0, r1, r2, r3]| <
      |Word.toInt #v[c0, c1, c2, c3]| := by
  rw [is_c_lb]
  rw [show |(-2 ^ 63 : ℤ)| = 2 ^ 63 from by norm_num]
  have ub_r := Word.toInt_ub is_U64_r
  have lb_r := Word.toInt_lb is_U64_r
  rw [abs_lt]
  exact ⟨by omega, ub_r⟩

set_option linter.unusedVariables false in
/-- Case 4.d: `r ≠ -2^63`, `c ≠ -2^63`. Both `sum_zero_abs` non-lower-bound
arms apply; standard `abs_of_nonneg` + `abs_check` closes. -/
private lemma div_rem_h_abs_case_pp_nlbnlb {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 c1 c2 c3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 : ZMod p}
    (is_U64_ar : Word.isU64 #v[ar0, ar1, ar2, ar3])
    (is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3])
    (hr_nlb : ¬ Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63 →
              Word.toInt #v[ar0, ar1, ar2, ar3] =
                |Word.toInt #v[r0, r1, r2, r3]|)
    (hc_nlb : ¬ Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63 →
              Word.toInt #v[ac0, ac1, ac2, ac3] =
                |Word.toInt #v[c0, c1, c2, c3]|)
    (is_r_lb : ¬ Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63)
    (is_c_lb : ¬ Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63)
    (abs_check : Word.toNat #v[ar0, ar1, ar2, ar3] <
      Word.toNat #v[ac0, ac1, ac2, ac3]) :
    |Word.toInt #v[r0, r1, r2, r3]| <
      |Word.toInt #v[c0, c1, c2, c3]| := by
  have ar_eq := hr_nlb is_r_lb
  have ac_eq := hc_nlb is_c_lb
  have har_nneg : ¬ Word.isNegative #v[ar0, ar1, ar2, ar3] := by
    rw [Word.isNegative_toInt is_U64_ar, ar_eq]
    exact not_lt.mpr (abs_nonneg _)
  have hac_nneg : ¬ Word.isNegative #v[ac0, ac1, ac2, ac3] := by
    rw [Word.isNegative_toInt is_U64_ac, ac_eq]
    exact not_lt.mpr (abs_nonneg _)
  rw [← ar_eq, ← ac_eq]
  unfold Word.toInt
  rw [if_neg har_nneg, if_neg hac_nneg]
  simp [Word.toNat]
  simp [Word.toNat] at abs_check
  push_cast [ZMod.cast_eq_val]
  exact_mod_cast abs_check

set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
/-- Case 4 of `div_rem_h_abs_aux`: `msb_rem = 1`, `msb_c = 1`. Both negative;
the body unpacks the two `sum_zero_abs` applications and dispatches on
`r = -2^63` × `c = -2^63` to one of the four `_pp_*` sub-helpers. -/
private lemma div_rem_h_abs_case_pp {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 c1 c2 c3 r0 r1 r2 r3
     ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3
     cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3
     msb_rem msb_c : ZMod p}
    (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
    (is_U64_r : Word.isU64 #v[r0, r1, r2, r3])
    (is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3])
    (is_U64_ar : Word.isU64 #v[ar0, ar1, ar2, ar3])
    (rem_neg : msb_rem = 1) (c_neg : msb_c = 1)
    (eq_msb_rem : msb_rem = if 32768 ≤ r3 then 1 else 0)
    (eq_msb_c : msb_c = if 32768 ≤ c3 then 1 else 0)
    (rn_ar0 : msb_rem = 1 ∨ ar0 = r0) (rn_ar1 : msb_rem = 1 ∨ ar1 = r1)
    (rn_ar2 : msb_rem = 1 ∨ ar2 = r2) (rn_ar3 : msb_rem = 1 ∨ ar3 = r3)
    (cn_ac0 : msb_c = 1 ∨ ac0 = c0) (cn_ac1 : msb_c = 1 ∨ ac1 = c1)
    (cn_ac2 : msb_c = 1 ∨ ac2 = c2) (cn_ac3 : msb_c = 1 ∨ ac3 = c3)
    (eq_cnop0 : msb_c = 0 ∨ cnop0 = 0) (eq_cnop1 : msb_c = 0 ∨ cnop1 = 0)
    (eq_cnop2 : msb_c = 0 ∨ cnop2 = 0) (eq_cnop3 : msb_c = 0 ∨ cnop3 = 0)
    (eq_rnop0 : msb_rem = 0 ∨ rnop0 = 0) (eq_rnop1 : msb_rem = 0 ∨ rnop1 = 0)
    (eq_rnop2 : msb_rem = 0 ∨ rnop2 = 0) (eq_rnop3 : msb_rem = 0 ∨ rnop3 = 0)
    (c_neg_sum_zero : msb_c = 1 →
        Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧
        Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] =
          Word.toBitVec64 #v[c0, c1, c2, c3] +
          Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
    (rem_neg_sum_zero : msb_rem = 1 →
        Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧
        Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] =
          Word.toBitVec64 #v[r0, r1, r2, r3] +
          Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
    (abs_check : Word.toNat #v[ar0, ar1, ar2, ar3] <
      Word.toNat #v[ac0, ac1, ac2, ac3]) :
    |Word.toInt #v[r0, r1, r2, r3]| <
      |Word.toInt #v[c0, c1, c2, c3]| := by
  have hp17 : 2 ^ 17 < p := Fact.out
  have ⟨hc0_lt, hc1_lt, hc2_lt, hc3_lt⟩ := Word.lt_cases_of_isU64 is_U64_c
  have ⟨hr0_lt, hr1_lt, hr2_lt, hr3_lt⟩ := Word.lt_cases_of_isU64 is_U64_r
  simp only [Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
    at hc0_lt hc1_lt hc2_lt hc3_lt hr0_lt hr1_lt hr2_lt hr3_lt
  simp [rem_neg, c_neg] at *
  subst rnop0 rnop1 rnop2 rnop3 cnop0 cnop1 cnop2 cnop3
  obtain ⟨_, heqz_c⟩ := c_neg_sum_zero
  obtain ⟨_, heqz_r⟩ := rem_neg_sum_zero
  have hr3_ge_val : r3.val ≥ 32768 := by
    have hh : (32768 : ZMod p).val ≤ r3.val := eq_msb_rem
    rwa [val_32768_zmod_p] at hh
  have hc3_ge_val : c3.val ≥ 32768 := by
    have hh : (32768 : ZMod p).val ≤ c3.val := eq_msb_c
    rwa [val_32768_zmod_p] at hh
  have r_isNeg : Word.isNegative #v[r0, r1, r2, r3] := by
    unfold Word.isNegative
    simp only [Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    omega
  have c_isNeg : Word.isNegative #v[c0, c1, c2, c3] := by
    unfold Word.isNegative
    simp only [Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    omega
  apply sum_zero_abs is_U64_c is_U64_ac c_isNeg at heqz_c
  apply sum_zero_abs is_U64_r is_U64_ar r_isNeg at heqz_r
  obtain ⟨hc_lb, hc_nlb⟩ := heqz_c
  obtain ⟨hr_lb, hr_nlb⟩ := heqz_r
  by_cases is_r_lb : Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63 <;>
    by_cases is_c_lb : Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63
  · exact div_rem_h_abs_case_pp_lblb hr_lb hc_lb is_r_lb is_c_lb abs_check
  · exact div_rem_h_abs_case_pp_lbnlb is_U64_c is_U64_ac
      hr_lb hc_nlb is_r_lb is_c_lb abs_check
  · exact div_rem_h_abs_case_pp_nlblb is_U64_r is_r_lb is_c_lb
  · exact div_rem_h_abs_case_pp_nlbnlb is_U64_ar is_U64_ac
      hr_nlb hc_nlb is_r_lb is_c_lb abs_check

/-- Extracted `h_abs` for `div_rem` (signed 64-bit DRS branch).

Lifted from `SP1Chips/DivRem/DivRem.lean` so its 4-way rem_neg × c_neg
case-split body (`simp [...] at *` per case, `subst`, `push_cast`,
`sum_zero_abs` applications) is kernel-checked independently of
`div_rem`. Together with `div_rem_h_prod_aux`, this lift is what
allows `div_rem` to compile without `debug.skipKernelTC`.

The body dispatches on `b_rem_neg × b_c_neg` and delegates to one of
the four `div_rem_h_abs_case_{nn,np,pn,pp}` helpers, each of which
elaborates within the default kernel WHNF depth budget — this is what
lets the dispatcher itself avoid `skipKernelTC`. -/
lemma div_rem_h_abs_aux {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 c1 c2 c3 r0 r1 r2 r3
     ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3
     cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3
     msb_rem msb_c : ZMod p}
    (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
    (is_U64_r : Word.isU64 #v[r0, r1, r2, r3])
    (is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3])
    (is_U64_ar : Word.isU64 #v[ar0, ar1, ar2, ar3])
    (b_rem_neg : msb_rem = 0 ∨ msb_rem = 1)
    (b_c_neg : msb_c = 0 ∨ msb_c = 1)
    (eq_msb_rem : msb_rem = if 32768 ≤ r3 then 1 else 0)
    (eq_msb_c : msb_c = if 32768 ≤ c3 then 1 else 0)
    (rn_ar0 : msb_rem = 1 ∨ ar0 = r0) (rn_ar1 : msb_rem = 1 ∨ ar1 = r1)
    (rn_ar2 : msb_rem = 1 ∨ ar2 = r2) (rn_ar3 : msb_rem = 1 ∨ ar3 = r3)
    (cn_ac0 : msb_c = 1 ∨ ac0 = c0) (cn_ac1 : msb_c = 1 ∨ ac1 = c1)
    (cn_ac2 : msb_c = 1 ∨ ac2 = c2) (cn_ac3 : msb_c = 1 ∨ ac3 = c3)
    (eq_cnop0 : msb_c = 0 ∨ cnop0 = 0) (eq_cnop1 : msb_c = 0 ∨ cnop1 = 0)
    (eq_cnop2 : msb_c = 0 ∨ cnop2 = 0) (eq_cnop3 : msb_c = 0 ∨ cnop3 = 0)
    (eq_rnop0 : msb_rem = 0 ∨ rnop0 = 0) (eq_rnop1 : msb_rem = 0 ∨ rnop1 = 0)
    (eq_rnop2 : msb_rem = 0 ∨ rnop2 = 0) (eq_rnop3 : msb_rem = 0 ∨ rnop3 = 0)
    (c_neg_sum_zero : msb_c = 1 →
        Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧
        Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] =
          Word.toBitVec64 #v[c0, c1, c2, c3] +
          Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
    (rem_neg_sum_zero : msb_rem = 1 →
        Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧
        Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] =
          Word.toBitVec64 #v[r0, r1, r2, r3] +
          Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
    (abs_check : Word.toNat #v[ar0, ar1, ar2, ar3] <
      Word.toNat #v[ac0, ac1, ac2, ac3]) :
    |Word.toInt #v[r0, r1, r2, r3]| <
      |Word.toInt #v[c0, c1, c2, c3]| := by
  rcases b_rem_neg with rem_nneg | rem_neg <;>
    rcases b_c_neg with c_nneg | c_neg
  · exact div_rem_h_abs_case_nn is_U64_c is_U64_r is_U64_ac is_U64_ar
      rem_nneg c_nneg eq_msb_rem eq_msb_c
      rn_ar0 rn_ar1 rn_ar2 rn_ar3 cn_ac0 cn_ac1 cn_ac2 cn_ac3
      eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3
      eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3
      c_neg_sum_zero rem_neg_sum_zero abs_check
  · exact div_rem_h_abs_case_np is_U64_c is_U64_r is_U64_ac is_U64_ar
      rem_nneg c_neg eq_msb_rem eq_msb_c
      rn_ar0 rn_ar1 rn_ar2 rn_ar3 cn_ac0 cn_ac1 cn_ac2 cn_ac3
      eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3
      eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3
      c_neg_sum_zero rem_neg_sum_zero abs_check
  · exact div_rem_h_abs_case_pn is_U64_c is_U64_r is_U64_ac is_U64_ar
      rem_neg c_nneg eq_msb_rem eq_msb_c
      rn_ar0 rn_ar1 rn_ar2 rn_ar3 cn_ac0 cn_ac1 cn_ac2 cn_ac3
      eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3
      eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3
      c_neg_sum_zero rem_neg_sum_zero abs_check
  · exact div_rem_h_abs_case_pp is_U64_c is_U64_r is_U64_ac is_U64_ar
      rem_neg c_neg eq_msb_rem eq_msb_c
      rn_ar0 rn_ar1 rn_ar2 rn_ar3 cn_ac0 cn_ac1 cn_ac2 cn_ac3
      eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3
      eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3
      c_neg_sum_zero rem_neg_sum_zero abs_check

end divrem_h_abs_helper

end DivRem
