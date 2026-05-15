import SP1Chips.ShiftRight.Common

namespace ShiftRight

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
-- Unused variables expected because many proofs are currently stopped.
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000

section sraw_poly

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 2000000000 in
-- 2B heartbeats: cb-blast for hl2=ll2=hl3=ll3=0 + msb_b case split + 2x32-leaf inner blasts.
set_option debug.skipKernelTC true in
-- Skip kernel typechecking: `Word.toBitVec64_poly_toNat_poly` involves `2^N`
-- re-checks (mirrors `spec.srlw_common_poly`'s use).
/-- Shared proof body for `spec.sraw_poly` and `spec.sraiw_poly`. Structure
mirrors `spec.srlw_common_poly` with an msb_b case split (since under SRAW,
`w_msb_b` doesn't force msb_b = 0; msb_b is determined by U16MSBOperation on b1). -/
private lemma spec.sraw_common_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly) (eq_sraw : Main[67] = 1) :
    Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
      execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[25], Main[26], Main[27], Main[28]] .SRAW := by
  -- Setup (mirrors spec.srlw_common_poly prologue).
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h_real := is_real_eq_one_of_sraw Main cstrs eq_sraw
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  have is_U32_b := Word.isU64_poly_low_poly_isU32_poly is_U64_b
  have is_U32_c := Word.isU64_poly_low_poly_isU32_poly is_U64_c
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨c0_16, _c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ] at b0_16 b1_16 b2_16 b3_16 c0_16
  obtain ⟨_, _, _, sop_4⟩ := single_op_poly Main cstrs
  have ⟨h_no_srl, h_no_sra, h_no_srlw⟩ := sop_4 eq_sraw
  -- Open the iff_poly.
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  -- Set up local names.
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
  -- Destructure cstrs (same shape as SRLW prologue).
  obtain ⟨_, h_msb_b1_sraw, h_msb_a1_srw, _, _,
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
  have h_v0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_v1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := by
    intro h; rw [h] at h_v1_val; rw [h_v0_val] at h_v1_val; exact zero_ne_one h_v1_val
  have h_zero_ne_one : (0 : ZMod p) ≠ 1 := fun h => h_one_ne_zero h.symm
  have h_sum_ne : ¬ Main[64] + Main[65] + Main[66] + Main[67] = 0 := by
    intro h
    rw [h_no_srl, h_no_sra, h_no_srlw, eq_sraw] at h
    simp only [add_zero, zero_add] at h
    exact h_one_ne_zero h
  have lt_ll0 := lt_ll0' h_sum_ne
  have lt_lh0 := lt_lh0' h_sum_ne
  have lt_ll1 := lt_ll1' h_sum_ne
  have lt_lh1 := lt_lh1' h_sum_ne
  have lt_ll2 := lt_ll2' h_sum_ne
  have lt_lh2 := lt_lh2' h_sum_ne
  have lt_ll3 := lt_ll3' h_sum_ne
  have lt_lh3 := lt_lh3' h_sum_ne
  -- Under SRAW: srl + sra = 0, so the LHS multiplier in h_b2_dec, h_b3_dec is 0,
  -- forcing hl2 = ll2 = hl3 = ll3 = 0 via cancel_mul_65536_zero_poly (after 16
  -- cb sub-cases to identify v0123). Same as the SRLW cb-blast.
  rw [h_no_srl, h_no_sra] at h_b2_dec h_b3_dec
  simp only [add_zero, zero_add, zero_mul, mul_zero] at h_b2_dec h_b3_dec
  symm at h_b2_dec h_b3_dec
  push_cast at h_b2_dec h_b3_dec
  have zero_aux : ∀ (M N : ℕ), M * N = 65536 → 0 < M →
      ∀ {hl ll : ZMod p}, v0123 = ((M : ℕ) : ZMod p) →
      hl.val < M → ll.val < N →
      hl * 65536 + ll * v0123 = 0 → hl = 0 ∧ ll = 0 := by
    intro M N h_MN h_M_pos hl ll h_v0123_eq h_hl_lt h_ll_lt h_eq
    have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
    have h_M_dvd : M ∣ 65536 := ⟨N, h_MN.symm⟩
    have h_M_le : M ≤ 65536 := Nat.le_of_dvd (by omega) h_M_dvd
    have h_N_le : N ≤ 65536 := by nlinarith [h_MN, h_M_pos]
    have h_M_lt_p : M < p := by omega
    have h_N_lt_p : N < p := by omega
    have h_v0123_val : v0123.val = M := by
      rw [h_v0123_eq]; exact ZMod.val_natCast_of_lt h_M_lt_p
    have h_v0123_dvd : v0123.val ∣ 65536 := by rw [h_v0123_val]; exact h_M_dvd
    have h_v0123_pos : 0 < v0123.val := by rw [h_v0123_val]; exact h_M_pos
    have h_cancel := cancel_mul_65536_zero_poly h_v0123_dvd h_v0123_pos h_eq
    rw [h_v0123_val] at h_cancel
    have h_quot_eq : 65536 / M = N := by
      rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
    rw [h_quot_eq] at h_cancel
    have h_hl_N_lt : hl.val * N < 65536 := by nlinarith [h_hl_lt, h_MN, h_M_pos, h_N_pos]
    have h_hl_N_lt_p : hl.val * N < p := by omega
    have h_hl_N_val : (hl * ((N : ℕ) : ZMod p)).val = hl.val * N := by
      rw [ZMod.val_mul_of_lt]
      · rw [ZMod.val_natCast_of_lt h_N_lt_p]
      · rw [ZMod.val_natCast_of_lt h_N_lt_p]; exact h_hl_N_lt_p
    have h_sum_lt_p : hl.val * N + ll.val < p := by omega
    have h_sum_val : (hl * ((N : ℕ) : ZMod p) + ll).val = hl.val * N + ll.val := by
      rw [ZMod.val_add_of_lt]
      · rw [h_hl_N_val]
      · rw [h_hl_N_val]; exact h_sum_lt_p
    have h_zero_val : (hl * ((N : ℕ) : ZMod p) + ll).val = 0 := by
      rw [h_cancel]; exact ZMod.val_zero
    rw [h_sum_val] at h_zero_val
    have h_hl_val_zero : hl.val = 0 := by
      have h_prod_zero : hl.val * N = 0 := by omega
      exact (Nat.mul_eq_zero.mp h_prod_zero).resolve_right (by omega)
    have h_ll_val_zero : ll.val = 0 := by omega
    exact ⟨(ZMod.val_eq_zero hl).mp h_hl_val_zero,
           (ZMod.val_eq_zero ll).mp h_ll_val_zero⟩
  have cb_aux : ∀ {hl ll : ZMod p}
      (_lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) +
                                    cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8) : ZMod p).val)
      (_lt_ll : ll.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) +
                              cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p).val)
      (_h_dec : hl * 65536 + ll * v0123 = 0)
      (S M N : ℕ) (_h_S_le : S ≤ 15)
      (_h_MN : M * N = 65536) (_h_M_pos : 0 < M)
      (_h_M_eq : (2 : ℕ) ^ (16 - S) = M) (_h_N_eq : (2 : ℕ) ^ S = N)
      (_h_v0123_eq : v0123 = ((M : ℕ) : ZMod p))
      (_h_cb_sum_eq : (cb0 + cb1 * ((2 : ℕ) : ZMod p) +
                       cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p) = ((S : ℕ) : ZMod p)),
      hl = 0 ∧ ll = 0 := by
    intro hl ll lt_hl lt_ll h_dec S M N h_S_le h_MN h_M_pos h_M_eq h_N_eq h_v0123_eq h_cb_sum_eq
    have h_S_lt_p : S < p := by omega
    have h_cb_sum_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) +
                        cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p).val = S := by
      rw [h_cb_sum_eq]; exact ZMod.val_natCast_of_lt h_S_lt_p
    have h_S_le_16 : S ≤ 16 := by omega
    have h_outer_val : ((16 : ZMod p) -
                       (cb0 + cb1 * ((2 : ℕ) : ZMod p) +
                        cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p)).val = 16 - S := by
      rw [h_cb_sum_eq]
      rw [show ((16 : ZMod p) - ((S : ℕ) : ZMod p)) = (((16 - S) : ℕ) : ZMod p) from by
        rw [Nat.cast_sub h_S_le_16]; push_cast; ring]
      exact ZMod.val_natCast_of_lt (by omega)
    rw [h_outer_val] at lt_hl
    rw [h_cb_sum_val] at lt_ll
    rw [h_M_eq] at lt_hl
    rw [h_N_eq] at lt_ll
    exact zero_aux M N h_MN h_M_pos h_v0123_eq lt_hl lt_ll h_dec
  have ⟨eq_hl2, eq_ll2⟩ : hl2 = 0 ∧ ll2 = 0 := by
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 0 65536 1 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 8 256 256 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 4 4096 16 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 12 16 4096 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 2 16384 4 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 10 64 1024 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 6 1024 64 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 14 4 16384 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 1 32768 2 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 9 128 512 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 5 2048 32 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 13 8 8192 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 3 8192 8 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 11 32 2048 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 7 512 128 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh2 lt_ll2 h_b2_dec 15 2 32768 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
  have ⟨eq_hl3, eq_ll3⟩ : hl3 = 0 ∧ ll3 = 0 := by
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 0 65536 1 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 8 256 256 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 4 4096 16 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 12 16 4096 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 2 16384 4 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 10 64 1024 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 6 1024 64 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 14 4 16384 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 1 32768 2 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 9 128 512 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 5 2048 32 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 13 8 8192 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 3 8192 8 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 11 32 2048 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 7 512 128 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · exact cb_aux lt_lh3 lt_ll3 h_b3_dec 15 2 32768 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
  -- Derive a2 = a3 = msb_srw * 65535 from srw_w2, srw_w3. Under SRAW: srlw+sraw = 1.
  rw [h_no_srlw, eq_sraw] at srw_w2 srw_w3
  simp only [zero_add, mul_one] at srw_w2 srw_w3
  simp only [show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
    at srw_w2 srw_w3
  have h_a2_eq : a2 = msb_srw * 65535 := srw_w2
  have h_a3_eq : a3 = msb_srw * 65535 := srw_w3
  -- Relate msb_srw to MSB of a1 via U16MSBOperation.spec_poly. Multiplier srlw+sraw = 1.
  rw [h_no_srlw, eq_sraw] at h_msb_a1_srw
  simp only [zero_add] at h_msb_a1_srw
  have h_msb_srw_bool : msb_srw = 0 ∨ msb_srw = 1 := by
    rw [U16MSBOperation.allHold_constraints_iff_poly] at h_msb_a1_srw
    exact h_msb_a1_srw.2.1
  -- a1.val < 65536 will be derived inside each (msb_b, cb4) outer leaf from the
  -- concrete a1 form (lr1 + correction, or msb_b * 65535).
  have h_a2_lt : a2.val < 65536 := by
    rw [h_a2_eq]
    have h_eq : msb_srw * (65535 : ZMod p) = msb_srw * (((65535 : ℕ) : ZMod p)) := by norm_cast
    rw [h_eq]; exact bool_mul_65535_lt_poly h_msb_srw_bool
  have h_a3_lt : a3.val < 65536 := by
    rw [h_a3_eq]
    have h_eq : msb_srw * (65535 : ZMod p) = msb_srw * (((65535 : ℕ) : ZMod p)) := by norm_cast
    rw [h_eq]; exact bool_mul_65535_lt_poly h_msb_srw_bool
  -- Derive msb_b case split via h_msb_b1_sraw (U16MSBOperation on b1, multiplier Main[67] = 1).
  rw [eq_sraw] at h_msb_b1_sraw
  have h_msb_b_eq : msb_b = if b1.val ≥ 32768 then 1 else 0 := by
    rw [show msb_b = ({ msb := msb_b } : U16MSBOperation (ZMod p)).msb from rfl]
    apply U16MSBOperation.spec_poly b1_16 h_msb_b1_sraw
  -- Resolve h_su16k under SRAW: srl + sra = 0, so cb5 * 2 * (srl + sra) = 0.
  rw [h_no_srl, h_no_sra] at h_su160 h_su161 h_su162 h_su163 one_of_su16s
  simp only [add_zero, zero_add, zero_mul, mul_zero] at h_su160 h_su161 h_su162 h_su163 one_of_su16s
  rw [h_no_srlw, eq_sraw] at one_of_su16s
  simp only [zero_add,
             show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
    at one_of_su16s
  -- h_su160 : su160 = 0 ∨ cb4 = 0
  -- h_su161 : su161 = 0 ∨ cb4 = 1
  -- h_su162 : su162 = 0 ∨ cb4 = 2  -- impossible (cb4 ∈ {0,1}) → su162 = 0
  -- h_su163 : su163 = 0 ∨ cb4 = 3  -- impossible → su163 = 0
  -- one_of_su16s : su160 + su161 + su162 + su163 = 1
  have h_su162_zero : su162 = 0 := by
    apply h_su162.resolve_right
    intro h
    rcases b_cb4 with hcb4 | hcb4
    · rw [hcb4] at h; exact val_2_ne_zero h.symm
    · rw [hcb4] at h
      have hv1 : (1 : ZMod p).val = 1 := h_v1_val
      have hv2 : (2 : ZMod p).val = 2 := val_2_zmod_p
      have hval := congrArg ZMod.val h
      rw [hv1, hv2] at hval; omega
  have h_su163_zero : su163 = 0 := by
    apply h_su163.resolve_right
    intro h
    rcases b_cb4 with hcb4 | hcb4
    · rw [hcb4] at h; exact val_3_ne_zero h.symm
    · rw [hcb4] at h
      have hv1 : (1 : ZMod p).val = 1 := h_v1_val
      have hv3 : (3 : ZMod p).val = 3 := by
        rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
        exact ZMod.val_natCast_of_lt (by omega)
      have hval := congrArg ZMod.val h
      rw [hv1, hv3] at hval; omega
  -- one_of_su16s simplifies: su160 + su161 = 1.
  rw [h_su162_zero, h_su163_zero, add_zero, add_zero] at one_of_su16s
  -- Activate srw_** under SRAW: srlw + sraw = 1.
  rw [h_no_srlw, eq_sraw] at srw_00 srw_01 srw_10 srw_11
  simp only [zero_add,
             show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
    at srw_00 srw_01 srw_10 srw_11
  -- srw_00 : su160 = 0 ∨ a0 = lr0
  -- srw_01 : su160 = 0 ∨ a1 = lr1 + (msb_b * 65536 - smv)
  -- srw_10 : su161 = 0 ∨ a0 = lr1 + (msb_b * 65536 - smv)
  -- srw_11 : su161 = 0 ∨ a1 = msb_b * 65535
  -- Bridge ll2 = 0 and ll3 = 0 to simplify lr1 = hl1, lr2 = 0, lr3 = 0 (already from cb-blast).
  -- lr0 = hl0 + ll1 * v0123 (unchanged).
  -- Lift shared cb-sum derivations BEFORE the cb4 case-split (which consumes b_cb4).
  have h_cb_sum_lt_64 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val < 64 := by
    have hb0 : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb1' : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb2 : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb3 : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb4 : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb5 : cb5.val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have h_eq := cb_sum_val_eq_poly b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
    omega
  have h_val_10 : (10 : ZMod p).val = 10 := by
    rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have h_diff := diff h_sum_ne
  rw [h_val_10] at h_diff
  have h_c0_mod_64 : c0.val % 64 = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val := by
    apply is_mod_64_poly (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)
    · exact h_cb_sum_lt_64
    · exact c0_16
    · exact h_diff
  have h_cb_sum_eq := cb_sum_val_eq_poly b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
  have hb0_le : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
  have hb1_le : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
  have hb2_le : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
  have hb3_le : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
  have hb4_le : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
  have v_2 : (2 : ZMod p).val = 2 := val_2_zmod_p
  have v_4 : (4 : ZMod p).val = 4 := val_4_zmod_p
  have v_8 : (8 : ZMod p).val = 8 := val_8_zmod_p
  have v_16 : (16 : ZMod p).val = 16 := val_16_zmod_p
  have m1 : (cb1 * 2 : ZMod p).val = cb1.val * 2 := by
    rw [ZMod.val_mul_of_lt]
    · rw [v_2]
    · rw [v_2]; omega
  have m2 : (cb2 * 4 : ZMod p).val = cb2.val * 4 := by
    rw [ZMod.val_mul_of_lt]
    · rw [v_4]
    · rw [v_4]; omega
  have m3 : (cb3 * 8 : ZMod p).val = cb3.val * 8 := by
    rw [ZMod.val_mul_of_lt]
    · rw [v_8]
    · rw [v_8]; omega
  have m4 : (cb4 * 16 : ZMod p).val = cb4.val * 16 := by
    rw [ZMod.val_mul_of_lt]
    · rw [v_16]
    · rw [v_16]; omega
  have a1_val' : (cb0 + cb1 * 2 : ZMod p).val = cb0.val + cb1.val * 2 := by
    rw [ZMod.val_add_of_lt]
    · rw [m1]
    · rw [m1]; omega
  have a2_val' : (cb0 + cb1 * 2 + cb2 * 4 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 := by
    rw [ZMod.val_add_of_lt]
    · rw [a1_val', m2]
    · rw [a1_val', m2]; omega
  have a3_val' : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 := by
    rw [ZMod.val_add_of_lt]
    · rw [a2_val', m3]
    · rw [a2_val', m3]; omega
  have h_cb_sum_5_val : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
    rw [ZMod.val_add_of_lt]
    · rw [a3_val', m4]
    · rw [a3_val', m4]; omega
  have h_c0_mod_32 : c0.val % 32 =
      (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 : ZMod p).val := by
    have h_dvd : c0.val % 32 = c0.val % 64 % 32 := by
      rw [Nat.mod_mod_of_dvd]; exact ⟨2, rfl⟩
    rw [h_dvd, h_c0_mod_64, h_cb_sum_eq, h_cb_sum_5_val]; omega
  -- Outer case split on msb_b via h_msb_b_eq.
  by_cases hb1 : b1.val ≥ 32768
  · -- msb_b = 1 case (Stage D).
    have h_msb_b_one : msb_b = 1 := by rw [h_msb_b_eq, if_pos hb1]
    rw [h_msb_b_one, one_mul] at eq_smv
    -- Substitute msb_b = 1, smv = v0123 into srw_** disjuncts.
    simp only [h_msb_b_one, eq_smv, one_mul] at srw_01 srw_10 srw_11
    -- srw_00 : su160 = 0 ∨ a0 = lr0
    -- srw_01 : su160 = 0 ∨ a1 = lr1 + (65536 - v0123)
    -- srw_10 : su161 = 0 ∨ a0 = lr1 + (65536 - v0123)
    -- srw_11 : su161 = 0 ∨ a1 = 65535
    have h_isU32_b_lo : (Word.low_poly #v[b0, b1, b2, b3]).isU32_poly :=
      Word.isU64_poly_low_poly_isU32_poly is_U64_b
    have h_isU32_c_lo : (Word.low_poly #v[c0, c1, c2, c3]).isU32_poly :=
      Word.isU64_poly_low_poly_isU32_poly is_U64_c
    -- low_b32.msb = true (from b1.val ≥ 32768).
    have h_b_lo_msb_true : ((Word.low_poly #v[b0, b1, b2, b3]).toBitVec32_poly).msb = true := by
      rw [BitVec.msb_eq_decide, HWord.toBitVec32_poly_toNat_poly h_isU32_b_lo]
      simp [Word.low_poly, HWord.toNat_poly]
      omega
    -- Reusable bound helpers.
    have lr_blast : ∀ {hl ll : ZMod p}
        (_lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                      + cb3 * 8) : ZMod p).val)
        (_lt_ll : ll.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8 : ZMod p).val),
        (hl + ll * v0123).val < 65536 := by
      intro hl ll lt_hl lt_ll
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact lr_blast_per_pattern_poly 0 65536 1 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 8 256 256 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 4 4096 16 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 12 16 4096 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 2 16384 4 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 10 64 1024 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 6 1024 64 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 14 4 16384 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 1 32768 2 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 9 128 512 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 5 2048 32 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 13 8 8192 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 3 8192 8 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 11 32 2048 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 7 512 128 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 15 2 32768 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
    -- correction_blast: (hl + (65536 - v0123)).val < 65536 when hl.val < 2^(16-cb_sum).
    have correction_blast : ∀ {hl : ZMod p}
        (_lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                      + cb3 * 8) : ZMod p).val),
        (hl + (((65536 : ℕ) : ZMod p) - v0123)).val < 65536 := by
      intro hl lt_hl
      have per_pattern : ∀ (S M N : ℕ) (_h_S_le : S ≤ 15) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
          (h_M_eq : (2 : ℕ) ^ (16 - S) = M)
          (h_v0123_eq : v0123 = ((M : ℕ) : ZMod p))
          (h_cb_sum_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                        = ((S : ℕ) : ZMod p))
          (lt_hl' : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                        + cb3 * 8) : ZMod p).val),
          (hl + (((65536 : ℕ) : ZMod p) - v0123)).val < 65536 := by
        intro S M N _h_S_le h_MN h_M_pos h_M_eq h_v0123_eq h_cb_sum_eq lt_hl'
        have h_M_le : M ≤ 65536 := by
          rw [show (65536 : ℕ) = 2 ^ 16 from by decide, ← h_M_eq]
          exact Nat.pow_le_pow_right (by omega) (by omega)
        have h_M_lt_p : M < p := by omega
        have h_v_val : v0123.val = M := by
          rw [h_v0123_eq]; exact ZMod.val_natCast_of_lt h_M_lt_p
        have h_65536_val : ((65536 : ℕ) : ZMod p).val = 65536 := ZMod.val_natCast_of_lt (by omega)
        have h_sub_val : (((65536 : ℕ) : ZMod p) - v0123).val = 65536 - M := by
          rw [ZMod.val_sub]
          · rw [h_v_val, h_65536_val]
          · rw [h_v_val, h_65536_val]; exact h_M_le
        have h_outer_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                    + cb3 * 8) : ZMod p).val = 16 - S := by
          rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                    + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
            rw [h_cb_sum_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
          exact ZMod.val_natCast_of_lt (by omega)
        have lt_hl_M : hl.val < M := by rw [h_outer_val] at lt_hl'; rw [← h_M_eq]; exact lt_hl'
        rw [ZMod.val_add_of_lt]
        · rw [h_sub_val]; omega
        · rw [h_sub_val]; omega
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact per_pattern 0 65536 1 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 8 256 256 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 4 4096 16 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 12 16 4096 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 2 16384 4 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 10 64 1024 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 6 1024 64 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 14 4 16384 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 1 32768 2 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 9 128 512 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 5 2048 32 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 13 8 8192 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 3 8192 8 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 11 32 2048 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 7 512 128 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
      · exact per_pattern 15 2 32768 (by omega) (by decide) (by omega) rfl
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring) lt_hl
    -- cb4 case-split.
    rcases b_cb4 with hcb4 | hcb4
    · -- cb4 = 0 → su160 = 1. a0 = lr0 = hl0+ll1*v0123, a1 = lr1+(65536-v0123) = hl1+(65536-v0123).
      have h_su161_zero : su161 = 0 := by
        apply h_su161.resolve_right
        intro h; rw [hcb4] at h; exact h_zero_ne_one h
      have h_su160_eq : su160 = 1 := by
        have := one_of_su16s
        rw [h_su161_zero, add_zero] at this; exact this
      have h_su160_ne_zero : su160 ≠ 0 := by rw [h_su160_eq]; exact h_one_ne_zero
      have h_a0_eq : a0 = lr0 := srw_00.resolve_left h_su160_ne_zero
      have h_a1_eq : a1 = lr1 + (((65536 : ℕ) : ZMod p) - v0123) := by
        have := srw_01.resolve_left h_su160_ne_zero
        convert this using 2
      have h_a0_lt : a0.val < 65536 := by rw [h_a0_eq, eq_lr0]; exact lr_blast lt_lh0 lt_ll1
      have h_a1_lt : a1.val < 65536 := by
        rw [h_a1_eq, eq_lr1, eq_ll2, zero_mul, add_zero]
        exact correction_blast lt_lh1
      have h_isU32_a_lo : HWord.isU32_poly #v[a0, a1] := by
        intro i; fin_cases i <;> simp [HWord.isU32_poly]
        · exact h_a0_lt
        · exact h_a1_lt
      have h_msb_srw_eq : msb_srw = if a1.val ≥ 32768 then 1 else 0 := by
        rw [show msb_srw = ({ msb := msb_srw } : U16MSBOperation (ZMod p)).msb from rfl]
        apply U16MSBOperation.spec_poly h_a1_lt h_msb_a1_srw
      have h_a01_msb_eq : (HWord.toBitVec32_poly #v[a0, a1]).msb = decide (a1.val ≥ 32768) := by
        have h_toNat : (HWord.toBitVec32_poly #v[a0, a1]).toNat = a0.val + a1.val * 2 ^ 16 := by
          rw [HWord.toBitVec32_poly_toNat_poly h_isU32_a_lo]; simp [HWord.toNat_poly]
        rw [BitVec.msb_eq_decide, h_toNat]
        have h_iff : (2 ^ (32 - 1) ≤ a0.val + a1.val * 2 ^ 16) ↔ (a1.val ≥ 32768) := by
          constructor <;> (intro h; omega)
        exact decide_eq_decide.mpr h_iff
      have h_a2_msb : a2 = if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then ((65535 : ℕ) : ZMod p) else 0 := by
        rw [h_a2_eq, h_msb_srw_eq]
        by_cases h : a1.val ≥ 32768
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = true := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = false := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
      have h_a3_msb : a3 = if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then ((65535 : ℕ) : ZMod p) else 0 := by
        rw [h_a3_eq, h_msb_srw_eq]
        by_cases h : a1.val ≥ 32768
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = true := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = false := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
      have h_signext_bridge : Word.toBitVec64_poly #v[a0, a1, a2, a3] =
          BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1]) := by
        rw [h_a2_msb, h_a3_msb]
        have := HWord.sign_extend_32_to_64_msb_poly h_isU32_a_lo
        have h_a0_idx : (#v[a0, a1] : HWord (ZMod p))[0] = a0 := rfl
        have h_a1_idx : (#v[a0, a1] : HWord (ZMod p))[1] = a1 := rfl
        rw [h_a0_idx, h_a1_idx] at this
        exact this.symm
      rw [h_signext_bridge]
      simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly]
      change BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1])
           = BitVec.signExtend 64 ((Word.low_poly #v[b0, b1, b2, b3]).toBitVec32_poly.sshiftRight
              ((BitVec.setWidth 5 (Word.low_poly #v[c0, c1, c2, c3]).toBitVec32_poly).toNat))
      congr 1
      -- Bridge sshiftRight via msb=true.
      rw [← BitVec.toNat_inj]
      rw [BitVec.toNat_sshiftRight_of_msb_true h_b_lo_msb_true]
      simp only [BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
      have h_shift_eq : (Word.low_poly #v[c0, c1, c2, c3]).toBitVec32_poly.toNat % 2 ^ 5
                      = c0.val % 32 := by
        rw [HWord.toBitVec32_poly_toNat_poly h_isU32_c_lo]
        simp [Word.low_poly, HWord.toNat_poly]; omega
      rw [h_shift_eq]; clear h_shift_eq
      simp only [Word.low_poly, Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      rw [h_a0_eq, h_a1_eq, eq_lr0, eq_lr1, eq_ll2, zero_mul, add_zero]
      rw [h_c0_mod_32]
      -- 16-way cb-blast using sraw_close_su16_0_case_msb1.
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact sraw_close_su16_0_case_msb1 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 9 (by omega) 128 512 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 7 (by omega) 512 128 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_0_case_msb1 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- cb4 = 1 → su161 = 1. a0 = lr1+(65536-v0123) = hl1+(65536-v0123), a1 = 65535.
      have h_su160_zero : su160 = 0 := by
        apply h_su160.resolve_right
        intro h; rw [hcb4] at h; exact h_one_ne_zero h
      have h_su161_eq : su161 = 1 := by
        have := one_of_su16s
        rw [h_su160_zero, zero_add] at this; exact this
      have h_su161_ne_zero : su161 ≠ 0 := by rw [h_su161_eq]; exact h_one_ne_zero
      have h_a0_eq : a0 = lr1 + (((65536 : ℕ) : ZMod p) - v0123) := by
        have := srw_10.resolve_left h_su161_ne_zero
        convert this using 2
      have h_a1_eq : a1 = ((65535 : ℕ) : ZMod p) := by
        have := srw_11.resolve_left h_su161_ne_zero
        convert this using 1
      have h_a0_lt : a0.val < 65536 := by
        rw [h_a0_eq, eq_lr1, eq_ll2, zero_mul, add_zero]
        exact correction_blast lt_lh1
      have h_a1_lt : a1.val < 65536 := by
        rw [h_a1_eq, show ((65535 : ℕ) : ZMod p).val = 65535 from
          ZMod.val_natCast_of_lt (by omega)]
        omega
      have h_isU32_a_lo : HWord.isU32_poly #v[a0, a1] := by
        intro i; fin_cases i <;> simp [HWord.isU32_poly]
        · exact h_a0_lt
        · exact h_a1_lt
      have h_msb_srw_eq : msb_srw = if a1.val ≥ 32768 then 1 else 0 := by
        rw [show msb_srw = ({ msb := msb_srw } : U16MSBOperation (ZMod p)).msb from rfl]
        apply U16MSBOperation.spec_poly h_a1_lt h_msb_a1_srw
      have h_a01_msb_eq : (HWord.toBitVec32_poly #v[a0, a1]).msb = decide (a1.val ≥ 32768) := by
        have h_toNat : (HWord.toBitVec32_poly #v[a0, a1]).toNat = a0.val + a1.val * 2 ^ 16 := by
          rw [HWord.toBitVec32_poly_toNat_poly h_isU32_a_lo]; simp [HWord.toNat_poly]
        rw [BitVec.msb_eq_decide, h_toNat]
        have h_iff : (2 ^ (32 - 1) ≤ a0.val + a1.val * 2 ^ 16) ↔ (a1.val ≥ 32768) := by
          constructor <;> (intro h; omega)
        exact decide_eq_decide.mpr h_iff
      have h_a2_msb : a2 = if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then ((65535 : ℕ) : ZMod p) else 0 := by
        rw [h_a2_eq, h_msb_srw_eq]
        by_cases h : a1.val ≥ 32768
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = true := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = false := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
      have h_a3_msb : a3 = if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then ((65535 : ℕ) : ZMod p) else 0 := by
        rw [h_a3_eq, h_msb_srw_eq]
        by_cases h : a1.val ≥ 32768
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = true := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = false := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
      have h_signext_bridge : Word.toBitVec64_poly #v[a0, a1, a2, a3] =
          BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1]) := by
        rw [h_a2_msb, h_a3_msb]
        have := HWord.sign_extend_32_to_64_msb_poly h_isU32_a_lo
        have h_a0_idx : (#v[a0, a1] : HWord (ZMod p))[0] = a0 := rfl
        have h_a1_idx : (#v[a0, a1] : HWord (ZMod p))[1] = a1 := rfl
        rw [h_a0_idx, h_a1_idx] at this
        exact this.symm
      rw [h_signext_bridge]
      simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly]
      change BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1])
           = BitVec.signExtend 64 ((Word.low_poly #v[b0, b1, b2, b3]).toBitVec32_poly.sshiftRight
              ((BitVec.setWidth 5 (Word.low_poly #v[c0, c1, c2, c3]).toBitVec32_poly).toNat))
      congr 1
      rw [← BitVec.toNat_inj]
      rw [BitVec.toNat_sshiftRight_of_msb_true h_b_lo_msb_true]
      simp only [BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
      have h_shift_eq : (Word.low_poly #v[c0, c1, c2, c3]).toBitVec32_poly.toNat % 2 ^ 5
                      = c0.val % 32 := by
        rw [HWord.toBitVec32_poly_toNat_poly h_isU32_c_lo]
        simp [Word.low_poly, HWord.toNat_poly]; omega
      rw [h_shift_eq]; clear h_shift_eq
      simp only [Word.low_poly, Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      rw [h_a0_eq, h_a1_eq, eq_lr1, eq_ll2, zero_mul, add_zero]
      rw [h_c0_mod_32]
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact sraw_close_su16_1_case_msb1 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 9 (by omega) 128 512 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 7 (by omega) 512 128 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact sraw_close_su16_1_case_msb1 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  · -- msb_b = 0 case (Stage C).
    have h_msb_b_zero : msb_b = 0 := by rw [h_msb_b_eq, if_neg hb1]
    push Not at hb1
    rw [h_msb_b_zero, zero_mul] at eq_smv
    simp only [h_msb_b_zero, eq_smv, zero_mul, mul_zero, add_zero, sub_self, sub_zero]
      at srw_01 srw_10 srw_11
    -- srw_00 : su160 = 0 ∨ a0 = lr0
    -- srw_01 : su160 = 0 ∨ a1 = lr1
    -- srw_10 : su161 = 0 ∨ a0 = lr1
    -- srw_11 : su161 = 0 ∨ a1 = 0
    have h_isU32_b_lo : (Word.low_poly #v[b0, b1, b2, b3]).isU32_poly :=
      Word.isU64_poly_low_poly_isU32_poly is_U64_b
    have h_isU32_c_lo : (Word.low_poly #v[c0, c1, c2, c3]).isU32_poly :=
      Word.isU64_poly_low_poly_isU32_poly is_U64_c
    -- low_b32.msb = false (from b1.val < 32768).
    have h_b_lo_msb_false : ((Word.low_poly #v[b0, b1, b2, b3]).toBitVec32_poly).msb = false := by
      rw [BitVec.msb_eq_decide, HWord.toBitVec32_poly_toNat_poly h_isU32_b_lo]
      simp [Word.low_poly, HWord.toNat_poly]
      omega
    -- Reusable bound helper: `(hl + ll * v0123).val < 65536` via 16-way cb-blast.
    have lr_blast : ∀ {hl ll : ZMod p}
        (_lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                      + cb3 * 8) : ZMod p).val)
        (_lt_ll : ll.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8 : ZMod p).val),
        (hl + ll * v0123).val < 65536 := by
      intro hl ll lt_hl lt_ll
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact lr_blast_per_pattern_poly 0 65536 1 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 8 256 256 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 4 4096 16 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 12 16 4096 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 2 16384 4 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 10 64 1024 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 6 1024 64 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 14 4 16384 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 1 32768 2 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 9 128 512 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 5 2048 32 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 13 8 8192 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 3 8192 8 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 11 32 2048 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 7 512 128 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
      · exact lr_blast_per_pattern_poly 15 2 32768 (by omega) (by decide) (by omega) rfl rfl
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          lt_hl lt_ll
    -- cb4 case-split.
    rcases b_cb4 with hcb4 | hcb4
    · -- cb4 = 0 → su160 = 1, su161 = 0. a0 = lr0, a1 = lr1.
      have h_su161_zero : su161 = 0 := by
        apply h_su161.resolve_right
        intro h; rw [hcb4] at h; exact h_zero_ne_one h
      have h_su160_eq : su160 = 1 := by
        have := one_of_su16s
        rw [h_su161_zero, add_zero] at this; exact this
      have h_su160_ne_zero : su160 ≠ 0 := by rw [h_su160_eq]; exact h_one_ne_zero
      have h_a0_eq : a0 = lr0 := srw_00.resolve_left h_su160_ne_zero
      have h_a1_eq : a1 = lr1 := srw_01.resolve_left h_su160_ne_zero
      -- Bounds via lr_blast.
      have h_a0_lt : a0.val < 65536 := by rw [h_a0_eq, eq_lr0]; exact lr_blast lt_lh0 lt_ll1
      have h_a1_lt : a1.val < 65536 := by
        rw [h_a1_eq, eq_lr1]
        have := lr_blast (hl := hl1) (ll := ll2) lt_lh1 lt_ll2
        exact this
      -- Signext bridge.
      have h_isU32_a_lo : HWord.isU32_poly #v[a0, a1] := by
        intro i; fin_cases i <;> simp [HWord.isU32_poly]
        · exact h_a0_lt
        · exact h_a1_lt
      -- Compute msb_srw via U16MSBOperation.spec_poly on h_msb_a1_srw (now a1_16 = h_a1_lt).
      have h_msb_srw_eq : msb_srw = if a1.val ≥ 32768 then 1 else 0 := by
        rw [show msb_srw = ({ msb := msb_srw } : U16MSBOperation (ZMod p)).msb from rfl]
        apply U16MSBOperation.spec_poly h_a1_lt h_msb_a1_srw
      have h_a01_msb_eq : (HWord.toBitVec32_poly #v[a0, a1]).msb = decide (a1.val ≥ 32768) := by
        have h_toNat : (HWord.toBitVec32_poly #v[a0, a1]).toNat = a0.val + a1.val * 2 ^ 16 := by
          rw [HWord.toBitVec32_poly_toNat_poly h_isU32_a_lo]; simp [HWord.toNat_poly]
        rw [BitVec.msb_eq_decide, h_toNat]
        have h_iff : (2 ^ (32 - 1) ≤ a0.val + a1.val * 2 ^ 16) ↔ (a1.val ≥ 32768) := by
          constructor <;> (intro h; omega)
        exact decide_eq_decide.mpr h_iff
      have h_a2_msb : a2 = if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then ((65535 : ℕ) : ZMod p) else 0 := by
        rw [h_a2_eq, h_msb_srw_eq]
        by_cases h : a1.val ≥ 32768
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = true := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = false := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
      have h_a3_msb : a3 = if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then ((65535 : ℕ) : ZMod p) else 0 := by
        rw [h_a3_eq, h_msb_srw_eq]
        by_cases h : a1.val ≥ 32768
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = true := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = false := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
      have h_signext_bridge : Word.toBitVec64_poly #v[a0, a1, a2, a3] =
          BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1]) := by
        rw [h_a2_msb, h_a3_msb]
        have := HWord.sign_extend_32_to_64_msb_poly h_isU32_a_lo
        have h_a0_idx : (#v[a0, a1] : HWord (ZMod p))[0] = a0 := rfl
        have h_a1_idx : (#v[a0, a1] : HWord (ZMod p))[1] = a1 := rfl
        rw [h_a0_idx, h_a1_idx] at this
        exact this.symm
      rw [h_signext_bridge]
      -- Unfold execute_RTYPEW_pure_w_poly for SRAW: sign_extend (m:=64) of sshiftRight.
      simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly]
      change BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1])
           = BitVec.signExtend 64 ((Word.low_poly #v[b0, b1, b2, b3]).toBitVec32_poly.sshiftRight
              ((BitVec.setWidth 5 (Word.low_poly #v[c0, c1, c2, c3]).toBitVec32_poly).toNat))
      congr 1
      -- Reduce sshiftRight to >>> via msb=false.
      rw [BitVec.sshiftRight_eq_of_msb_false h_b_lo_msb_false]
      rw [← BitVec.toNat_inj]
      simp only [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
                 Nat.shiftRight_eq_div_pow]
      have h_shift_eq : (Word.low_poly #v[c0, c1, c2, c3]).toBitVec32_poly.toNat % 2 ^ 5
                      = c0.val % 32 := by
        rw [HWord.toBitVec32_poly_toNat_poly h_isU32_c_lo]
        simp [Word.low_poly, HWord.toNat_poly]; omega
      rw [h_shift_eq]; clear h_shift_eq
      simp only [Word.low_poly, Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      -- Substitute a0 = lr0 = hl0+ll1*v0123, a1 = lr1 = hl1+ll2*v0123 = hl1.
      rw [h_a0_eq, h_a1_eq, eq_lr0, eq_lr1, eq_ll2, zero_mul, add_zero]
      -- c0.val % 32 bridge.
      rw [h_c0_mod_32]
      -- cb4 = 0 → su160 = 1: use srlw_close_su16_0_case with appropriate cb5 setting.
      -- 16-way cb-blast on cb0..cb3.
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact srlw_close_su16_0_case 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 9 (by omega) 128 512 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 7 (by omega) 512 128 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_0_case 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- cb4 = 1 → su161 = 1, su160 = 0. a0 = lr1 = hl1, a1 = 0.
      have h_su160_zero : su160 = 0 := by
        apply h_su160.resolve_right
        intro h; rw [hcb4] at h; exact h_one_ne_zero h
      have h_su161_eq : su161 = 1 := by
        have := one_of_su16s
        rw [h_su160_zero, zero_add] at this; exact this
      have h_su161_ne_zero : su161 ≠ 0 := by rw [h_su161_eq]; exact h_one_ne_zero
      have h_a0_eq : a0 = lr1 := srw_10.resolve_left h_su161_ne_zero
      have h_a1_eq : a1 = 0 := srw_11.resolve_left h_su161_ne_zero
      have h_a0_lt : a0.val < 65536 := by
        rw [h_a0_eq, eq_lr1]
        exact lr_blast (hl := hl1) (ll := ll2) lt_lh1 lt_ll2
      have h_a1_lt : a1.val < 65536 := by rw [h_a1_eq]; simp [h_v0_val]
      have h_isU32_a_lo : HWord.isU32_poly #v[a0, a1] := by
        intro i; fin_cases i <;> simp [HWord.isU32_poly]
        · exact h_a0_lt
        · exact h_a1_lt
      have h_msb_srw_eq : msb_srw = if a1.val ≥ 32768 then 1 else 0 := by
        rw [show msb_srw = ({ msb := msb_srw } : U16MSBOperation (ZMod p)).msb from rfl]
        apply U16MSBOperation.spec_poly h_a1_lt h_msb_a1_srw
      have h_a01_msb_eq : (HWord.toBitVec32_poly #v[a0, a1]).msb = decide (a1.val ≥ 32768) := by
        have h_toNat : (HWord.toBitVec32_poly #v[a0, a1]).toNat = a0.val + a1.val * 2 ^ 16 := by
          rw [HWord.toBitVec32_poly_toNat_poly h_isU32_a_lo]; simp [HWord.toNat_poly]
        rw [BitVec.msb_eq_decide, h_toNat]
        have h_iff : (2 ^ (32 - 1) ≤ a0.val + a1.val * 2 ^ 16) ↔ (a1.val ≥ 32768) := by
          constructor <;> (intro h; omega)
        exact decide_eq_decide.mpr h_iff
      have h_a2_msb : a2 = if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then ((65535 : ℕ) : ZMod p) else 0 := by
        rw [h_a2_eq, h_msb_srw_eq]
        by_cases h : a1.val ≥ 32768
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = true := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = false := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
      have h_a3_msb : a3 = if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then ((65535 : ℕ) : ZMod p) else 0 := by
        rw [h_a3_eq, h_msb_srw_eq]
        by_cases h : a1.val ≥ 32768
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = true := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
        · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = false := by rw [h_a01_msb_eq]; simp [h]
          simp [h, h_msb]
      have h_signext_bridge : Word.toBitVec64_poly #v[a0, a1, a2, a3] =
          BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1]) := by
        rw [h_a2_msb, h_a3_msb]
        have := HWord.sign_extend_32_to_64_msb_poly h_isU32_a_lo
        have h_a0_idx : (#v[a0, a1] : HWord (ZMod p))[0] = a0 := rfl
        have h_a1_idx : (#v[a0, a1] : HWord (ZMod p))[1] = a1 := rfl
        rw [h_a0_idx, h_a1_idx] at this
        exact this.symm
      rw [h_signext_bridge]
      simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly]
      change BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1])
           = BitVec.signExtend 64 ((Word.low_poly #v[b0, b1, b2, b3]).toBitVec32_poly.sshiftRight
              ((BitVec.setWidth 5 (Word.low_poly #v[c0, c1, c2, c3]).toBitVec32_poly).toNat))
      congr 1
      rw [BitVec.sshiftRight_eq_of_msb_false h_b_lo_msb_false]
      rw [← BitVec.toNat_inj]
      simp only [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
                 Nat.shiftRight_eq_div_pow]
      have h_shift_eq : (Word.low_poly #v[c0, c1, c2, c3]).toBitVec32_poly.toNat % 2 ^ 5
                      = c0.val % 32 := by
        rw [HWord.toBitVec32_poly_toNat_poly h_isU32_c_lo]
        simp [Word.low_poly, HWord.toNat_poly]; omega
      rw [h_shift_eq]; clear h_shift_eq
      simp only [Word.low_poly, Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      rw [h_a0_eq, h_a1_eq, eq_lr1, eq_ll2, zero_mul, add_zero]
      rw [h_c0_mod_32]
      -- cb4 = 1 → su161 = 1: use srlw_close_su16_1_case.
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact srlw_close_su16_1_case 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 9 (by omega) 128 512 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 7 (by omega) 512 128 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · exact srlw_close_su16_1_case 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl
          (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec

lemma spec.sraw_poly (Main : Vector (ZMod p) 69) (h : is_sraw_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRAW :=
  fun cstrs => spec.sraw_common_poly Main cstrs h.1

lemma spec.sraiw_poly (Main : Vector (ZMod p) 69) (h : is_sraiw_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRAW :=
  fun cstrs => spec.sraw_common_poly Main cstrs h.1

end sraw_poly

end ShiftRight
