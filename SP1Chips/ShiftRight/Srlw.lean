import SP1Chips.ShiftRight.Common

namespace ShiftRight

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
-- Unused variables expected because many proofs are currently stopped.
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 69)

section srlw

/-- Shared proof body for `spec.srlw` and `spec.srliw` — both prove the same `.SRLW`
equivalence from just `Main[66] = 1`. Extracted to avoid duplicating the 32-way
`rcases` case split. -/
private lemma spec.srlw_common
    (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
    (eq_srlw : Main[66] = 1) :
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRLW
  := by
    have ⟨is_U64_a, is_U64_b, is_U64_c⟩ := ops_U64 Main cstrs (srlw_real Main eq_srlw)
    obtain ⟨a0_16, a1_16, a2_16, a3_16⟩ := Word.lt_cases_of_isU64 is_U64_a
    obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨c0_16, c1_16, c2_16, c3_16⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨sop_1, sop_2, sop_3, sop_4⟩ := single_op Main cstrs
    replace cstrs := (allHold_constraints_iff Main).mp cstrs
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
    set msb_b := Main[36]
    set msb_srw := Main[37]
    set cb0 := Main[38]
    set cb1 := Main[39]
    set cb2 := Main[40]
    set cb3 := Main[41]
    set cb4 := Main[42]
    set cb5 := Main[43]
    set smv := Main[44]
    set v0123 := Main[45]
    set v012 := Main[46]
    set v01 := Main[47]
    set ll0 := Main[48]
    set ll1 := Main[49]
    set ll2 := Main[50]
    set ll3 := Main[51]
    set hl0 := Main[52]
    set hl1 := Main[53]
    set hl2 := Main[54]
    set hl3 := Main[55]
    set lr0 := Main[56]
    set lr1 := Main[57]
    set lr2 := Main[58]
    set lr3 := Main[59]
    set su160 := Main[60]
    set su161 := Main[61]
    set su162 := Main[62]
    set su163 := Main[63]
    set srl := Main[64]
    set sra := Main[65]
    set srlw := Main[66]
    set sraw := Main[67]
    set bop := Main[68]
    obtain ⟨h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
             b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             w_msb_b, eq_smv, w_msb_srv, sr_rest⟩ := cstrs
    obtain ⟨nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05, eq_op_a_0⟩ := sr_rest
    clear h_msb_b3 h_msb_b1 cpu alu eq_op_a_0
    symm at h_b2_dec h_b3_dec
    simp_all
    have is_U32_a : HWord.isU32 #v[ a0, a1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_b : HWord.isU32 #v[ b0, b1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_c : HWord.isU32 #v[ c0, c1 ] := by apply HWord.isU32_of_cases <;> assumption
    have ⟨eq_hl2, eq_ll2⟩ : hl2 = 0 ∧ ll2 = 0 := by
      clear *- lt_hl2 lt_ll2 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
      apply (cancel_mul_65536_v2 (by simp)) at h_b2_dec <;>
      simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b2_dec <;>
      rw [Nat.mod_eq_of_lt (by omega)] at h_b2_dec <;>
      split_ands <;> omega
    have ⟨eq_hl3, eq_ll3⟩ : hl3 = 0 ∧ ll3 = 0 := by
      clear *- lt_hl3 lt_ll3 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
      apply (cancel_mul_65536_v2 (by simp)) at h_b3_dec <;>
      simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b3_dec <;>
      rw [Nat.mod_eq_of_lt (by omega)] at h_b3_dec <;>
      split_ands <;> omega
    simp [eq_hl2, eq_ll2, eq_hl3, eq_ll3] at *
    simp_all
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
    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      · unfold HWord.isNegative; split_ifs <;> simp_all; omega
      · congr; rw [HWord.isNegative_msb is_U32_a]
    · suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = (HWord.toBitVec32 #v[b0, b1] >>> (c0.val % 32))
      · rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      · rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        rw [HWord.toBitVec32_toNat is_U32_a, HWord.toBitVec32_toNat is_U32_b]
        rw [this]; clear this h_a3
        cases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
        rcases b_cb3 <;> rcases b_cb4 <;> simp_all
        all_goals {
          (try apply cancel_mul_65536_v1 (by simp) at h_b0_dec)
          (try apply cancel_mul_65536_v1 (by simp) at h_b1_dec)
          simp_all [HWord.toNat]
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          omega
        }

lemma spec.srlw (h : is_srlw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRLW
  := fun cstrs => spec.srlw_common Main cstrs h.1

end srlw

section srliw

lemma spec.srliw (h : is_srliw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRLW
  := fun cstrs => spec.srlw_common Main cstrs h.1

end srliw

section srlw_poly

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 400000000 in
-- 400M heartbeats: 2-way byte_shift × 16-way cb0..cb3 rcases on top of the
-- SRLW prologue (deriving msb_srw, sign_extend bridge, hl2/ll2/hl3/ll3 = 0).
set_option debug.skipKernelTC true in
-- Skip kernel typechecking: `Word.toBitVec64_poly_toNat_poly` involves `2^N`
-- re-checks (mirrors `spec.srl_common_poly`'s use).
/-- Shared proof body for `spec.srlw_poly` and `spec.srliw_poly`. Structure
mirrors `spec.srl_common_poly` but for 32-bit operands:
- Forces `hl2 = ll2 = hl3 = ll3 = 0` via `cancel_mul_65536_zero_poly` (since
  the b2/b3 byte equations under SRLW have LHS multiplier 0).
- Reduces the 64-bit goal to a 32-bit shift via `sign_extend_32_to_64_msb_poly`.
- 32-way blast (cb5 forced 0 by 5-bit shamt) closes via existing
  `srl_close_su16_{0,1}_case` wrappers on the low half. -/
private lemma spec.srlw_common_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly) (eq_srlw : Main[66] = 1) :
    Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
      execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[25], Main[26], Main[27], Main[28]] .SRLW := by
  -- Setup (mirrors spec.srl_common_poly prologue).
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h_real := is_real_eq_one_of_srlw Main cstrs eq_srlw
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  have is_U64_a := ops_U64_a_poly Main cstrs h_real
  have is_U32_b := Word.isU64_poly_low_poly_isU32_poly is_U64_b
  have is_U32_c := Word.isU64_poly_low_poly_isU32_poly is_U64_c
  have is_U32_a := Word.isU64_poly_low_poly_isU32_poly is_U64_a
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨c0_16, _c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  obtain ⟨a0_16, a1_16, _a2_16, _a3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_a
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ] at b0_16 b1_16 b2_16 b3_16 c0_16 a0_16 a1_16
  obtain ⟨_, _, sop_3, _⟩ := single_op_poly Main cstrs
  have ⟨h_no_srl, h_no_sra, h_no_sraw⟩ := sop_3 eq_srlw
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
  -- Destructure cstrs (same shape as SRL/SRA prologue).
  obtain ⟨_, h_msb_a1, _, _, _,
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
    rw [h_no_srl, h_no_sra, eq_srlw, h_no_sraw] at h
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
  -- Under SRLW: srl + sra = 0, so the LHS multiplier in h_b2_dec, h_b3_dec is 0,
  -- forcing hl2 = ll2 = hl3 = ll3 = 0 via cancel_mul_65536_zero_poly (after 16
  -- cb sub-cases to identify v0123).
  rw [h_no_srl, h_no_sra] at h_b2_dec h_b3_dec
  simp only [add_zero, zero_add, zero_mul] at h_b2_dec h_b3_dec
  symm at h_b2_dec h_b3_dec
  -- Helper: under SRLW, given `M ∣ 65536`, `0 < M`, `v0123 = ((M : ℕ) : ZMod p)`,
  -- and bounds `hl.val < M`, `ll.val < 65536/M`, the equation
  -- `hl * 65536 + ll * v0123 = 0` gives `hl = 0 ∧ ll = 0`.
  -- (Bound shape matches `lt_lh2/lt_ll2` after the cb-determined v0123 value
  -- is fixed: lt_lh = `hl.val < 2^(16-S)` = M, lt_ll = `ll.val < 2^S` = 65536/M.)
  have zero_aux : ∀ (M : ℕ), M ∣ 65536 → 0 < M →
      ∀ {hl ll : ZMod p}, v0123 = ((M : ℕ) : ZMod p) →
      hl.val < M → ll.val < 65536 / M →
      hl * 65536 + ll * v0123 = 0 → hl = 0 ∧ ll = 0 := by
    intro M h_dvd h_pos hl ll h_v0123_eq h_hl_lt h_ll_lt h_eq
    have h_M_le : M ≤ 65536 := Nat.le_of_dvd (by omega) h_dvd
    have h_M_lt_p : M < p := by omega
    have h_v0123_val : v0123.val = M := by
      rw [h_v0123_eq]; exact ZMod.val_natCast_of_lt h_M_lt_p
    have h_v0123_dvd : v0123.val ∣ 65536 := by rw [h_v0123_val]; exact h_dvd
    have h_v0123_pos : 0 < v0123.val := by rw [h_v0123_val]; exact h_pos
    have h_cancel := cancel_mul_65536_zero_poly h_v0123_dvd h_v0123_pos h_eq
    rw [h_v0123_val] at h_cancel
    -- h_cancel : hl * ((65536/M : ℕ) : ZMod p) + ll = 0
    have h_quot_pos : 0 < 65536 / M := Nat.div_pos h_M_le h_pos
    have h_quot_le : 65536 / M ≤ 65536 := Nat.div_le_self _ _
    have h_M_quot_eq : M * (65536 / M) = 65536 := Nat.mul_div_cancel' h_dvd
    have h_quot_le_p : 65536 / M < p := by omega
    have h_hl_quot_lt : hl.val * (65536 / M) < 65536 := by
      nlinarith [h_hl_lt, h_M_quot_eq, h_pos, h_quot_pos]
    have h_hl_quot_lt_p : hl.val * (65536 / M) < p := by omega
    have h_hl_quot_val : (hl * ((65536 / M : ℕ) : ZMod p)).val = hl.val * (65536 / M) := by
      rw [ZMod.val_mul_of_lt]
      · rw [ZMod.val_natCast_of_lt h_quot_le_p]
      · rw [ZMod.val_natCast_of_lt h_quot_le_p]; exact h_hl_quot_lt_p
    have h_sum_lt_p : hl.val * (65536 / M) + ll.val < p := by
      have : hl.val * (65536 / M) + ll.val < 65536 + 65536 / M := by omega
      omega
    have h_sum_val : (hl * ((65536 / M : ℕ) : ZMod p) + ll).val =
                     hl.val * (65536 / M) + ll.val := by
      rw [ZMod.val_add_of_lt]
      · rw [h_hl_quot_val]
      · rw [h_hl_quot_val]; exact h_sum_lt_p
    have h_zero_val : (hl * ((65536 / M : ℕ) : ZMod p) + ll).val = 0 := by
      rw [h_cancel]; exact ZMod.val_zero
    rw [h_sum_val] at h_zero_val
    -- hl.val * (65536/M) + ll.val = 0 in ℕ ⇒ both factors zero.
    have h_hl_val_zero : hl.val = 0 := by
      have h_prod_zero : hl.val * (65536 / M) = 0 := by omega
      exact (Nat.mul_eq_zero.mp h_prod_zero).resolve_right (by omega)
    have h_ll_val_zero : ll.val = 0 := by omega
    exact ⟨(ZMod.val_eq_zero hl).mp h_hl_val_zero,
           (ZMod.val_eq_zero ll).mp h_ll_val_zero⟩
  -- TODO(srlw_poly_body): apply `zero_aux` in a 16-case cb dispatch for
  -- `(hl2, ll2)` and `(hl3, ll3)`, then reduce the goal via
  -- `sign_extend_32_to_64_msb_poly` + SRL byte-shift wrappers on the low half.
  sorry

lemma spec.srlw_poly (Main : Vector (ZMod p) 69) (h : is_srlw_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRLW :=
  fun cstrs => spec.srlw_common_poly Main cstrs h.1

lemma spec.srliw_poly (Main : Vector (ZMod p) 69) (h : is_srliw_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRLW :=
  fun cstrs => spec.srlw_common_poly Main cstrs h.1

end srlw_poly

end ShiftRight
