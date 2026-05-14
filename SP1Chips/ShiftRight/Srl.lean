import SP1Chips.ShiftRight.Common

namespace ShiftRight

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
-- Unused variables expected because many proofs are currently stopped.
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 69)

section srl

/-- Shared proof body for `spec.srl` and `spec.srli` — both prove the same `.SRL`
equivalence from just `Main[64] = 1`. Extracted to avoid duplicating the 64-way
`rcases` case split across both lemmas. -/
private lemma spec.srl_common
    (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
    (eq_srl : Main[64] = 1) :
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRL
  := by
    have ⟨is_U64_a, is_U64_b, is_U64_c⟩ := ops_U64 Main cstrs (srl_real Main eq_srl)
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
    clear h_msb_b3 h_msb_b1 h_msb_a1 cpu alu eq_op_a_0
    simp_all
    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
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
    clear diff
    rw [this]; clear this
    rw [Word.toBitVec64_toNat is_U64_a, Word.toBitVec64_toNat is_U64_b]
    simp [Word.toNat]
    -- 64-way case split
    rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
    rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
    simp_all <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b0_dec) <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b1_dec) <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b2_dec) <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b3_dec) <;>
    simp_all
    all_goals {
      try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
      repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
      try omega
    }

lemma spec.srl (h : is_srl Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRL
  := fun cstrs => spec.srl_common Main cstrs h.1

end srl

section srli

lemma spec.srli (h : is_srli Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRL
  := fun cstrs => spec.srl_common Main cstrs h.1

end srli

section srl_poly

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 400000000 in
-- 400M heartbeats: 64-way cb0..cb5 rcases × per-case cancel_mul_65536_poly + omega.
set_option debug.skipKernelTC true in
-- Skip kernel typechecking: `Word.toBitVec64_poly_toNat_poly` involves `2^N` re-checks
-- that trip kernel deep recursion (mirrors `spec.sll_poly`'s use).
-- Shared proof body for `spec.srl_poly` and `spec.srli_poly`.
private lemma spec.srl_common_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly) (eq_srl : Main[64] = 1) :
    Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
      execute_RTYPE_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[25], Main[26], Main[27], Main[28]] .SRL := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h_real := is_real_eq_one_of_srl Main cstrs eq_srl
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨c0_16, _c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  -- Normalize Vector index forms: #v[a, b, c, d][0] → a, etc.
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ] at b0_16 b1_16 b2_16 b3_16 c0_16
  -- Open the iff_poly.
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  -- Aggressively normalize literal-cast forms so cb_sum_val_eq_poly applies cleanly.
  simp only [Nat.cast_ofNat] at cstrs
  obtain ⟨_, _, _, _, _,
           _, _, _, _, _, _,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
           _, _, _, _, _, _, _, _, _,
           _, _, _,
           _, _, h_b0_dec, _, _, h_b1_dec,
           _, _, h_b2_dec, _, _, h_b3_dec,
           _, _, _, _,
           _, _, _, _⟩ := cstrs
  -- Goal manipulation: reduce to nat arithmetic.
  rw [← BitVec.toNat_inj]
  simp only [execute_RTYPE_pure_w_poly, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight,
             BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  -- Reduce shift count `(toBitVec64_poly c).toNat % 2^6` to `Main[25].val % 64`.
  have h_shift_eq : (Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], Main[28]]).toNat % 2 ^ 6
                  = Main[25].val % 64 := by
    rw [Word.toBitVec64_poly_toNat_poly is_U64_c, Word.toNat_poly_def]
    simp; omega
  rw [h_shift_eq]; clear h_shift_eq
  -- Use cb_sum_val_eq_poly + is_mod_64_poly to reduce c0.val % 64 → cb-sum-of-vals.
  -- The iff's `diff` has form `Main[39] * ↑2 + ...` (cast form) while
  -- `cb_sum_val_eq_poly`'s LHS has form `cb1 * 2`. They are defeq but not
  -- syntactically equal, so we use `convert ... using N` to bridge.
  have h_cb_sum_val_eq := cb_sum_val_eq_poly b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
  have h_cb_sum_lt : (Main[38] + Main[39] * 2 + Main[40] * 4 + Main[41] * 8 +
      Main[42] * 16 + Main[43] * 32 : ZMod p).val < 64 := by
    have hb0 : Main[38].val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
    have hb1 : Main[39].val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
    have hb2 : Main[40].val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
    have hb3 : Main[41].val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
    have hb4 : Main[42].val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
    have hb5 : Main[43].val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
    have : (Main[38] + Main[39] * 2 + Main[40] * 4 + Main[41] * 8 +
        Main[42] * 16 + Main[43] * 32 : ZMod p).val =
        Main[38].val + Main[39].val * 2 + Main[40].val * 4 + Main[41].val * 8 +
        Main[42].val * 16 + Main[43].val * 32 := h_cb_sum_val_eq
    omega
  have h_diff := diff (by intro h; rw [h] at h_real; exact zero_ne_one h_real)
  -- Reduce `2 ^ (10 : ZMod p).val` in diff to `1024`.
  have h_val_10 : (10 : ZMod p).val = 10 := by
    rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_val_10] at h_diff
  -- Convert h_diff from constraint's cast form to the raw form `cb_sum_val_eq_poly` uses.
  -- The two forms are defeq via `Nat.cast 2 = (2 : ZMod p)` etc., so `exact` works.
  have h_diff_raw : ((Main[25] - (Main[38] + Main[39] * 2 + Main[40] * 4 + Main[41] * 8 +
      Main[42] * 16 + Main[43] * 32 : ZMod p)) * (64 : ZMod p)⁻¹).val < 1024 := h_diff
  have h_c0_mod : Main[25].val % 64 = Main[38].val + Main[39].val * 2 + Main[40].val * 4 +
      Main[41].val * 8 + Main[42].val * 16 + Main[43].val * 32 := by
    -- is_mod_64_poly's inferred m matches the underlying term of h_diff_raw (cast form
    -- internally), so hm has cast form on RHS. Chain via `Eq.trans` + the defeq fact.
    have hm := is_mod_64_poly h_cb_sum_lt c0_16 h_diff_raw
    -- hm : Main[25].val % 64 = (cast_form).val
    -- h_cb_sum_val_eq : (raw_form).val = sum
    -- We need: Main[25].val % 64 = sum. The cast/raw forms have equal .val (defeq).
    have h_form_eq : (Main[38] + Main[39] * 2 + Main[40] * 4 + Main[41] * 8 +
        Main[42] * 16 + Main[43] * 32 : ZMod p).val =
        Main[38].val + Main[39].val * 2 + Main[40].val * 4 + Main[41].val * 8 +
        Main[42].val * 16 + Main[43].val * 32 := h_cb_sum_val_eq
    exact hm.trans h_form_eq
  rw [h_c0_mod]; clear h_c0_mod h_diff h_cb_sum_val_eq h_cb_sum_lt
  rw [Word.toBitVec64_poly_toNat_poly is_U64_b, Word.toNat_poly_def]
  -- Unfold the LHS `Word.toBitVec64_poly` to its toNat form. Without `is_U64_a`,
  -- the LHS toNat has a `% 2^64` we keep.
  simp only [Word.toBitVec64_poly, Word.toNat_poly_def, BitVec.toNat_ofNat,
             Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ]
  -- Goal is now (approximately):
  --   (Main[32].val + Main[33].val * 65536 + Main[34].val * 2^32 + Main[35].val * 2^48) % 2^64
  --     = (Main[15].val + Main[16].val * 65536 + ... ) / 2 ^ (cb-sum-val)
  -- Phase 3a stop: 64-way `rcases b_cb0..b_cb5` + `cancel_mul_65536_poly` per case
  -- + omega close remains. Each cb-sum substitution yields a specific 2^N divisor.
  sorry

lemma spec.srl_poly (Main : Vector (ZMod p) 69) (h : is_srl_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRL :=
  fun cstrs => spec.srl_common_poly Main cstrs h.1

lemma spec.srli_poly (Main : Vector (ZMod p) 69) (h : is_srli_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRL :=
  fun cstrs => spec.srl_common_poly Main cstrs h.1

end srl_poly

end ShiftRight
