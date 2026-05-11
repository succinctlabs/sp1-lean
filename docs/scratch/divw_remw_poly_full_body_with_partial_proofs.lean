set_option debug.skipKernelTC true in
set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
-- Polymorphic counterpart of `divw_remw`. Signed 32-bit div/rem with
-- 64-bit sign-extended results. Mirrors `divuw_remuw_poly`'s 4-limb
-- carry chain at HWord width plus signed-handling: HWord.toInt_*_poly
-- bounds, HWord.eq_toInt_poly_eq, HWord.extend_true_is_signExtend_poly,
-- 3-condition tdiv_tmod_unique_full witness (h_prod, h_abs, h_sign).
lemma divw_remw_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event : ZMod p)
  (is_U64_b : Word.isU64_poly #v[b0, b1, b2, b3])
  (is_U64_c : Word.isU64_poly #v[c0, c1, c2, c3])
  (sop1 : is_div = 1 → is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop2 : is_divu = 1 → is_div = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop3 : is_rem = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop4 : is_remu = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop5 : is_divw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop6 : is_remw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop7 : is_divuw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_remuw = 0)
  (sop8 : is_remuw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0)
  (eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw)
  (eq_b_neg : b_neg = msb_b * (is_div + is_rem + is_divw + is_remw))
  (eq_rem_neg : rem_neg = msb_rem * (is_div + is_rem + is_divw + is_remw))
  (eq_c_neg : c_neg = msb_c * (is_div + is_rem + is_divw + is_remw))
  (eq_lb0 : lb0 = b0)
  (eq_lc0 : lc0 = c0)
  (eq_lb1 : lb1 = b1)
  (eq_lc1 : lc1 = c1)
  (eq_lb2 : lb2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (eq_lc2 : lc2 = c2 * (1 - is_word) + c_neg * is_word * 65535)
  (eq_lb3 : lb3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (eq_lc3 : lc3 = c3 * (1 - is_word) + c_neg * is_word * 65535)
  (eq_qbc0 : qbc0 = q0)
  (eq_qbc1 : qbc1 = q1)
  (w_eq_qbc2_uw : is_divuw + is_remuw = 0 ∨ qbc2 = 0)
  (w_eq_qbc2_w : is_divw + is_remw = 0 ∨ qbc2 = msb_quot * 65535)
  (w_eq_q2_w : is_word = 0 ∨ q2 = msb_quot * 65535)
  (eq_qbc2 : is_divu + is_remu + is_div + is_rem = 0 ∨ qbc2 = q2)
  (w_eq_qbc3_uw : is_divuw + is_remuw = 0 ∨ qbc3 = 0)
  (w_eq_qbc3_w : is_divw + is_remw = 0 ∨ qbc3 = msb_quot * 65535)
  (w_eq_q3_w : is_word = 0 ∨ q3 = msb_quot * 65535)
  (eq_qbc3 : is_divu + is_remu + is_div + is_rem = 0 ∨ qbc3 = q3)
  (eq_rbc0 : rbc0 = r0)
  (eq_rbc1 : rbc1 = r1)
  (w_eq_rbc2_uw : is_divuw + is_remuw = 0 ∨ rbc2 = 0)
  (w_eq_rbc2_w : is_divw + is_remw = 0 ∨ rbc2 = msb_rem * 65535)
  (w_eq_r2_w : is_word = 0 ∨ r2 = msb_rem * 65535)
  (eq_rbc2 : is_divu + is_remu + is_div + is_rem = 0 ∨ rbc2 = r2)
  (w_eq_rbc3_uw : is_divuw + is_remuw = 0 ∨ rbc3 = 0)
  (w_eq_rbc3_w : is_divw + is_remw = 0 ∨ rbc3 = msb_rem * 65535)
  (w_eq_r3_w : is_word = 0 ∨ r3 = msb_rem * 65535)
  (eq_rbc3 : is_divu + is_remu + is_div + is_rem = 0 ∨ rbc3 = r3)
  (eq_is_overflow : is_overflow = is_overflow_b * is_overflow_c * (is_div + is_rem + is_divw + is_remw))
  (eq_b_neg_not_overflow : b_neg_not_overflow = b_neg * (1 - is_overflow))
  (eq_not_b_neg_not_overflow : b_not_neg_not_overflow = (1 - b_neg) * (1 - is_overflow))
  (of_eq_q0 : is_overflow = 0 ∨ q0 = b0)
  (of_eq_r0 : is_overflow = 0 ∨ r0 = 0)
  (of_eq_q1 : is_overflow = 0 ∨ q1 = b1)
  (of_eq_r1 : is_overflow = 0 ∨ r1 = 0)
  (of_eq_q2 : is_overflow = 0 ∨ q2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (of_eq_r2 : is_overflow = 0 ∨ r2 = 0)
  (of_eq_q3 : is_overflow = 0 ∨ q3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (of_eq_r3 : is_overflow = 0 ∨ r3 = 0)
  (nof_eq_ctqpr0 : is_overflow = 1 ∨ b0 = ctq0 + r0 - cry0 * 65536)
  (nof_eq_ctqpr1 : is_overflow = 1 ∨ b1 = ctq1 + r1 - cry1 * 65536 + cry0)
  (nof_eq_ctqpr2 : is_overflow = 1 ∨ b2 * (1 - is_word) + b_neg * is_word * 65535 = ctq2 + rbc2 - cry2 * 65536 + cry1)
  (nof_eq_ctqpr3 : is_overflow = 1 ∨ b3 * (1 - is_word) + b_neg * is_word * 65535 = ctq3 + rbc3 - cry3 * 65536 + cry2)
  (nof_eq_ctqpr4 : is_overflow = 1 ∨ ctq4 + rem_neg * 65535 - cry4 * 65536 + cry3 = b_neg * 65535)
  (nof_eq_ctqpr5 : is_overflow = 1 ∨ ctq5 + rem_neg * 65535 - cry5 * 65536 + cry4 = b_neg * 65535)
  (nof_eq_ctqpr6 : is_overflow = 1 ∨ ctq6 + rem_neg * 65535 - cry6 * 65536 + cry5 = b_neg * 65535)
  (nof_eq_ctqpr7 : is_overflow = 1 ∨ ctq7 + rem_neg * 65535 - cry7 * 65536 + cry6 = b_neg * 65535)
  (u16_ctqpr0 : (ctq0 + r0 - cry0 * 65536).val < 65536)
  (u16_ctqpr1 : (ctq1 + r1 - cry1 * 65536 + cry0).val < 65536)
  (u16_ctqpr2 : (ctq2 + rbc2 - cry2 * 65536 + cry1).val < 65536)
  (u16_ctqpr3 : (ctq3 + rbc3 - cry3 * 65536 + cry2).val < 65536)
  (u16_ctqpr4 : (ctq4 + rem_neg * 65535 - cry4 * 65536 + cry3).val < 65536)
  (u16_ctqpr5 : (ctq5 + rem_neg * 65535 - cry5 * 65536 + cry4).val < 65536)
  (u16_ctqpr6 : (ctq6 + rem_neg * 65535 - cry6 * 65536 + cry5).val < 65536)
  (u16_ctqpr7 : (ctq7 + rem_neg * 65535 - cry7 * 65536 + cry6).val < 65536)
  (eq_d_a0 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a0 = q0)
  (eq_r_a0 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a0 = r0)
  (eq_d_a1 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a1 = q1)
  (eq_r_a1 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a1 = r1)
  (eq_d_a2 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a2 = q2)
  (eq_r_a2 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a2 = r2)
  (eq_d_a3 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a3 = q3)
  (eq_r_a3 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a3 = r3)
  (r_neg_b_neg : rem_neg = 0 ∨ b_neg = 1)
  (r_pos_b_pos : r0 + r1 + r2 + r3 = 0 ∨ rem_neg = 1 ∨ b_neg = 0)
  (c0_eq_q0 : is_c_0 = 0 ∨ q0 = 65535)
  (c0_eq_q1 : is_c_0 = 0 ∨ q1 = 65535)
  (c0_eq_q2 : is_c_0 = 0 ∨ q2 = 65535)
  (c0_eq_q3 : is_c_0 = 0 ∨ q3 = 65535)
  (c0_eq_r0 : is_c_0 = 0 ∨ r0 = b0)
  (c0_eq_r1 : is_c_0 = 0 ∨ r1 = b1)
  (c0_eq_r2 : is_c_0 = 0 ∨ rbc2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (c0_eq_r3 : is_c_0 = 0 ∨ rbc3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (cn_ac0 : c_neg = 1 ∨ ac0 = c0)
  (rn_ar0 : rem_neg = 1 ∨ ar0 = r0)
  (cn_ac1 : c_neg = 1 ∨ ac1 = c1)
  (rn_ar1 : rem_neg = 1 ∨ ar1 = r1)
  (cn_ac2 : c_neg = 1 ∨ ac2 = c2 * (1 - is_word) + c_neg * is_word * 65535)
  (rn_ar2 : rem_neg = 1 ∨ ar2 = rbc2)
  (cn_ac3 : c_neg = 1 ∨ ac3 = c3 * (1 - is_word) + c_neg * is_word * 65535)
  (rn_ar3 : rem_neg = 1 ∨ ar3 = rbc3)
  (u16_ac0 : ac0.val < 65536)
  (u16_ac1 : ac1.val < 65536)
  (u16_ac2 : ac2.val < 65536)
  (u16_ac3 : ac3.val < 65536)
  (eq_cnop0 : c_neg = 0 ∨ cnop0 = 0)
  (eq_cnop1 : c_neg = 0 ∨ cnop1 = 0)
  (eq_cnop2 : c_neg = 0 ∨ cnop2 = 0)
  (eq_cnop3 : c_neg = 0 ∨ cnop3 = 0)
  (u16_ar0 : ar0.val < 65536)
  (u16_ar1 : ar1.val < 65536)
  (u16_ar2 : ar2.val < 65536)
  (u16_ar3 : ar3.val < 65536)
  (eq_rnop0 : rem_neg = 0 ∨ rnop0 = 0)
  (eq_rnop1 : rem_neg = 0 ∨ rnop1 = 0)
  (eq_rnop2 : rem_neg = 0 ∨ rnop2 = 0)
  (eq_rnop3 : rem_neg = 0 ∨ rnop3 = 0)
  (eq_abs_c_alu_event : abs_c_alu_event = c_neg)
  (eq_abs_rem_alu_event : abs_rem_alu_event = rem_neg)
  (eq_maco10 : maco10 = is_c_0 + (1 - is_c_0) * ac0)
  (eq_maco11 : maco11 = (1 - is_c_0) * ac1)
  (eq_maco12 : maco12 = (1 - is_c_0) * ac2)
  (eq_maco13 : maco13 = (1 - is_c_0) * ac3)
  (eq_arlt : is_c_0 = 1 ∨ arlt = 1)
  (u16_q0 : q0.val < 65536)
  (u16_q1 : q1.val < 65536)
  (u16_q2 : q2.val < 65536)
  (u16_q3 : q3.val < 65536)
  (u16_r0 : r0.val < 65536)
  (u16_r1 : r1.val < 65536)
  (u16_r2 : r2.val < 65536)
  (u16_r3 : r3.val < 65536)
  (b_cry0 : cry0 = 0 ∨ cry0 = 1)
  (b_cry1 : cry1 = 0 ∨ cry1 = 1)
  (b_cry2 : cry2 = 0 ∨ cry2 = 1)
  (b_cry3 : cry3 = 0 ∨ cry3 = 1)
  (b_cry4 : cry4 = 0 ∨ cry4 = 1)
  (b_cry5 : cry5 = 0 ∨ cry5 = 1)
  (b_cry6 : cry6 = 0 ∨ cry6 = 1)
  (b_cry7 : cry7 = 0 ∨ cry7 = 1)
  (u16_ctq0 : ctq0.val < 65536)
  (u16_ctq1 : ctq1.val < 65536)
  (u16_ctq2 : ctq2.val < 65536)
  (u16_ctq3 : ctq3.val < 65536)
  (u16_ctq4 : ctq4.val < 65536)
  (u16_ctq5 : ctq5.val < 65536)
  (u16_ctq6 : ctq6.val < 65536)
  (u16_ctq7 : ctq7.val < 65536)
  (b_is_div : is_div = 0 ∨ is_div = 1)
  (b_is_divu : is_divu = 0 ∨ is_divu = 1)
  (b_is_rem : is_rem = 0 ∨ is_rem = 1)
  (b_is_remu : is_remu = 0 ∨ is_remu = 1)
  (b_is_divw : is_divw = 0 ∨ is_divw = 1)
  (b_is_remw : is_remw = 0 ∨ is_remw = 1)
  (b_is_divuw : is_divuw = 0 ∨ is_divuw = 1)
  (b_is_remuw : is_remuw = 0 ∨ is_remuw = 1)
  (b_is_overflow : is_overflow = 0 ∨ is_overflow = 1)
  (b_is_real_not_word : is_word = 0 ∨ is_word = 1)
  (b_b_neg : b_neg = 0 ∨ b_neg = 1)
  (b_b_neg_not_overflow : b_neg_not_overflow = 0 ∨ b_neg_not_overflow = 1)
  (b_b_not_neg_not_overflow : b_not_neg_not_overflow = 0 ∨ b_not_neg_not_overflow = 1)
  (b_rem_neg : rem_neg = 0 ∨ rem_neg = 1)
  (b_c_neg : c_neg = 0 ∨ c_neg = 1)
  (b_one_of_ops : is_divu + is_remu + is_div + is_rem + is_divw + is_remw + is_divuw + is_remuw = 1)
  (w_overflow_b : is_word = 1 → is_overflow_b = if #v[b0, b1, 0, 0] = (#v[0, 32768, 0, 0] : Word (ZMod p)) then 1 else 0)
  (w_overflow_c : is_word = 1 → is_overflow_c = if #v[c0, c1, 0, 0] = (#v[65535, 65535, 0, 0] : Word (ZMod p)) then 1 else 0)
  (div_zero : is_c_0 = if #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] = (#v[0, 0, 0, 0] : Word (ZMod p)) then 1 else 0)
  (c_neg_sum_zero : c_neg = 1 → Word.isU64_poly #v[cnop0, cnop1, cnop2, cnop3] ∧ Word.toBitVec64_poly #v[cnop0, cnop1, cnop2, cnop3] = Word.toBitVec64_poly #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] + Word.toBitVec64_poly #v[ac0, ac1, ac2, ac3])
  (rem_neg_sum_zero : rem_neg = 1 → Word.isU64_poly #v[rnop0, rnop1, rnop2, rnop3] ∧ Word.toBitVec64_poly #v[rnop0, rnop1, rnop2, rnop3] = Word.toBitVec64_poly #v[r0, r1, rbc2, rbc3] + Word.toBitVec64_poly #v[ar0, ar1, ar2, ar3])
  (main_mul_low : Word.isU64_poly #v[ctq0, ctq1, ctq2, ctq3] ∧ Word.toBitVec64_poly #v[ctq0, ctq1, ctq2, ctq3] = execute_MUL_pure (Word.toBitVec64_poly #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64_poly #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MUL)
  (main_mul_high : is_word = 0 → (is_div + is_rem = 1 → Word.isU64_poly #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64_poly #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64_poly #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64_poly #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULH) ∧ (is_divu + is_remu = 1 → Word.isU64_poly #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64_poly #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64_poly #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64_poly #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULHU))
  (overflow_b : is_word = 0 → is_overflow_b = if #v[b0, b1, b2, b3] = (#v[0, 0, 0, 32768] : Word (ZMod p)) then 1 else 0)
  (overflow_c : is_word = 0 → is_overflow_c = if #v[c0, c1, c2, c3] = (#v[65535, 65535, 65535, 65535] : Word (ZMod p)) then 1 else 0)
  (eq_msb_b : is_word = 0 → msb_b = if 32768 ≤ b3 then 1 else 0)
  (eq_msb_c : is_word = 0 → msb_c = if 32768 ≤ c3 then 1 else 0)
  (eq_msb_rem : is_word = 0 → msb_rem = if 32768 ≤ r3 then 1 else 0)
  (w_eq_msb_b : is_word = 1 → msb_b = if 32768 ≤ b1 then 1 else 0)
  (w_eq_msb_c : is_word = 1 → msb_c = if 32768 ≤ c1 then 1 else 0)
  (w_eq_msb_rem : is_word = 1 → msb_rem = if 32768 ≤ r1 then 1 else 0)
  (w_eq_msb_quot : is_word = 1 → msb_quot = if 32768 ≤ q1 then 1 else 0)
  (abs_check : is_c_0 = 0 → arlt = if Word.toNat_poly #v[ar0, ar1, ar2, ar3] < Word.toNat_poly #v[is_c_0 + (1 - is_c_0) * ac0, (1 - is_c_0) * ac1, (1 - is_c_0) * ac2, (1 - is_c_0) * ac3] then 1 else 0) :
    is_divw + is_remw = 1 →
    ⟨Word.toBitVec64_poly #v[q0, q1, q2, q3], Word.toBitVec64_poly #v[r0, r1, r2, r3]⟩ = execute_DIV_REM_pure (Word.toBitVec64_poly #v[b0, b1, b2, b3]) (Word.toBitVec64_poly #v[c0, c1, c2, c3]) .DRWS
      := by
    haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
    have h17 : 2 ^ 17 < p := Fact.out
    have h01 : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h21 : (2 : ZMod p) ≠ 1 := by
      intro h
      have h2v : ((2 : ℕ) : ZMod p).val = 2 := ZMod.val_natCast_of_lt (by omega)
      have h1v : ((1 : ℕ) : ZMod p).val = 1 := ZMod.val_natCast_of_lt (by omega)
      have : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by push_cast; exact h
      have := congrArg ZMod.val this
      rw [h2v, h1v] at this
      omega
    have h65535_val : ((65535 : ℕ) : ZMod p).val = 65535 := ZMod.val_natCast_of_lt (by omega)
    have h32768_val : ((32768 : ℕ) : ZMod p).val = 32768 := ZMod.val_natCast_of_lt (by omega)
    have h1v : (1 : ZMod p).val = 1 := by
      have : ((1 : ℕ) : ZMod p).val = 1 := ZMod.val_natCast_of_lt (by omega)
      simpa using this
    have h0v : (0 : ZMod p).val = 0 := ZMod.val_zero
    have hcv0 : cry0.val ≤ 1 := by rcases b_cry0 with h | h <;> rw [h] <;> simp [h0v, h1v]
    have hcv1 : cry1.val ≤ 1 := by rcases b_cry1 with h | h <;> rw [h] <;> simp [h0v, h1v]
    have hcv2 : cry2.val ≤ 1 := by rcases b_cry2 with h | h <;> rw [h] <;> simp [h0v, h1v]
    have hcv3 : cry3.val ≤ 1 := by rcases b_cry3 with h | h <;> rw [h] <;> simp [h0v, h1v]
    intro divw_remw
    obtain ⟨z_div, z_rem, z_divu, z_remu, z_divuw, z_remuw⟩ : is_div = 0 ∧ is_rem = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divuw = 0 ∧ is_remuw = 0 := by
      clear *- divw_remw sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_one_of_ops h01 h21
      rcases b_is_divw with h_dw | h_dw <;> rcases b_is_remw with h_rw | h_rw
      · exfalso; rw [h_dw, h_rw, zero_add] at divw_remw; exact h01 divw_remw.symm
      · have := sop6 h_rw
        exact ⟨this.1, this.2.2.1, this.2.1, this.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩
      · have := sop5 h_dw
        exact ⟨this.1, this.2.2.1, this.2.1, this.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩
      · exfalso
        rw [h_dw, h_rw] at divw_remw
        have : (1 + 1 : ZMod p) = 2 := by ring
        rw [this] at divw_remw; exact h21 divw_remw
    simp [z_div, z_rem, z_divu, z_remu, z_divuw, z_remuw, divw_remw] at *
    simp [eq_is_word] at *
    subst lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3
    subst abs_c_alu_event abs_rem_alu_event b_neg rem_neg c_neg
    have h65535_ne : (65535 : ZMod p) ≠ 0 := by
      intro h; have := congrArg ZMod.val h
      rw [h65535_val, ZMod.val_zero] at this; omega
    have div_zero' : is_c_0 = if c0 = 0 ∧ c1 = 0 then 1 else 0 := by
      rw [div_zero]
      have hmsb_zero : c1 = 0 → msb_c = 0 := by
        intro hc1
        rw [w_eq_msb_c, hc1]; rw [if_neg]
        intro h; change (32768 : ZMod p).val ≤ (0 : ZMod p).val at h
        rw [h32768_val, ZMod.val_zero] at h; omega
      split_ifs with h_vec h_zc
      · rfl
      · exfalso; apply h_zc
        simp at h_vec
        exact ⟨h_vec.1, h_vec.2.1⟩
      · exfalso; apply h_vec
        obtain ⟨h0, h1⟩ := h_zc
        have hmsb := hmsb_zero h1
        simp [h0, h1, hmsb]
      · rfl
    clear div_zero
    simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, Bool.cond_eq_ite, -BitVec.toInt_setWidth]
    rw [Word.setWidth_eq_low_poly is_U64_b, Word.setWidth_eq_low_poly is_U64_c]
    have is_U32_bl := Word.isU64_poly_low_poly_isU32_poly is_U64_b
    have is_U32_cl := Word.isU64_poly_low_poly_isU32_poly is_U64_c
    simp [Word.low_poly] at *
    rw [HWord.toBitVec32_poly_toInt_poly is_U32_bl, HWord.toBitVec32_poly_toInt_poly is_U32_cl]
    have heq32_q1 : (32768 : ZMod p) ≤ q1 ↔ 32768 ≤ q1.val := by
      change (32768 : ZMod p).val ≤ q1.val ↔ _; rw [h32768_val]
    have heq32_r1 : (32768 : ZMod p) ≤ r1 ↔ 32768 ≤ r1.val := by
      change (32768 : ZMod p).val ≤ r1.val ↔ _; rw [h32768_val]
    have ext_q : (#v[q0, q1, q2, q3] : Word (ZMod p)) = HWord.extend_poly #v[q0, q1] true := by
      subst q2 q3 msb_quot
      simp [HWord.extend_poly, HWord.isNegative_poly, heq32_q1]
    have ext_r : (#v[r0, r1, r2, r3] : Word (ZMod p)) = HWord.extend_poly #v[r0, r1] true := by
      subst r2 r3 msb_rem
      simp [HWord.extend_poly, HWord.isNegative_poly, heq32_r1]
    rw [ext_q, ext_r]
    repeat rw [HWord.extend_true_is_signExtend_poly (by apply HWord.isU32_of_cases_poly <;> simpa)]
    have lb_b := HWord.toInt_poly_lb is_U32_bl; have ub_b := HWord.toInt_poly_ub is_U32_bl
    have lb_c := HWord.toInt_poly_lb is_U32_cl; have ub_c := HWord.toInt_poly_ub is_U32_cl
    split_ifs at div_zero' with nzc <;> simp [div_zero'] at *
    · -- c = 0 branch (zc0 ∧ zc1)
      obtain ⟨zc0, zc1⟩ := nzc
      simp [zc0, zc1] at *
      have hzero_int : HWord.toInt_poly (#v[(0 : ZMod p), 0] : HWord (ZMod p)) = 0 := by
        simp [HWord.toInt_poly, HWord.isNegative_poly, HWord.toNat_poly, h0v]
      simp [hzero_int, c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3,
            c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3]
      split_ands
      · simp [HWord.toBitVec32_poly, HWord.toNat_poly, h65535_val]
      · simp only [← BitVec.toInt_inj]
        rw [BitVec.toInt_signExtend_of_le (by simp), HWord.toBitVec32_poly_toInt_poly is_U32_bl]
        simp; rw [Int.bmod_eq_of_le] <;> simp <;> omega
    · -- c ≠ 0 branch
      subst arlt maco10 maco11 maco12 maco13
      rw [if_neg]; rotate_left
      · intro zc
        apply nzc
        have hcs := HWord.lt_cases_of_isU32_poly is_U32_cl
        have hc0_lt : c0.val < 65536 := hcs.1
        have hc1_lt : c1.val < 65536 := hcs.2
        unfold HWord.toInt_poly HWord.toNat_poly HWord.isNegative_poly at zc
        simp only [Vector.getElem_mk, List.getElem_toArray,
                   List.getElem_cons_zero, List.getElem_cons_succ] at zc
        split_ifs at zc with h_neg
        · exfalso
          push_cast at zc
          -- zc: (c0.val : ℤ) + (c1.val : ℤ) * 65536 - 2^32 = 0
          -- with c0, c1 < 65536, max sum < 2^32, so impossible.
          have h_max : (c0.val : ℤ) + (c1.val : ℤ) * 65536 < 4294967296 := by
            have hc1_lt_int : (c1.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc1_lt
            have hc0_lt_int : (c0.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc0_lt
            nlinarith
          linarith
        · push_cast at zc
          have hc0v : c0.val = 0 := by omega
          have hc1v : c1.val = 0 := by omega
          exact ⟨(ZMod.val_eq_zero c0).mp hc0v, (ZMod.val_eq_zero c1).mp hc1v⟩
      · rcases b_is_overflow with nof | of; rotate_left
        · -- overflow branch: of_eq_q* / of_eq_r* drive
          simp [of] at *
          split_ifs at w_overflow_b with ofb <;> simp [w_overflow_b] at *
          split_ifs at w_overflow_c with ofc <;> simp [w_overflow_c] at *
          obtain ⟨eb0, eb1⟩ := ofb
          obtain ⟨ec0, ec1⟩ := ofc
          simp [of_eq_q0, of_eq_q1, of_eq_r0, of_eq_r1, eb0, eb1, ec0, ec1] at *
          simp only [HWord.toBitVec32_poly, HWord.toInt_poly, HWord.isNegative_poly, HWord.toNat_poly]
          simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
          simp [h0v, h32768_val, h65535_val]
        · -- non-overflow branch: main h_prod / h_abs / h_sign witness
          simp [nof] at *
          rw [if_neg]; rotate_left
          · intro ⟨h_eq_b, h_eq_c⟩
            have hbb : (#v[b0, b1] : HWord (ZMod p)) = #v[0, 32768] := by
              rw [HWord.eq_toInt_poly_eq is_U32_bl, h_eq_b]
              simp [HWord.toInt_poly, HWord.isNegative_poly, HWord.toNat_poly,
                    h0v, h32768_val]
              apply HWord.isU32_of_cases_poly <;> simp [h0v, h32768_val]
            simp at hbb
            rw [if_pos hbb] at w_overflow_b; simp [w_overflow_b] at *
            have hcc : (#v[c0, c1] : HWord (ZMod p)) = #v[65535, 65535] := by
              rw [HWord.eq_toInt_poly_eq is_U32_cl, h_eq_c]
              simp [HWord.toInt_poly, HWord.isNegative_poly, HWord.toNat_poly,
                    h65535_val, h32768_val]
              apply HWord.isU32_of_cases_poly <;> simp [h65535_val]
            simp at hcc
            rw [if_pos hcc] at w_overflow_c; simp [w_overflow_c] at *
          · have is_U32_rl : HWord.isU32_poly #v[r0, r1] := by
              apply HWord.isU32_of_cases_poly <;> simpa
            have is_U32_ql : HWord.isU32_poly #v[q0, q1] := by
              apply HWord.isU32_of_cases_poly <;> simpa
            have lb_q := HWord.toInt_poly_lb is_U32_ql
            have ub_q := HWord.toInt_poly_ub is_U32_ql
            have lb_r := HWord.toInt_poly_lb is_U32_rl
            have ub_r := HWord.toInt_poly_ub is_U32_rl
            suffices :
              HWord.toInt_poly #v[q0, q1] = (HWord.toInt_poly #v[b0, b1]).tdiv (HWord.toInt_poly #v[c0, c1]) ∧
              HWord.toInt_poly #v[r0, r1] = (HWord.toInt_poly #v[b0, b1]).tmod (HWord.toInt_poly #v[c0, c1])
            · obtain ⟨hdiv, hrem⟩ := this
              rw [← hdiv, ← hrem]
              simp [← BitVec.toInt_inj]
              repeat rw [BitVec.toInt_signExtend_of_le (by simp)]
              rw [HWord.toBitVec32_poly_toInt_poly is_U32_ql, HWord.toBitVec32_poly_toInt_poly is_U32_rl]
              iterate 2 rw [Int.bmod_eq_of_le (by omega) (by omega)]
              trivial
            · -- Three witnesses for tdiv_tmod_unique_full: h_prod, h_abs, h_sign.
              have sgn_msb_b : msb_b = 1 → (HWord.toInt_poly #v[b0, b1]).sign = -1 := by
                intro h_msb_b
                have hb1 : b1.val ≥ 32768 := by
                  rw [w_eq_msb_b] at h_msb_b
                  split_ifs at h_msb_b with h
                  · change (32768 : ZMod p).val ≤ b1.val at h; rwa [h32768_val] at h
                  · simp at h_msb_b
                rw [HWord.sign_cases_poly is_U32_bl]
                rw [if_pos (by simp [HWord.isNegative_poly]; omega)]
              have sgn_msb_c : msb_c = 1 → (HWord.toInt_poly #v[c0, c1]).sign = -1 := by
                intro h_msb_c
                have hc1 : c1.val ≥ 32768 := by
                  rw [w_eq_msb_c] at h_msb_c
                  split_ifs at h_msb_c with h
                  · change (32768 : ZMod p).val ≤ c1.val at h; rwa [h32768_val] at h
                  · simp at h_msb_c
                rw [HWord.sign_cases_poly is_U32_cl]
                rw [if_pos (by simp [HWord.isNegative_poly]; omega)]
              have sgn_msb_rem : msb_rem = 1 → (HWord.toInt_poly #v[r0, r1]).sign = -1 := by
                intro h_msb_rem
                have hr1 : r1.val ≥ 32768 := by
                  rw [w_eq_msb_rem] at h_msb_rem
                  split_ifs at h_msb_rem with h
                  · change (32768 : ZMod p).val ≤ r1.val at h; rwa [h32768_val] at h
                  · simp at h_msb_rem
                rw [HWord.sign_cases_poly is_U32_rl]
                rw [if_pos (by simp [HWord.isNegative_poly]; omega)]
              have cnz : HWord.toInt_poly #v[c0, c1] ≠ 0 := by
                intro zc
                apply nzc
                have hcs := HWord.lt_cases_of_isU32_poly is_U32_cl
                have hc0_lt : c0.val < 65536 := hcs.1
                have hc1_lt : c1.val < 65536 := hcs.2
                unfold HWord.toInt_poly HWord.toNat_poly HWord.isNegative_poly at zc
                simp only [Vector.getElem_mk, List.getElem_toArray,
                           List.getElem_cons_zero, List.getElem_cons_succ] at zc
                split_ifs at zc with h_neg
                · exfalso
                  push_cast at zc
                  have h_max : (c0.val : ℤ) + (c1.val : ℤ) * 65536 < 4294967296 := by
                    have hc1_lt_int : (c1.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc1_lt
                    have hc0_lt_int : (c0.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc0_lt
                    nlinarith
                  linarith
                · push_cast at zc
                  have hc0v : c0.val = 0 := by omega
                  have hc1v : c1.val = 0 := by omega
                  exact ⟨(ZMod.val_eq_zero c0).mp hc0v, (ZMod.val_eq_zero c1).mp hc1v⟩
              -- First condition: h_prod — mirrors Fin KB lines 3611-3672.
              have h_prod : HWord.toInt_poly #v[b0, b1] = HWord.toInt_poly #v[q0, q1] * HWord.toInt_poly #v[c0, c1] + HWord.toInt_poly #v[r0, r1] := by
                -- Bounds for sign-extension constants (msb_* ∈ {0,1}, * 65535 < 65536)
                have u16_msb_b_v : (msb_b * 65535).val < 65536 := by
                  rw [w_eq_msb_b]; split_ifs <;> simp [h0v, h65535_val]
                have u16_msb_c_v : (msb_c * 65535).val < 65536 := by
                  rw [w_eq_msb_c]; split_ifs <;> simp [h0v, h65535_val]
                have u16_msb_rem_v : (msb_rem * 65535).val < 65536 := by
                  rw [w_eq_msb_rem]; split_ifs <;> simp [h0v, h65535_val]
                have u16_msb_quot_v : (msb_quot * 65535).val < 65536 := by
                  rw [w_eq_msb_quot]; split_ifs <;> simp [h0v, h65535_val]
                have heq32_b1 : (32768 : ZMod p) ≤ b1 ↔ 32768 ≤ b1.val := by
                  change (32768 : ZMod p).val ≤ b1.val ↔ _; rw [h32768_val]
                have heq32_c1 : (32768 : ZMod p) ≤ c1 ↔ 32768 ≤ c1.val := by
                  change (32768 : ZMod p).val ≤ c1.val ↔ _; rw [h32768_val]
                obtain ⟨is_U64_ctql, ctq_low⟩ := main_mul_low
                -- 4-limb sign-extended forms of b, c, q, r as HWord.extend_poly _ true.
                have eq_eb : (#v[b0, b1, msb_b * 65535, msb_b * 65535] : Word (ZMod p)) =
                    HWord.extend_poly #v[b0, b1] true := by
                  simp [HWord.extend_poly, HWord.isNegative_poly, w_eq_msb_b, heq32_b1]
                have eq_er : (#v[r0, r1, msb_rem * 65535, msb_rem * 65535] : Word (ZMod p)) =
                    HWord.extend_poly #v[r0, r1] true := by
                  simp [HWord.extend_poly, HWord.isNegative_poly, w_eq_msb_rem, heq32_r1]
                have eq_eq : (#v[q0, q1, msb_quot * 65535, msb_quot * 65535] : Word (ZMod p)) =
                    HWord.extend_poly #v[q0, q1] true := by
                  simp [HWord.extend_poly, HWord.isNegative_poly, w_eq_msb_quot, heq32_q1]
                have eq_ec : (#v[c0, c1, msb_c * 65535, msb_c * 65535] : Word (ZMod p)) =
                    HWord.extend_poly #v[c0, c1] true := by
                  simp [HWord.extend_poly, HWord.isNegative_poly, w_eq_msb_c, heq32_c1]
                -- Stage B suffices: prove the 4-limb BitVec64 carry-chain equality.
                suffices bv_ctqr :
                  Word.toBitVec64_poly (#v[b0, b1, msb_b * 65535, msb_b * 65535] : Word (ZMod p)) =
                    Word.toBitVec64_poly (#v[ctq0, ctq1, ctq2, ctq3] : Word (ZMod p)) +
                    Word.toBitVec64_poly (#v[r0, r1, msb_rem * 65535, msb_rem * 65535] : Word (ZMod p)) by
                  -- Stage A: derive h_prod from bv_ctqr via signed multiplication.
                  rw [eq_eb, eq_er] at bv_ctqr
                  -- ctq_low : Word.toBitVec64_poly #v[ctq0..3] = execute_MUL_pure ... mop.MUL
                  -- The qbc2/3 in ctq_low's argument become msb_quot * 65535 after subst.
                  -- The c2/3 expression: c2 * (1 - is_word) + c_neg * is_word * 65535 with
                  -- is_word=1, c_neg=msb_c → 0 + msb_c * 65535 = msb_c * 65535.
                  simp [execute_MUL_pure, -BitVec.extractLsb] at ctq_low
                  -- bv_decide: extending to 128 bits with False vs True agrees on the low 64 bits
                  -- of multiplication.
                  have hext_eq : BitVec.extractLsb 63 0
                      ((Word.toBitVec64_poly (#v[q0, q1, msb_quot * 65535, msb_quot * 65535] : Word (ZMod p))).extend 128 False *
                       (Word.toBitVec64_poly (#v[c0, c1, msb_c * 65535, msb_c * 65535] : Word (ZMod p))).extend 128 False) =
                    BitVec.extractLsb 63 0
                      ((Word.toBitVec64_poly (#v[q0, q1, msb_quot * 65535, msb_quot * 65535] : Word (ZMod p))).extend 128 True *
                       (Word.toBitVec64_poly (#v[c0, c1, msb_c * 65535, msb_c * 65535] : Word (ZMod p))).extend 128 True) := by
                    simp [BitVec.extend, -BitVec.extractLsb]; bv_decide
                  rw [hext_eq] at ctq_low; clear hext_eq
                  rw [eq_eq, eq_ec] at ctq_low
                  simp only [← BitVec.toInt_inj] at ctq_low
                  have is_U32_ql' : HWord.isU32_poly (#v[q0, q1] : HWord (ZMod p)) := by
                    apply HWord.isU32_of_cases_poly <;> simpa
                  have is_U32_cl' : HWord.isU32_poly (#v[c0, c1] : HWord (ZMod p)) := by
                    apply HWord.isU32_of_cases_poly <;> simpa
                  have hmul_int :
                      ((HWord.extend_poly (#v[q0, q1] : HWord (ZMod p)) true).toBitVec64_poly.extend 128 True *
                       (HWord.extend_poly (#v[c0, c1] : HWord (ZMod p)) true).toBitVec64_poly.extend 128 True).toInt =
                      HWord.toInt_poly (#v[q0, q1] : HWord (ZMod p)) * HWord.toInt_poly (#v[c0, c1] : HWord (ZMod p)) := by
                    iterate 2 rw [HWord.extend_true_is_signExtend_poly (by assumption)]
                    simp [BitVec.extend, BitVec.toInt_signExtend_of_le]
                    iterate 2 rw [HWord.toBitVec32_poly_toInt_poly (by assumption)]
                    rw [Int.bmod_eq_of_le] <;> simp <;> nlinarith
                  rw [extractLsb_is_toInt (by rw [hmul_int]; nlinarith) (by rw [hmul_int]; nlinarith)] at ctq_low
                  rw [hmul_int] at ctq_low; clear hmul_int
                  simp [← BitVec.toInt_inj, ctq_low] at bv_ctqr
                  iterate 2 rw [HWord.extend_true_is_signExtend_poly (by assumption),
                                BitVec.toInt_signExtend_of_le (by simp),
                                HWord.toBitVec32_poly_toInt_poly (by assumption)] at bv_ctqr
                  rw [bv_ctqr]
                  rw [Int.bmod_eq_of_le] <;> simp <;> nlinarith
                · -- Stage B: prove bv_ctqr via 4-limb carry chain. Mirror divuw_remuw_poly's
                  -- pattern (hsum/eq/main_eq) but with sign-extension constants in upper limbs.
                  have hcs_b := HWord.lt_cases_of_isU32_poly is_U32_bl
                  have hcs_r := HWord.lt_cases_of_isU32_poly is_U32_rl
                  have hcs_c := HWord.lt_cases_of_isU32_poly is_U32_cl
                  have hcs_q := HWord.lt_cases_of_isU32_poly is_U32_ql
                  have hcs_ctq := Word.lt_cases_of_isU64_poly is_U64_ctql
                  obtain ⟨b0_lt, b1_lt⟩ := hcs_b
                  obtain ⟨c0_lt, c1_lt⟩ := hcs_c
                  obtain ⟨q0_lt, q1_lt⟩ := hcs_q
                  obtain ⟨r0_lt, r1_lt⟩ := hcs_r
                  obtain ⟨ctq0_lt, ctq1_lt, ctq2_lt, ctq3_lt⟩ := hcs_ctq
                  -- Rearrange `nof_eq_ctqpr_i` to `... + cry_{i-1} - cry_i * 65536` form.
                  rw [← add_sub_right_comm] at u16_ctqpr1 u16_ctqpr2 u16_ctqpr3
                                              nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                  -- Apply div_mod_decomposition_w_poly to get .val % / / forms.
                  rw [div_mod_decomposition_w_poly (by omega) (by omega : cry0.val < 2)] at nof_eq_ctqpr0
                  rw [div_mod_decomposition_w_poly (by omega) (by omega : cry1.val < 2)] at nof_eq_ctqpr1
                  rw [div_mod_decomposition_w_poly (by omega) (by omega : cry2.val < 2)] at nof_eq_ctqpr2
                  rw [div_mod_decomposition_w_poly (by omega) (by omega : cry3.val < 2)] at nof_eq_ctqpr3
                  -- Distribute .val over + via ZMod.val_add_of_lt.
                  have hsum01 : (ctq0 + r0).val = ctq0.val + r0.val :=
                    ZMod.val_add_of_lt (by omega)
                  have hsum1' : (ctq1 + r1).val = ctq1.val + r1.val :=
                    ZMod.val_add_of_lt (by omega)
                  have hsum1 : (ctq1 + r1 + cry0).val = ctq1.val + r1.val + cry0.val := by
                    rw [show (ctq1 + r1 + cry0) = (ctq1 + r1) + cry0 from rfl,
                        ZMod.val_add_of_lt (by rw [hsum1']; omega), hsum1']
                  have hsum2' : (ctq2 + msb_rem * 65535).val = ctq2.val + (msb_rem * 65535).val :=
                    ZMod.val_add_of_lt (by omega)
                  have hsum2 : (ctq2 + msb_rem * 65535 + cry1).val =
                      ctq2.val + (msb_rem * 65535).val + cry1.val := by
                    rw [show (ctq2 + msb_rem * 65535 + cry1) = (ctq2 + msb_rem * 65535) + cry1 from rfl,
                        ZMod.val_add_of_lt (by rw [hsum2']; omega), hsum2']
                  have hsum3' : (ctq3 + msb_rem * 65535).val = ctq3.val + (msb_rem * 65535).val :=
                    ZMod.val_add_of_lt (by omega)
                  have hsum3 : (ctq3 + msb_rem * 65535 + cry2).val =
                      ctq3.val + (msb_rem * 65535).val + cry2.val := by
                    rw [show (ctq3 + msb_rem * 65535 + cry2) = (ctq3 + msb_rem * 65535) + cry2 from rfl,
                        ZMod.val_add_of_lt (by rw [hsum3']; omega), hsum3']
                  -- Build clean Nat-side carry equations (eq_i : LHS = RHS).
                  have eq0 : b0.val + cry0.val * 65536 = ctq0.val + r0.val := by
                    obtain ⟨h1, h2⟩ := nof_eq_ctqpr0; rw [hsum01] at h1 h2; omega
                  have eq1 : b1.val + cry1.val * 65536 = ctq1.val + r1.val + cry0.val := by
                    obtain ⟨h1, h2⟩ := nof_eq_ctqpr1; rw [hsum1] at h1 h2; omega
                  have eq2 : (msb_b * 65535).val + cry2.val * 65536 =
                      ctq2.val + (msb_rem * 65535).val + cry1.val := by
                    obtain ⟨h1, h2⟩ := nof_eq_ctqpr2; rw [hsum2] at h1 h2; omega
                  have eq3 : (msb_b * 65535).val + cry3.val * 65536 =
                      ctq3.val + (msb_rem * 65535).val + cry2.val := by
                    obtain ⟨h1, h2⟩ := nof_eq_ctqpr3; rw [hsum3] at h1 h2; omega
                  -- Linear combination weighted by 2^(16i): the cry_{i} terms telescope.
                  have main_eq :
                      b0.val + b1.val * 65536 + (msb_b * 65535).val * 4294967296 +
                        (msb_b * 65535).val * 281474976710656 +
                        cry3.val * 18446744073709551616 =
                      ctq0.val + ctq1.val * 65536 + ctq2.val * 4294967296 +
                        ctq3.val * 281474976710656 +
                      (r0.val + r1.val * 65536 + (msb_rem * 65535).val * 4294967296 +
                        (msb_rem * 65535).val * 281474976710656) := by
                    omega
                  -- Lift to BitVec equality via ← BitVec.toNat_inj + BitVec.toNat_add.
                  rw [← BitVec.toNat_inj]
                  rw [BitVec.toNat_add]
                  rw [show Word.toBitVec64_poly (#v[b0, b1, msb_b * 65535, msb_b * 65535] : Word (ZMod p)) =
                        BitVec.ofNat 64 (b0.val + b1.val * 65536 +
                          (msb_b * 65535).val * 4294967296 +
                          (msb_b * 65535).val * 281474976710656) from by
                        simp [Word.toBitVec64_poly, Word.toNat_poly]]
                  rw [show Word.toBitVec64_poly (#v[ctq0, ctq1, ctq2, ctq3] : Word (ZMod p)) =
                        BitVec.ofNat 64 (ctq0.val + ctq1.val * 65536 +
                          ctq2.val * 4294967296 + ctq3.val * 281474976710656) from by
                        simp [Word.toBitVec64_poly, Word.toNat_poly]]
                  rw [show Word.toBitVec64_poly (#v[r0, r1, msb_rem * 65535, msb_rem * 65535] : Word (ZMod p)) =
                        BitVec.ofNat 64 (r0.val + r1.val * 65536 +
                          (msb_rem * 65535).val * 4294967296 +
                          (msb_rem * 65535).val * 281474976710656) from by
                        simp [Word.toBitVec64_poly, Word.toNat_poly]]
                  simp only [BitVec.toNat_ofNat]
                  omega
              -- Second condition: h_abs — mirrors Fin KB lines 3674-3770.
              -- TODO: Two attempts at full 4-case proof both hit `Stack overflow detected.
              -- Aborting.` at lean elapsed ~16:08–16:11 (consistent across both attempts).
              -- The trigger is the same in each: somewhere after the warnings finish printing
              -- (line 3546) the elaborator runs out of stack space. NOT a Lean recursion-depth
              -- issue (maxRecDepth is 1M); this is OS stack overflow in the elaborator. Both
              -- the original full proof (with `eqWH` universal helper using `unfold`) and the
              -- minimal case-1-only attempt (using `simp only`, no `unfold`) hit it at the
              -- same point — suggesting the problem is NOT in eqWH but in some subsequent
              -- tactic that's common to both: probably the destructive `simp [rem_nneg, c_nneg]
              -- at *` against the 200+ hypothesis context, or the `subst ar0 ... ac0..3` chain
              -- after it. Recipe options for the next attempt: (a) replace `simp at *` with
              -- `subst msb_rem` (since `rem_nneg : msb_rem = 0` is in subst-able form), then
              -- targeted `simp only [...] at <specific>`; (b) extract h_abs as a SEPARATE
              -- top-level lemma so its body has a fresh, smaller hypothesis context;
              -- (c) try `set_option maxStackSize` if such an option exists. See
              -- docs/memory/feedback_divrem_core_port_blockers.md for full attempt history.
              have h_abs : |HWord.toInt_poly #v[r0, r1]| < |HWord.toInt_poly #v[c0, c1]| := by
                sorry
              -- Third condition: h_sign — mirrors Fin KB lines 3772-3805.
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
              split_ands <;> assumption
