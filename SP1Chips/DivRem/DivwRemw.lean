import SP1Chips.DivRem.Common

namespace DivRem

set_option linter.style.setOption false
set_option maxHeartbeats 100000000
-- The chip's `correct_*` proofs drive an imbalanced goal tree via chained
-- `apply ... at` / `specialize ... at` that operates on one focused case at a
-- time. Rewriting each to `<;>` would flatten the tree but require goal-state
-- reasoning the linter can't see; keep the existing structure.
set_option linter.style.multiGoal false
set_option linter.style.longLine false


attribute [-simp] mul_eq_zero not_and

section divw_remw

set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
-- Signed 32-bit div/rem with 64-bit sign-extended results. Mirrors
-- `divuw_remuw_poly`'s 4-limb carry chain at HWord width plus signed
-- handling: HWord.toInt_*_poly bounds, HWord.eq_toInt_poly_eq,
-- HWord.extend_true_is_signExtend_poly, 3-condition tdiv_tmod_unique_full
-- witness (h_prod, h_abs, h_sign).
lemma divw_remw_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
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
  (c_neg_sum_zero : c_neg = 1 → Word.isU64_poly #v[cnop0, cnop1, cnop2, cnop3] ∧ Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] = Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] + Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
  (rem_neg_sum_zero : rem_neg = 1 → Word.isU64_poly #v[rnop0, rnop1, rnop2, rnop3] ∧ Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] = Word.toBitVec64 #v[r0, r1, rbc2, rbc3] + Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
  (main_mul_low : Word.isU64_poly #v[ctq0, ctq1, ctq2, ctq3] ∧ Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MUL)
  (main_mul_high : is_word = 0 → (is_div + is_rem = 1 → Word.isU64_poly #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULH) ∧ (is_divu + is_remu = 1 → Word.isU64_poly #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULHU))
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
    ⟨Word.toBitVec64 #v[q0, q1, q2, q3], Word.toBitVec64 #v[r0, r1, r2, r3]⟩ = execute_DIV_REM_pure (Word.toBitVec64 #v[b0, b1, b2, b3]) (Word.toBitVec64 #v[c0, c1, c2, c3]) .DRWS
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
        rw [val_32768_zmod_p, ZMod.val_zero] at h; omega
      by_cases hzc : c0 = 0 ∧ c1 = 0
      · rw [if_pos hzc, if_pos]
        obtain ⟨h0, h1⟩ := hzc
        simp [h0, h1, hmsb_zero h1]
      · rw [if_neg hzc, if_neg]
        intro hvec
        exact hzc ⟨hvec.1, hvec.2.1⟩
    clear div_zero
    simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, Bool.cond_eq_ite, -BitVec.toInt_setWidth]
    rw [Word.setWidth_eq_low_poly is_U64_b, Word.setWidth_eq_low_poly is_U64_c]
    have is_U32_bl := Word.isU64_poly_low_poly_isU32_poly is_U64_b
    have is_U32_cl := Word.isU64_poly_low_poly_isU32_poly is_U64_c
    simp [Word.low_poly] at *
    rw [HWord.toBitVec32_poly_toInt_poly is_U32_bl, HWord.toBitVec32_poly_toInt_poly is_U32_cl]
    have heq32_q1 : (32768 : ZMod p) ≤ q1 ↔ 32768 ≤ q1.val := by
      change (32768 : ZMod p).val ≤ q1.val ↔ _; rw [val_32768_zmod_p]
    have heq32_r1 : (32768 : ZMod p) ≤ r1 ↔ 32768 ≤ r1.val := by
      change (32768 : ZMod p).val ≤ r1.val ↔ _; rw [val_32768_zmod_p]
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
                  · change (32768 : ZMod p).val ≤ b1.val at h; rwa [val_32768_zmod_p] at h
                  · simp at h_msb_b
                rw [HWord.sign_cases_poly is_U32_bl]
                rw [if_pos (by simp [HWord.isNegative_poly]; omega)]
              have sgn_msb_c : msb_c = 1 → (HWord.toInt_poly #v[c0, c1]).sign = -1 := by
                intro h_msb_c
                have hc1 : c1.val ≥ 32768 := by
                  rw [w_eq_msb_c] at h_msb_c
                  split_ifs at h_msb_c with h
                  · change (32768 : ZMod p).val ≤ c1.val at h; rwa [val_32768_zmod_p] at h
                  · simp at h_msb_c
                rw [HWord.sign_cases_poly is_U32_cl]
                rw [if_pos (by simp [HWord.isNegative_poly]; omega)]
              have sgn_msb_rem : msb_rem = 1 → (HWord.toInt_poly #v[r0, r1]).sign = -1 := by
                intro h_msb_rem
                have hr1 : r1.val ≥ 32768 := by
                  rw [w_eq_msb_rem] at h_msb_rem
                  split_ifs at h_msb_rem with h
                  · change (32768 : ZMod p).val ≤ r1.val at h; rwa [val_32768_zmod_p] at h
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
              -- First condition: h_prod.
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
                  change (32768 : ZMod p).val ≤ b1.val ↔ _; rw [val_32768_zmod_p]
                have heq32_c1 : (32768 : ZMod p) ≤ c1 ↔ 32768 ≤ c1.val := by
                  change (32768 : ZMod p).val ≤ c1.val ↔ _; rw [val_32768_zmod_p]
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
                  Word.toBitVec64 (#v[b0, b1, msb_b * 65535, msb_b * 65535] : Word (ZMod p)) =
                    Word.toBitVec64 (#v[ctq0, ctq1, ctq2, ctq3] : Word (ZMod p)) +
                    Word.toBitVec64 (#v[r0, r1, msb_rem * 65535, msb_rem * 65535] : Word (ZMod p)) by
                  -- Stage A: derive h_prod from bv_ctqr via signed multiplication.
                  rw [eq_eb, eq_er] at bv_ctqr
                  -- ctq_low : Word.toBitVec64 #v[ctq0..3] = execute_MUL_pure ... mop.MUL
                  -- The qbc2/3 in ctq_low's argument become msb_quot * 65535 after subst.
                  -- The c2/3 expression: c2 * (1 - is_word) + c_neg * is_word * 65535 with
                  -- is_word=1, c_neg=msb_c → 0 + msb_c * 65535 = msb_c * 65535.
                  simp [execute_MUL_pure, -BitVec.extractLsb] at ctq_low
                  -- bv_decide: extending to 128 bits with False vs True agrees on the low 64 bits
                  -- of multiplication.
                  have hext_eq : BitVec.extractLsb 63 0
                      ((Word.toBitVec64 (#v[q0, q1, msb_quot * 65535, msb_quot * 65535] : Word (ZMod p))).extend 128 False *
                       (Word.toBitVec64 (#v[c0, c1, msb_c * 65535, msb_c * 65535] : Word (ZMod p))).extend 128 False) =
                    BitVec.extractLsb 63 0
                      ((Word.toBitVec64 (#v[q0, q1, msb_quot * 65535, msb_quot * 65535] : Word (ZMod p))).extend 128 True *
                       (Word.toBitVec64 (#v[c0, c1, msb_c * 65535, msb_c * 65535] : Word (ZMod p))).extend 128 True) := by
                    simp [BitVec.extend, -BitVec.extractLsb]; bv_decide
                  rw [hext_eq] at ctq_low; clear hext_eq
                  rw [eq_eq, eq_ec] at ctq_low
                  simp only [← BitVec.toInt_inj] at ctq_low
                  have hmul_int :
                      ((HWord.extend_poly (#v[q0, q1] : HWord (ZMod p)) true).toBitVec64.extend 128 True *
                       (HWord.extend_poly (#v[c0, c1] : HWord (ZMod p)) true).toBitVec64.extend 128 True).toInt =
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
                  -- Normalize Vector indexing in bounds (e.g., #v[b0, b1][0] → b0)
                  -- so omega can match them against the goal's direct .val terms.
                  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at b0_lt b1_lt c0_lt c1_lt q0_lt q1_lt r0_lt r1_lt ctq0_lt ctq1_lt ctq2_lt ctq3_lt
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
                  rw [show Word.toBitVec64 (#v[b0, b1, msb_b * 65535, msb_b * 65535] : Word (ZMod p)) =
                        BitVec.ofNat 64 (b0.val + b1.val * 65536 +
                          (msb_b * 65535).val * 4294967296 +
                          (msb_b * 65535).val * 281474976710656) from by
                        simp [Word.toBitVec64, Word.toNat_poly]]
                  rw [show Word.toBitVec64 (#v[ctq0, ctq1, ctq2, ctq3] : Word (ZMod p)) =
                        BitVec.ofNat 64 (ctq0.val + ctq1.val * 65536 +
                          ctq2.val * 4294967296 + ctq3.val * 281474976710656) from by
                        simp [Word.toBitVec64, Word.toNat_poly]]
                  rw [show Word.toBitVec64 (#v[r0, r1, msb_rem * 65535, msb_rem * 65535] : Word (ZMod p)) =
                        BitVec.ofNat 64 (r0.val + r1.val * 65536 +
                          (msb_rem * 65535).val * 4294967296 +
                          (msb_rem * 65535).val * 281474976710656) from by
                        simp [Word.toBitVec64, Word.toNat_poly]]
                  simp only [BitVec.toNat_ofNat]
                  omega
              -- Second condition: h_abs. 4-way rcases on (b_rem_neg, b_c_neg);
              -- non-neg cases close via abs_check; neg cases use sum_zero_abs_poly +
              -- Word_toInt_poly_neg_form_eq_HWord_toInt_poly to bridge 4-limb Word.toInt_poly
              -- (with sign-extended 65535 upper limbs) to the 2-limb HWord.toInt_poly.
              have h_abs : |HWord.toInt_poly #v[r0, r1]| < |HWord.toInt_poly #v[c0, c1]| := by
                have is_U64_ar : Word.isU64_poly #v[ar0, ar1, ar2, ar3] := by
                  apply Word.isU64_of_cases_poly <;> simpa
                have is_U64_ac : Word.isU64_poly #v[ac0, ac1, ac2, ac3] := by
                  apply Word.isU64_of_cases_poly <;> simpa
                have hp17 : 2 ^ 17 < p := Fact.out
                have ⟨hc0_lt, hc1_lt⟩ := HWord.lt_cases_of_isU32_poly is_U32_cl
                have ⟨hr0_lt, hr1_lt⟩ := HWord.lt_cases_of_isU32_poly is_U32_rl
                have ⟨hac0_lt, hac1_lt, hac2_lt, hac3_lt⟩ := Word.lt_cases_of_isU64_poly is_U64_ac
                have ⟨har0_lt, har1_lt, har2_lt, har3_lt⟩ := Word.lt_cases_of_isU64_poly is_U64_ar
                simp only [Vector.getElem_mk, List.getElem_toArray,
                           List.getElem_cons_zero, List.getElem_cons_succ]
                  at hc0_lt hc1_lt hr0_lt hr1_lt hac0_lt hac1_lt hac2_lt hac3_lt
                       har0_lt har1_lt har2_lt har3_lt
                have h65535_v : ((65535 : ℕ) : ZMod p).val = 65535 :=
                  ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
                have h65535_lt : ((65535 : ℕ) : ZMod p).val < 65536 := by rw [h65535_v]; omega
                have h65535_ge : ((65535 : ℕ) : ZMod p).val ≥ 32768 := by rw [h65535_v]; omega
                rcases b_rem_neg with rem_nneg | rem_neg <;>
                  rcases b_c_neg with c_nneg | c_neg
                · -- Case 1: msb_rem = 0, msb_c = 0
                  simp [rem_nneg, c_nneg] at *
                  subst ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3
                  -- After simp, w_eq_msb_rem : ¬ (32768 : ZMod p) ≤ r1, similarly w_eq_msb_c.
                  -- Convert to .val form so omega can use them.
                  have hr1_lt_val : r1.val < 32768 := by
                    by_contra h; push Not at h
                    apply w_eq_msb_rem
                    change (32768 : ZMod p).val ≤ r1.val
                    rw [val_32768_zmod_p]; exact h
                  have hc1_lt_val : c1.val < 32768 := by
                    by_contra h; push Not at h
                    apply w_eq_msb_c
                    change (32768 : ZMod p).val ≤ c1.val
                    rw [val_32768_zmod_p]; exact h
                  simp [HWord.toInt_poly, HWord.isNegative_poly]
                  iterate 2 rw [if_neg (by omega)]
                  simp [Word.toNat_poly] at abs_check
                  simpa
                · -- Case 2: msb_rem = 0, msb_c = 1
                  simp [rem_nneg, c_neg] at *
                  subst ar0 ar1 ar2 ar3 cnop0 cnop1 cnop2 cnop3
                  simp at *
                  obtain ⟨_, heqz⟩ := c_neg_sum_zero
                  have ⟨hc0_lt, hc1_lt⟩ := HWord.lt_cases_of_isU32_poly is_U32_cl
                  have ⟨hac0_lt, hac1_lt, hac2_lt, hac3_lt⟩ := Word.lt_cases_of_isU64_poly is_U64_ac
                  have hisU64_c_neg : Word.isU64_poly (#v[c0, c1, 65535, 65535] : Word (ZMod p)) :=
                    Word.isU64_of_cases_poly hc0_lt hc1_lt h65535_lt h65535_lt
                  apply sum_zero_abs_poly hisU64_c_neg is_U64_ac
                    (by change ((65535 : ℕ) : ZMod p).val ≥ 32768; exact h65535_ge) at heqz
                  obtain ⟨hc_lb, hc_nlb⟩ := heqz
                  have hcc : Word.toInt_poly (#v[c0, c1, 65535, 65535] : Word (ZMod p))
                      = HWord.toInt_poly #v[c0, c1] :=
                    Word_toInt_poly_neg_form_eq_HWord_toInt_poly w_eq_msb_c h65535_val
                  rw [hcc] at hc_lb hc_nlb; clear hcc
                  have hr1_lt_val : r1.val < 32768 := by
                    by_contra h; push Not at h
                    apply w_eq_msb_rem
                    change (32768 : ZMod p).val ≤ r1.val
                    rw [val_32768_zmod_p]; exact h
                  by_cases is_c_lb : HWord.toInt_poly #v[c0, c1] = -2 ^ 63
                  · omega
                  · have is_c_lb' := is_c_lb
                    apply hc_nlb at is_c_lb'
                    have hac_nneg : ¬ Word.isNegative_poly #v[ac0, ac1, ac2, ac3] := by
                      rw [Word.isNegative_poly_toInt_poly is_U64_ac, is_c_lb']
                      exact not_lt.mpr (abs_nonneg _)
                    have hr_nneg : ¬ HWord.isNegative_poly #v[r0, r1] := by
                      unfold HWord.isNegative_poly
                      simp only [Vector.getElem_mk, List.getElem_toArray,
                                 List.getElem_cons_zero, List.getElem_cons_succ]
                      omega
                    rw [← is_c_lb']
                    rw [Word.toInt_poly, if_neg hac_nneg,
                        HWord.toInt_poly, if_neg hr_nneg]
                    simp [HWord.toNat_poly, Word.toNat_poly]
                    simp [Word.toNat_poly] at abs_check
                    push_cast [ZMod.cast_eq_val]
                    rw [abs_of_nonneg (by positivity)]
                    exact_mod_cast abs_check
                · -- Case 3: msb_rem = 1, msb_c = 0
                  simp [rem_neg, c_nneg] at *
                  subst ac0 ac1 ac2 ac3 rnop0 rnop1 rnop2 rnop3
                  simp at *
                  obtain ⟨_, heqz⟩ := rem_neg_sum_zero
                  have ⟨hr0_lt, hr1_lt⟩ := HWord.lt_cases_of_isU32_poly is_U32_rl
                  have ⟨har0_lt, har1_lt, har2_lt, har3_lt⟩ := Word.lt_cases_of_isU64_poly is_U64_ar
                  have hisU64_r_neg : Word.isU64_poly (#v[r0, r1, 65535, 65535] : Word (ZMod p)) :=
                    Word.isU64_of_cases_poly hr0_lt hr1_lt h65535_lt h65535_lt
                  apply sum_zero_abs_poly hisU64_r_neg is_U64_ar
                    (by change ((65535 : ℕ) : ZMod p).val ≥ 32768; exact h65535_ge) at heqz
                  obtain ⟨hr_lb, hr_nlb⟩ := heqz
                  have hrr : Word.toInt_poly (#v[r0, r1, 65535, 65535] : Word (ZMod p))
                      = HWord.toInt_poly #v[r0, r1] :=
                    Word_toInt_poly_neg_form_eq_HWord_toInt_poly w_eq_msb_rem h65535_val
                  rw [hrr] at hr_lb hr_nlb; clear hrr
                  have hc1_lt_val : c1.val < 32768 := by
                    by_contra h; push Not at h
                    apply w_eq_msb_c
                    change (32768 : ZMod p).val ≤ c1.val
                    rw [val_32768_zmod_p]; exact h
                  by_cases is_rem_lb : HWord.toInt_poly #v[r0, r1] = -2 ^ 63
                  · omega
                  · have is_rem_lb' := is_rem_lb
                    apply hr_nlb at is_rem_lb'
                    have har_nneg : ¬ Word.isNegative_poly #v[ar0, ar1, ar2, ar3] := by
                      rw [Word.isNegative_poly_toInt_poly is_U64_ar, is_rem_lb']
                      exact not_lt.mpr (abs_nonneg _)
                    have hc_nneg : ¬ HWord.isNegative_poly #v[c0, c1] := by
                      unfold HWord.isNegative_poly
                      simp only [Vector.getElem_mk, List.getElem_toArray,
                                 List.getElem_cons_zero, List.getElem_cons_succ]
                      omega
                    rw [← is_rem_lb']
                    rw [Word.toInt_poly, if_neg har_nneg,
                        HWord.toInt_poly, if_neg hc_nneg]
                    simp [HWord.toNat_poly, Word.toNat_poly]
                    simp [Word.toNat_poly] at abs_check
                    push_cast [ZMod.cast_eq_val]
                    rw [abs_of_nonneg (by positivity)]
                    exact_mod_cast abs_check
                · -- Case 4: msb_rem = 1, msb_c = 1
                  simp [rem_neg, c_neg] at *
                  subst rnop0 rnop1 rnop2 rnop3 cnop0 cnop1 cnop2 cnop3
                  obtain ⟨_, heqz_c⟩ := c_neg_sum_zero
                  obtain ⟨_, heqz_rem⟩ := rem_neg_sum_zero
                  have ⟨hc0_lt, hc1_lt⟩ := HWord.lt_cases_of_isU32_poly is_U32_cl
                  have ⟨hr0_lt, hr1_lt⟩ := HWord.lt_cases_of_isU32_poly is_U32_rl
                  have ⟨hac0_lt, hac1_lt, hac2_lt, hac3_lt⟩ := Word.lt_cases_of_isU64_poly is_U64_ac
                  have ⟨har0_lt, har1_lt, har2_lt, har3_lt⟩ := Word.lt_cases_of_isU64_poly is_U64_ar
                  have hisU64_c_neg : Word.isU64_poly (#v[c0, c1, 65535, 65535] : Word (ZMod p)) :=
                    Word.isU64_of_cases_poly hc0_lt hc1_lt h65535_lt h65535_lt
                  have hisU64_r_neg : Word.isU64_poly (#v[r0, r1, 65535, 65535] : Word (ZMod p)) :=
                    Word.isU64_of_cases_poly hr0_lt hr1_lt h65535_lt h65535_lt
                  apply sum_zero_abs_poly hisU64_c_neg is_U64_ac
                    (by change ((65535 : ℕ) : ZMod p).val ≥ 32768; exact h65535_ge) at heqz_c
                  apply sum_zero_abs_poly hisU64_r_neg is_U64_ar
                    (by change ((65535 : ℕ) : ZMod p).val ≥ 32768; exact h65535_ge) at heqz_rem
                  have eqc : Word.toInt_poly (#v[c0, c1, 65535, 65535] : Word (ZMod p))
                      = HWord.toInt_poly #v[c0, c1] :=
                    Word_toInt_poly_neg_form_eq_HWord_toInt_poly w_eq_msb_c h65535_val
                  have eqr : Word.toInt_poly (#v[r0, r1, 65535, 65535] : Word (ZMod p))
                      = HWord.toInt_poly #v[r0, r1] :=
                    Word_toInt_poly_neg_form_eq_HWord_toInt_poly w_eq_msb_rem h65535_val
                  rw [eqc] at heqz_c
                  rw [eqr] at heqz_rem
                  by_cases is_c_lb : HWord.toInt_poly #v[c0, c1] = -2 ^ 63
                  · by_contra; clear *- lb_c ub_c is_c_lb; omega
                  · by_cases is_r_lb : HWord.toInt_poly #v[r0, r1] = -2 ^ 63
                    · by_contra; clear *- lb_r ub_r is_r_lb; omega
                    · obtain ⟨_, hc_nlb⟩ := heqz_c
                      obtain ⟨_, hr_nlb⟩ := heqz_rem
                      specialize hc_nlb is_c_lb
                      specialize hr_nlb is_r_lb
                      have hac_nneg : ¬ Word.isNegative_poly #v[ac0, ac1, ac2, ac3] := by
                        rw [Word.isNegative_poly_toInt_poly is_U64_ac, hc_nlb]
                        exact not_lt.mpr (abs_nonneg _)
                      have har_nneg : ¬ Word.isNegative_poly #v[ar0, ar1, ar2, ar3] := by
                        rw [Word.isNegative_poly_toInt_poly is_U64_ar, hr_nlb]
                        exact not_lt.mpr (abs_nonneg _)
                      rw [← hc_nlb, ← hr_nlb]
                      rw [Word.toInt_poly, if_neg har_nneg]
                      rw [Word.toInt_poly, if_neg hac_nneg]
                      simp [Word.toNat_poly]
                      simp [Word.toNat_poly] at abs_check
                      push_cast [ZMod.cast_eq_val]
                      exact_mod_cast abs_check
              -- Third condition: h_sign. Case-split b_b_neg; within msb_b=1, case-split b_rem_neg
              -- to avoid relying on a multi-limb sum bound (only the 2-limb r0 + r1 = 0 case
              -- needs `Fact (2 ^ 17 < p)`). For msb_b=0 case, use
              -- sign_cases_poly + h_prod + h_abs + nlinarith.
              have h_sign : HWord.toInt_poly #v[r0, r1] = 0 ∨
                  (HWord.toInt_poly #v[r0, r1]).sign = (HWord.toInt_poly #v[b0, b1]).sign := by
                rcases b_b_neg with b_msb_nneg | b_msb_neg
                · -- msb_b = 0
                  subst b_msb_nneg
                  have hmsb_rem_0 : msb_rem = 0 := by
                    rcases r_neg_b_neg with h | h
                    · exact h
                    · exact absurd h zero_ne_one
                  subst hmsb_rem_0
                  -- HWord.isNegative_poly uses .val ≥ 32768 form, so derive bounds in .val terms.
                  have hr1_lt_val : r1.val < 32768 := by
                    by_contra h; push Not at h
                    have : (32768 : ZMod p) ≤ r1 := by
                      change (32768 : ZMod p).val ≤ r1.val
                      rw [val_32768_zmod_p]; exact h
                    rw [if_pos this] at w_eq_msb_rem
                    exact zero_ne_one w_eq_msb_rem
                  have hb1_lt_val : b1.val < 32768 := by
                    by_contra h; push Not at h
                    have : (32768 : ZMod p) ≤ b1 := by
                      change (32768 : ZMod p).val ≤ b1.val
                      rw [val_32768_zmod_p]; exact h
                    rw [if_pos this] at w_eq_msb_b
                    exact zero_ne_one w_eq_msb_b
                  by_cases rz : HWord.toInt_poly #v[r0, r1] = 0
                  · left; exact rz
                  · right
                    rw [HWord.sign_cases_poly is_U32_bl, HWord.sign_cases_poly is_U32_rl]
                    unfold HWord.isNegative_poly
                    simp only [Vector.getElem_mk, List.getElem_toArray,
                               List.getElem_cons_zero, List.getElem_cons_succ]
                    rw [if_neg (show ¬ r1.val ≥ 32768 from by omega),
                        if_neg (show ¬ b1.val ≥ 32768 from by omega)]
                    -- Goal: (if b.toInt = 0 then 0 else 1) = (if r.toInt = 0 then 0 else 1)
                    have rpos : HWord.toInt_poly #v[r0, r1] > 0 := by
                      have rnneg : 0 ≤ HWord.toInt_poly #v[r0, r1] := by
                        unfold HWord.toInt_poly HWord.isNegative_poly HWord.toNat_poly
                        simp only [Vector.getElem_mk, List.getElem_toArray,
                                   List.getElem_cons_zero, List.getElem_cons_succ]
                        rw [if_neg (show ¬ r1.val ≥ 32768 from by omega)]
                        positivity
                      omega
                    split_ifs with hb <;> try omega
                    -- Remaining case: hb : b.toInt = 0, hr : r.toInt ≠ 0
                    exfalso
                    rw [h_prod] at hb
                    set q := HWord.toInt_poly #v[q0, q1]
                    set c := HWord.toInt_poly #v[c0, c1]
                    set r := HWord.toInt_poly #v[r0, r1]
                    clear *- rpos h_abs hb
                    simp [Int.abs_cases] at h_abs
                    rw [if_pos (by omega)] at h_abs
                    apply Int.split_nzp q <;> intro hq <;> [skip; simp_all; skip]
                    all_goals
                      have : c * q > r := by split_ifs at * <;> nlinarith
                      nlinarith
                · -- msb_b = 1
                  have h_sgn_b : (HWord.toInt_poly #v[b0, b1]).sign = -1 :=
                    sgn_msb_b b_msb_neg
                  rcases b_rem_neg with rem_nneg | rem_neg
                  · -- msb_rem = 0: r2 = r3 = 0, so r_pos_b_pos collapses to r0 + r1 = 0
                    left
                    have hp17 : 2 ^ 17 < p := Fact.out
                    -- w_eq_r2_w / w_eq_r3_w simplified to direct equations post `simp at *`
                    have hr2 : r2 = (0 : ZMod p) := by
                      rw [w_eq_r2_w, rem_nneg, zero_mul]
                    have hr3 : r3 = (0 : ZMod p) := by
                      rw [w_eq_r3_w, rem_nneg, zero_mul]
                    have hrz : r0 + r1 = (0 : ZMod p) := by
                      rcases r_pos_b_pos with h | h | h
                      · rw [hr2, hr3] at h; linear_combination h
                      · exfalso; rw [rem_nneg] at h; exact zero_ne_one h
                      · exfalso; rw [b_msb_neg] at h; exact one_ne_zero h
                    have hsum_val : r0.val + r1.val = 0 := by
                      have hadd : (r0 + r1 : ZMod p).val = r0.val + r1.val :=
                        ZMod.val_add_of_lt (by omega)
                      rw [hrz, ZMod.val_zero] at hadd
                      omega
                    have hr0v : r0.val = 0 := by omega
                    have hr1v : r1.val = 0 := by omega
                    have hr1_lt : ¬ (32768 : ZMod p) ≤ r1 := by
                      intro h
                      have : (32768 : ZMod p).val ≤ r1.val := h
                      rw [val_32768_zmod_p] at this; omega
                    simp [HWord.toInt_poly, HWord.isNegative_poly, HWord.toNat_poly,
                          hr0v, hr1v]
                  · -- msb_rem = 1: use sgn_msb_rem
                    right
                    rw [sgn_msb_rem rem_neg, h_sgn_b]
              rw [tdiv_tmod_unique_full cnz]
              split_ands <;> assumption

-- Signed-32-bit variant: `.DRWS` op, threads through `divw_remw_poly`
-- (HWord signed core).
set_option maxHeartbeats 32000000 in
-- DRWS sign-extension multiplies the per-side constraint expansion by an
-- extra msb case-split (b/c/r/q), exceeding the default heartbeat budget.
set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
lemma spec.divw_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 246) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real_poly Main → is_divw_poly Main →
      Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] =
      (execute_DIV_REM_pure
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
        (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRWS).1
  := by
  intro cstrs h_is_real h_is_divw
  have ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op_poly Main cstrs
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff_poly Main).mp cstrs; simp at h_is_real
  simp [is_divw_poly] at h_is_divw
  set a0 := Main[28]
  set a1 := Main[29]
  set a2 := Main[30]
  set a3 := Main[31]
  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]
  set c0 := Main[22]
  set c1 := Main[23]
  set c2 := Main[24]
  set c3 := Main[25]
  set lb0 := Main[32]
  set lb1 := Main[33]
  set lb2 := Main[34]
  set lb3 := Main[35]
  set lc0 := Main[36]
  set lc1 := Main[37]
  set lc2 := Main[38]
  set lc3 := Main[39]
  set q0 := Main[40]
  set q1 := Main[41]
  set q2 := Main[42]
  set q3 := Main[43]
  set qbc0 := Main[44]
  set qbc1 := Main[45]
  set qbc2 := Main[46]
  set qbc3 := Main[47]
  set rbc0 := Main[48]
  set rbc1 := Main[49]
  set rbc2 := Main[50]
  set rbc3 := Main[51]
  set r0 := Main[52]
  set r1 := Main[53]
  set r2 := Main[54]
  set r3 := Main[55]
  set ar0 := Main[56]
  set ar1 := Main[57]
  set ar2 := Main[58]
  set ar3 := Main[59]
  set ac0 := Main[60]
  set ac1 := Main[61]
  set ac2 := Main[62]
  set ac3 := Main[63]
  set maco10 := Main[64]
  set maco11 := Main[65]
  set maco12 := Main[66]
  set maco13 := Main[67]
  set ctq0 := Main[68]
  set ctq1 := Main[69]
  set ctq2 := Main[70]
  set ctq3 := Main[71]
  set ctq4 := Main[72]
  set ctq5 := Main[73]
  set ctq6 := Main[74]
  set ctq7 := Main[75]
  set cnop0 := Main[166]
  set cnop1 := Main[167]
  set cnop2 := Main[168]
  set cnop3 := Main[169]
  set rnop0 := Main[170]
  set rnop1 := Main[171]
  set rnop2 := Main[172]
  set rnop3 := Main[173]
  set arlt := Main[174]
  set cry0 := Main[182]
  set cry1 := Main[183]
  set cry2 := Main[184]
  set cry3 := Main[185]
  set cry4 := Main[186]
  set cry5 := Main[187]
  set cry6 := Main[188]
  set cry7 := Main[189]
  set is_c_0 := Main[200]
  set is_div := Main[201]
  set is_divu := Main[202]
  set is_rem := Main[203]
  set is_remu := Main[204]
  set is_divw := Main[205]
  set is_remw := Main[206]
  set is_divuw := Main[207]
  set is_remuw := Main[208]
  set is_overflow := Main[209]
  set is_overflow_b := Main[220]
  set is_overflow_c := Main[231]
  set msb_b := Main[232]
  set msb_rem := Main[233]
  set msb_c := Main[234]
  set msb_quot := Main[235]
  set b_neg := Main[236]
  set b_neg_not_overflow := Main[237]
  set b_not_neg_not_overflow := Main[238]
  set is_real_not_word := Main[239]
  set rem_neg := Main[240]
  set c_neg := Main[241]
  set abs_c_alu_event := Main[242]
  set abs_rem_alu_event := Main[243]
  set is_real := Main[244]
  set remainder_check_multiplicity := Main[245]
  obtain ⟨main_mul_low, main_mul_high,
           overflow_b, overflow_c, w_overflow_b, w_overflow_c,
           div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
           eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
           cpu, alu,
           eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
           eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2,
           w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2,
           w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3,
           u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
           rest2⟩ := cstrs
  obtain ⟨eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
           r_neg_b_neg, r_pos_b_pos,
           c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
           cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
           u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
           u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
           eq_abs_c_alu_event, eq_abs_rem_alu_event,
           eq_maco10, eq_maco11, eq_maco12, eq_maco13,
           eq_rcm, eq_arlt,
           rest3⟩ := rest2
  obtain ⟨u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
           b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3,
           u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg,
           b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real,
           b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops, h_op_a_0⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))]
    at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_divw]
  apply MulOperation.spec.mul_poly at main_mul_low
  apply MulOperation.spec.mulh.gen_poly at main_mul_high
  apply IsEqualWordOperation.spec.gen_poly at overflow_b
  apply IsEqualWordOperation.spec.gen_poly at overflow_c
  apply IsEqualWordOperation.spec.gen_poly at w_overflow_b
  apply IsEqualWordOperation.spec.gen_poly at w_overflow_c
  apply IsZeroWordOperation.spec_poly at div_zero
  apply U16MSBOperation.spec.gen_poly at eq_msb_b
  apply U16MSBOperation.spec.gen_poly at eq_msb_c
  apply U16MSBOperation.spec.gen_poly at eq_msb_rem
  apply U16MSBOperation.spec.gen_poly at w_eq_msb_b
  apply U16MSBOperation.spec.gen_poly at w_eq_msb_c
  apply U16MSBOperation.spec.gen_poly at w_eq_msb_rem
  apply U16MSBOperation.spec.gen_poly at w_eq_msb_quot
  apply AddOperation.spec.gen_poly at c_neg_sum_zero
  apply AddOperation.spec.gen_poly at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen_poly at abs_check
  simp [-Vector.eq_mk, -Vector.mk_eq, -Vector.mk.injEq]
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c
       div_zero eq_msb_b eq_msb_c eq_msb_rem
       w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check
  have msb_bridge_eq : ∀ (a : ZMod p),
      ((32768 : ZMod p) ≤ a) = (a.val ≥ 32768) := by
    intro a; apply propext
    change (32768 : ZMod p).val ≤ a.val ↔ _
    rw [val_32768_zmod_p]
  simp only [← msb_bridge_eq] at eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by
    subst is_word; rfl
  have := divw_remw_poly a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3
    q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3
    ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7
    cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7
    is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow
    is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow
    b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event
    is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8
    eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1
    (by exact_mod_cast eq_lb2) (by exact_mod_cast eq_lc2)
    (by exact_mod_cast eq_lb3) (by exact_mod_cast eq_lc3)
    eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2
    w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3
    eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2
    w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this (by exact_mod_cast eq_b_neg_not_overflow)
    (by exact_mod_cast eq_not_b_neg_not_overflow)
    of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3
    nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
    nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
    u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3
    u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7
    eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3
    r_neg_b_neg r_pos_b_pos
    c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3
    cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3
    u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3
    u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3
    eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by
    clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by
    rcases b_is_real_not_word with h | h <;>
      first
        | (left; linear_combination h)
        | (right; linear_combination h)
        | (left; linear_combination -h)
        | (right; linear_combination -h)
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3
    b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7
    u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7
    b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw
    b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow
    b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero
    main_mul_low main_mul_high overflow_b overflow_c
    eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check
  all_goals
    obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := sop5 h_is_divw
    -- For divw, is_divw + is_remw = 1 ≠ 0; resolve_left peels the RHS of
    -- the w_eq_*_w disjunctions: rbc/qbc = msb_? * 65535.
    have h_sum_w_ne : (is_divw + is_remw : ZMod p) ≠ 0 := by
      intro hh
      have : (1 : ZMod p) = 0 := by linear_combination hh - h_is_divw - z4
      exact one_ne_zero this
    have h_rbc2_eq : rbc2 = msb_rem * 65535 := w_eq_rbc2_w.resolve_left h_sum_w_ne
    have h_rbc3_eq : rbc3 = msb_rem * 65535 := w_eq_rbc3_w.resolve_left h_sum_w_ne
    have h_qbc2_eq : qbc2 = msb_quot * 65535 := w_eq_qbc2_w.resolve_left h_sum_w_ne
    have h_qbc3_eq : qbc3 = msb_quot * 65535 := w_eq_qbc3_w.resolve_left h_sum_w_ne
    -- is_word = is_divw + is_remw + is_divuw + is_remuw = 1 for divw.
    have h_iw_1 : (is_divw + is_remw + is_divuw + is_remuw : ZMod p) = 1 := by
      linear_combination h_is_divw + z4 + z5 + z6
    -- msb_rem, msb_quot ∈ {0, 1}. The hypothesis form varies across side-goals
    -- (per the 3-form blocker documented in commit a62938b):
    --   (a) post-gen_poly + post-msb_bridge: `is_word = 1 → ?cols.msb = if 32768 ≤ ?x then 1 else 0`
    --   (b) post-gen_poly only: same but `if ?x.val ≥ 32768`
    --   (c) raw `List.Forall SP1Constraint.toProp (U16MSBOperation.constraints ...)`
    have h_msb_rem_01 : msb_rem = 0 ∨ msb_rem = 1 := by
      first
        | (have h : msb_rem = if (32768 : ZMod p) ≤ r1 then 1 else 0 := w_eq_msb_rem h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_rem = if r1.val ≥ 32768 then 1 else 0 := w_eq_msb_rem h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_rem = if r1.val ≥ 32768 then 1 else 0 :=
             U16MSBOperation.spec.gen_poly u16_r1 w_eq_msb_rem h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
    have h_msb_quot_01 : msb_quot = 0 ∨ msb_quot = 1 := by
      first
        | (have h : msb_quot = if (32768 : ZMod p) ≤ q1 then 1 else 0 := w_eq_msb_quot h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_quot = if q1.val ≥ 32768 then 1 else 0 := w_eq_msb_quot h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_quot = if q1.val ≥ 32768 then 1 else 0 :=
             U16MSBOperation.spec.gen_poly u16_q1 w_eq_msb_quot h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
    -- msb_b, msb_c also need bounds — Word.isU64_poly arms for the
    -- sign-extended b- and c-words have shape `[?, ?, msb_? * 65535, msb_? * 65535]`.
    have ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64_poly is_U64_b
    have ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64_poly is_U64_c
    have h_msb_b_01 : msb_b = 0 ∨ msb_b = 1 := by
      first
        | (have h : msb_b = if (32768 : ZMod p) ≤ b1 then 1 else 0 := w_eq_msb_b h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_b = if b1.val ≥ 32768 then 1 else 0 := w_eq_msb_b h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_b = if b1.val ≥ 32768 then 1 else 0 :=
             U16MSBOperation.spec.gen_poly hb1 w_eq_msb_b h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
    have h_msb_c_01 : msb_c = 0 ∨ msb_c = 1 := by
      first
        | (have h : msb_c = if (32768 : ZMod p) ≤ c1 then 1 else 0 := w_eq_msb_c h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_c = if c1.val ≥ 32768 then 1 else 0 := w_eq_msb_c h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_c = if c1.val ≥ 32768 then 1 else 0 :=
             U16MSBOperation.spec.gen_poly hc1 w_eq_msb_c h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
    simp [h_is_divw, z0, z1, z2, z3, z4, z5, z6,
          h_rbc2_eq, h_rbc3_eq, h_qbc2_eq, h_qbc3_eq] at *
  all_goals first
    | (rw [← this, eq_d_a0, eq_d_a1, eq_d_a2, eq_d_a3])
    | omega
    | (apply Word.isU64_of_cases_poly <;> simp_all; done)
    | (apply Word.isU64_of_cases_poly <;> simp <;> omega)
    | (apply Word.lt_cases_of_isU64_poly at is_U64_c; simp at is_U64_c; omega)
    | (apply Word.lt_cases_of_isU64_poly at is_U64_b; simp at is_U64_b; omega)
    | (apply Word.lt_cases_of_isU64_poly at is_U64_c
       apply Word.isU64_of_cases_poly <;> simp at is_U64_c ⊢ <;> omega)
    | (apply Word.lt_cases_of_isU64_poly at is_U64_b
       apply Word.isU64_of_cases_poly <;> simp at is_U64_b ⊢ <;> omega)
    | (rcases b_b_neg with hbn | hbn <;>
       (apply Word.isU64_of_cases_poly <;> simp_all [hbn] <;> omega))
    | (apply maco_arm_closer_poly u16_ac0 u16_ac1 u16_ac2 u16_ac3
        (by split_ifs at div_zero
            · right; exact div_zero
            · left; exact div_zero))
    -- msb-bearing arms: Word.isU64_poly goals for sign-extended r/q/c words
    -- have shape `#v[?, ?, m * 65535, m * 65535]` where m ∈ {0, 1}.
    -- `msb_arm_closer_poly` closes each shape directly given the low-limb
    -- u16 bounds (from `u16_r0`/`u16_q0` directly, or from `is_U64_c`).
    -- (b-side msb arm not needed for `divw` writeback — kept derived for parity.)
    | (apply msb_arm_closer_poly u16_r0 u16_r1 h_msb_rem_01)
    | (apply msb_arm_closer_poly u16_q0 u16_q1 h_msb_quot_01)
    | (apply msb_arm_closer_poly hc0 hc1 h_msb_c_01)

-- Twin of `spec.divw_poly` with `.2` projection, `is_remw_poly` flag,
-- `sop6` mutex, `eq_r_*` writeback.
set_option maxHeartbeats 32000000 in
-- DRWS sign-extension multiplies the per-side constraint expansion by an
-- extra msb case-split (b/c/r/q), exceeding the default heartbeat budget.
set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
lemma spec.remw_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 246) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real_poly Main → is_remw_poly Main →
      Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] =
      (execute_DIV_REM_pure
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
        (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRWS).2
  := by
  intro cstrs h_is_real h_is_remw
  have ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op_poly Main cstrs
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff_poly Main).mp cstrs; simp at h_is_real
  simp [is_remw_poly] at h_is_remw
  set a0 := Main[28]
  set a1 := Main[29]
  set a2 := Main[30]
  set a3 := Main[31]
  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]
  set c0 := Main[22]
  set c1 := Main[23]
  set c2 := Main[24]
  set c3 := Main[25]
  set lb0 := Main[32]
  set lb1 := Main[33]
  set lb2 := Main[34]
  set lb3 := Main[35]
  set lc0 := Main[36]
  set lc1 := Main[37]
  set lc2 := Main[38]
  set lc3 := Main[39]
  set q0 := Main[40]
  set q1 := Main[41]
  set q2 := Main[42]
  set q3 := Main[43]
  set qbc0 := Main[44]
  set qbc1 := Main[45]
  set qbc2 := Main[46]
  set qbc3 := Main[47]
  set rbc0 := Main[48]
  set rbc1 := Main[49]
  set rbc2 := Main[50]
  set rbc3 := Main[51]
  set r0 := Main[52]
  set r1 := Main[53]
  set r2 := Main[54]
  set r3 := Main[55]
  set ar0 := Main[56]
  set ar1 := Main[57]
  set ar2 := Main[58]
  set ar3 := Main[59]
  set ac0 := Main[60]
  set ac1 := Main[61]
  set ac2 := Main[62]
  set ac3 := Main[63]
  set maco10 := Main[64]
  set maco11 := Main[65]
  set maco12 := Main[66]
  set maco13 := Main[67]
  set ctq0 := Main[68]
  set ctq1 := Main[69]
  set ctq2 := Main[70]
  set ctq3 := Main[71]
  set ctq4 := Main[72]
  set ctq5 := Main[73]
  set ctq6 := Main[74]
  set ctq7 := Main[75]
  set cnop0 := Main[166]
  set cnop1 := Main[167]
  set cnop2 := Main[168]
  set cnop3 := Main[169]
  set rnop0 := Main[170]
  set rnop1 := Main[171]
  set rnop2 := Main[172]
  set rnop3 := Main[173]
  set arlt := Main[174]
  set cry0 := Main[182]
  set cry1 := Main[183]
  set cry2 := Main[184]
  set cry3 := Main[185]
  set cry4 := Main[186]
  set cry5 := Main[187]
  set cry6 := Main[188]
  set cry7 := Main[189]
  set is_c_0 := Main[200]
  set is_div := Main[201]
  set is_divu := Main[202]
  set is_rem := Main[203]
  set is_remu := Main[204]
  set is_divw := Main[205]
  set is_remw := Main[206]
  set is_divuw := Main[207]
  set is_remuw := Main[208]
  set is_overflow := Main[209]
  set is_overflow_b := Main[220]
  set is_overflow_c := Main[231]
  set msb_b := Main[232]
  set msb_rem := Main[233]
  set msb_c := Main[234]
  set msb_quot := Main[235]
  set b_neg := Main[236]
  set b_neg_not_overflow := Main[237]
  set b_not_neg_not_overflow := Main[238]
  set is_real_not_word := Main[239]
  set rem_neg := Main[240]
  set c_neg := Main[241]
  set abs_c_alu_event := Main[242]
  set abs_rem_alu_event := Main[243]
  set is_real := Main[244]
  set remainder_check_multiplicity := Main[245]
  obtain ⟨main_mul_low, main_mul_high,
           overflow_b, overflow_c, w_overflow_b, w_overflow_c,
           div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
           eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
           cpu, alu,
           eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
           eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2,
           w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2,
           w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3,
           u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
           rest2⟩ := cstrs
  obtain ⟨eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
           r_neg_b_neg, r_pos_b_pos,
           c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
           cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
           u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
           u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
           eq_abs_c_alu_event, eq_abs_rem_alu_event,
           eq_maco10, eq_maco11, eq_maco12, eq_maco13,
           eq_rcm, eq_arlt,
           rest3⟩ := rest2
  obtain ⟨u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
           b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3,
           u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg,
           b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real,
           b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops, h_op_a_0⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))]
    at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_remw]
  apply MulOperation.spec.mul_poly at main_mul_low
  apply MulOperation.spec.mulh.gen_poly at main_mul_high
  apply IsEqualWordOperation.spec.gen_poly at overflow_b
  apply IsEqualWordOperation.spec.gen_poly at overflow_c
  apply IsEqualWordOperation.spec.gen_poly at w_overflow_b
  apply IsEqualWordOperation.spec.gen_poly at w_overflow_c
  apply IsZeroWordOperation.spec_poly at div_zero
  apply U16MSBOperation.spec.gen_poly at eq_msb_b
  apply U16MSBOperation.spec.gen_poly at eq_msb_c
  apply U16MSBOperation.spec.gen_poly at eq_msb_rem
  apply U16MSBOperation.spec.gen_poly at w_eq_msb_b
  apply U16MSBOperation.spec.gen_poly at w_eq_msb_c
  apply U16MSBOperation.spec.gen_poly at w_eq_msb_rem
  apply U16MSBOperation.spec.gen_poly at w_eq_msb_quot
  apply AddOperation.spec.gen_poly at c_neg_sum_zero
  apply AddOperation.spec.gen_poly at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen_poly at abs_check
  simp [-Vector.eq_mk, -Vector.mk_eq, -Vector.mk.injEq]
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c
       div_zero eq_msb_b eq_msb_c eq_msb_rem
       w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check
  have msb_bridge_eq : ∀ (a : ZMod p),
      ((32768 : ZMod p) ≤ a) = (a.val ≥ 32768) := by
    intro a; apply propext
    change (32768 : ZMod p).val ≤ a.val ↔ _
    rw [val_32768_zmod_p]
  simp only [← msb_bridge_eq] at eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by
    subst is_word; rfl
  have := divw_remw_poly a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3
    q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3
    ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7
    cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7
    is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow
    is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow
    b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event
    is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8
    eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1
    (by exact_mod_cast eq_lb2) (by exact_mod_cast eq_lc2)
    (by exact_mod_cast eq_lb3) (by exact_mod_cast eq_lc3)
    eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2
    w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3
    eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2
    w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this (by exact_mod_cast eq_b_neg_not_overflow)
    (by exact_mod_cast eq_not_b_neg_not_overflow)
    of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3
    nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
    nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
    u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3
    u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7
    eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3
    r_neg_b_neg r_pos_b_pos
    c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3
    cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3
    u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3
    u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3
    eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by
    clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by
    rcases b_is_real_not_word with h | h <;>
      first
        | (left; linear_combination h)
        | (right; linear_combination h)
        | (left; linear_combination -h)
        | (right; linear_combination -h)
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3
    b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7
    u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7
    b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw
    b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow
    b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero
    main_mul_low main_mul_high overflow_b overflow_c
    eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check
  all_goals
    obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := sop6 h_is_remw
    -- For remw, is_divw + is_remw = 1 ≠ 0; resolve_left peels the w_eq_*_w
    -- disjunctions to rbc/qbc = msb_? * 65535. Mirrors spec.divw_poly.
    -- sop6 z* order: z0=is_div, z1=is_divu, z2=is_rem, z3=is_remu, z4=is_divw,
    -- z5=is_divuw, z6=is_remuw (all 0). h_is_remw : is_remw = 1.
    have h_sum_w_ne : (is_divw + is_remw : ZMod p) ≠ 0 := by
      intro hh
      have : (1 : ZMod p) = 0 := by linear_combination hh - h_is_remw - z4
      exact one_ne_zero this
    have h_rbc2_eq : rbc2 = msb_rem * 65535 := w_eq_rbc2_w.resolve_left h_sum_w_ne
    have h_rbc3_eq : rbc3 = msb_rem * 65535 := w_eq_rbc3_w.resolve_left h_sum_w_ne
    have h_qbc2_eq : qbc2 = msb_quot * 65535 := w_eq_qbc2_w.resolve_left h_sum_w_ne
    have h_qbc3_eq : qbc3 = msb_quot * 65535 := w_eq_qbc3_w.resolve_left h_sum_w_ne
    have h_iw_1 : (is_divw + is_remw + is_divuw + is_remuw : ZMod p) = 1 := by
      linear_combination h_is_remw + z4 + z5 + z6
    have h_msb_rem_01 : msb_rem = 0 ∨ msb_rem = 1 := by
      first
        | (have h : msb_rem = if (32768 : ZMod p) ≤ r1 then 1 else 0 := w_eq_msb_rem h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_rem = if r1.val ≥ 32768 then 1 else 0 := w_eq_msb_rem h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_rem = if r1.val ≥ 32768 then 1 else 0 :=
             U16MSBOperation.spec.gen_poly u16_r1 w_eq_msb_rem h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
    have h_msb_quot_01 : msb_quot = 0 ∨ msb_quot = 1 := by
      first
        | (have h : msb_quot = if (32768 : ZMod p) ≤ q1 then 1 else 0 := w_eq_msb_quot h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_quot = if q1.val ≥ 32768 then 1 else 0 := w_eq_msb_quot h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_quot = if q1.val ≥ 32768 then 1 else 0 :=
             U16MSBOperation.spec.gen_poly u16_q1 w_eq_msb_quot h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
    have ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64_poly is_U64_b
    have ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64_poly is_U64_c
    have h_msb_b_01 : msb_b = 0 ∨ msb_b = 1 := by
      first
        | (have h : msb_b = if (32768 : ZMod p) ≤ b1 then 1 else 0 := w_eq_msb_b h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_b = if b1.val ≥ 32768 then 1 else 0 := w_eq_msb_b h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_b = if b1.val ≥ 32768 then 1 else 0 :=
             U16MSBOperation.spec.gen_poly hb1 w_eq_msb_b h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
    have h_msb_c_01 : msb_c = 0 ∨ msb_c = 1 := by
      first
        | (have h : msb_c = if (32768 : ZMod p) ≤ c1 then 1 else 0 := w_eq_msb_c h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_c = if c1.val ≥ 32768 then 1 else 0 := w_eq_msb_c h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
        | (have h : msb_c = if c1.val ≥ 32768 then 1 else 0 :=
             U16MSBOperation.spec.gen_poly hc1 w_eq_msb_c h_iw_1
           rw [h]; split_ifs <;> [right; left] <;> rfl)
    simp [h_is_remw, z0, z1, z2, z3, z4, z5, z6,
          h_rbc2_eq, h_rbc3_eq, h_qbc2_eq, h_qbc3_eq] at *
  all_goals first
    | (rw [← this, eq_r_a0, eq_r_a1, eq_r_a2, eq_r_a3])
    | omega
    | (apply Word.isU64_of_cases_poly <;> simp_all; done)
    | (apply Word.isU64_of_cases_poly <;> simp <;> omega)
    | (apply Word.lt_cases_of_isU64_poly at is_U64_c; simp at is_U64_c; omega)
    | (apply Word.lt_cases_of_isU64_poly at is_U64_b; simp at is_U64_b; omega)
    | (apply Word.lt_cases_of_isU64_poly at is_U64_c
       apply Word.isU64_of_cases_poly <;> simp at is_U64_c ⊢ <;> omega)
    | (apply Word.lt_cases_of_isU64_poly at is_U64_b
       apply Word.isU64_of_cases_poly <;> simp at is_U64_b ⊢ <;> omega)
    | (rcases b_b_neg with hbn | hbn <;>
       (apply Word.isU64_of_cases_poly <;> simp_all [hbn] <;> omega))
    | (apply maco_arm_closer_poly u16_ac0 u16_ac1 u16_ac2 u16_ac3
        (by split_ifs at div_zero
            · right; exact div_zero
            · left; exact div_zero))
    -- msb-bearing arms (see spec.divw_poly for shape rationale).
    | (apply msb_arm_closer_poly u16_r0 u16_r1 h_msb_rem_01)
    | (apply msb_arm_closer_poly u16_q0 u16_q1 h_msb_quot_01)
    | (apply msb_arm_closer_poly hc0 hc1 h_msb_c_01)

end divw_remw

end DivRem
