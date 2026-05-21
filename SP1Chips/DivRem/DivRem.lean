import SP1Chips.DivRem.AbsHelper

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

section div_rem

set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
-- 32M heartbeats: signed 64-bit core needs h_sign witness plus the residual
-- close-step (mirrors `divw_remw` recipe at HWord width). The two heavy
-- witnesses — `h_prod`'s `2^128`-walking body and `h_abs`'s 4-way rem_neg × c_neg
-- case-split body — are extracted into `div_rem_h_prod_aux` and `div_rem_h_abs_aux`
-- in `Common.lean`. The h_abs helper retains `skipKernelTC` on its own decl
-- (its body alone is still too deep for the kernel's WHNF reduction limit), but
-- with that escape localized there, the chip's own kernel walk stays bounded
-- and `div_rem` no longer needs the escape.
lemma div_rem {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
  (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event : ZMod p)
  (is_U64_b : Word.isU64 #v[b0, b1, b2, b3])
  (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
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
  (c_neg_sum_zero : c_neg = 1 → Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧ Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] = Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] + Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
  (rem_neg_sum_zero : rem_neg = 1 → Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧ Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] = Word.toBitVec64 #v[r0, r1, rbc2, rbc3] + Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
  (main_mul_low : Word.isU64 #v[ctq0, ctq1, ctq2, ctq3] ∧ Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MUL)
  (main_mul_high : is_word = 0 → (is_div + is_rem = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULH) ∧ (is_divu + is_remu = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULHU))
  (overflow_b : is_word = 0 → is_overflow_b = if #v[b0, b1, b2, b3] = (#v[0, 0, 0, 32768] : Word (ZMod p)) then 1 else 0)
  (overflow_c : is_word = 0 → is_overflow_c = if #v[c0, c1, c2, c3] = (#v[65535, 65535, 65535, 65535] : Word (ZMod p)) then 1 else 0)
  (eq_msb_b : is_word = 0 → msb_b = if 32768 ≤ b3 then 1 else 0)
  (eq_msb_c : is_word = 0 → msb_c = if 32768 ≤ c3 then 1 else 0)
  (eq_msb_rem : is_word = 0 → msb_rem = if 32768 ≤ r3 then 1 else 0)
  (w_eq_msb_b : is_word = 1 → msb_b = if 32768 ≤ b1 then 1 else 0)
  (w_eq_msb_c : is_word = 1 → msb_c = if 32768 ≤ c1 then 1 else 0)
  (w_eq_msb_rem : is_word = 1 → msb_rem = if 32768 ≤ r1 then 1 else 0)
  (w_eq_msb_quot : is_word = 1 → msb_quot = if 32768 ≤ q1 then 1 else 0)
  (abs_check : is_c_0 = 0 → arlt = if Word.toNat #v[ar0, ar1, ar2, ar3] < Word.toNat #v[is_c_0 + (1 - is_c_0) * ac0, (1 - is_c_0) * ac1, (1 - is_c_0) * ac2, (1 - is_c_0) * ac3] then 1 else 0) :
    is_div + is_rem = 1 →
    ⟨Word.toBitVec64 #v[q0, q1, q2, q3], Word.toBitVec64 #v[r0, r1, r2, r3]⟩ = execute_DIV_REM_pure (Word.toBitVec64 #v[b0, b1, b2, b3]) (Word.toBitVec64 #v[c0, c1, c2, c3]) .DRS
      := by
    haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
    have h17 : 2 ^ 17 < p := Fact.out
    have h24 : 2 ^ 24 < p := Fact.out
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
    have hcv4 : cry4.val ≤ 1 := by rcases b_cry4 with h | h <;> rw [h] <;> simp [h0v, h1v]
    have hcv5 : cry5.val ≤ 1 := by rcases b_cry5 with h | h <;> rw [h] <;> simp [h0v, h1v]
    have hcv6 : cry6.val ≤ 1 := by rcases b_cry6 with h | h <;> rw [h] <;> simp [h0v, h1v]
    have hcv7 : cry7.val ≤ 1 := by rcases b_cry7 with h | h <;> rw [h] <;> simp [h0v, h1v]
    intro div_rem
    obtain ⟨z_divu, z_remu, z_divw, z_remw, z_divuw, z_remuw⟩ :
        is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0 := by
      clear *- div_rem sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8
                       b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw
                       b_one_of_ops h01 h21
      rcases b_is_div with h_d | h_d <;> rcases b_is_rem with h_r | h_r
      · exfalso; rw [h_d, h_r, zero_add] at div_rem; exact h01 div_rem.symm
      · -- (0,1): is_div=0, is_rem=1; use sop3
        -- sop3 : is_div = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0
        have := sop3 h_r
        exact ⟨this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩
      · -- (1,0): is_div=1, is_rem=0; use sop1
        -- sop1 : is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0
        have := sop1 h_d
        exact ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩
      · exfalso
        rw [h_d, h_r] at div_rem
        have : (1 + 1 : ZMod p) = 2 := by ring
        rw [this] at div_rem; exact h21 div_rem
    simp [z_divu, z_remu, z_divw, z_remw, z_divuw, z_remuw, div_rem] at *
    simp [eq_is_word] at *
    subst lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3
    subst abs_c_alu_event abs_rem_alu_event b_neg rem_neg c_neg
    have h65535_ne : (65535 : ZMod p) ≠ 0 := by
      intro h; have := congrArg ZMod.val h
      rw [h65535_val, ZMod.val_zero] at this; omega
    simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, Bool.cond_eq_ite]
    rw [Word.toBitVec64_toInt is_U64_b, Word.toBitVec64_toInt is_U64_c]
    split_ifs at div_zero with nzc <;> simp [div_zero] at *
    · -- c = 0 branch: c0 = c1 = c2 = c3 = 0 → q = #v[65535×4] = -1#64, r = b
      obtain ⟨zc0, zc1, zc2, zc3⟩ := nzc
      simp [zc0, zc1, zc2, zc3] at *
      have hzero_int : Word.toInt (#v[(0 : ZMod p), 0, 0, 0] : Word (ZMod p)) = 0 := by
        simp [Word.toInt, Word.isNegative, Word.toNat, h0v]
      simp [hzero_int, c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3,
            c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3]
      refine ⟨?_, ?_⟩
      · -- q side: Word.toBitVec64 #v[65535, 65535, 65535, 65535] = -1#64
        simp [Word.toBitVec64, Word.toNat, h65535_val]
      · -- r side: Word.toBitVec64 b = BitVec.ofInt 64 (Word.toInt b)
        have lb_b := Word.toInt_lb is_U64_b
        have ub_b := Word.toInt_ub is_U64_b
        simp only [← BitVec.toInt_inj]
        rw [Word.toBitVec64_toInt is_U64_b]
        rw [BitVec.toInt_ofInt]
        rw [Int.bmod_eq_of_le (by omega) (by omega)]
    · -- c ≠ 0 branch
      subst arlt maco10 maco11 maco12 maco13
      rw [if_neg]; rotate_left
      · intro zc
        apply nzc
        have hcs := Word.lt_cases_of_isU64 is_U64_c
        obtain ⟨hc0_lt, hc1_lt, hc2_lt, hc3_lt⟩ := hcs
        simp only [Vector.getElem_mk, List.getElem_toArray,
                   List.getElem_cons_zero, List.getElem_cons_succ] at hc0_lt hc1_lt hc2_lt hc3_lt
        unfold Word.toInt Word.toNat Word.isNegative at zc
        simp only [Vector.getElem_mk, List.getElem_toArray,
                   List.getElem_cons_zero, List.getElem_cons_succ] at zc
        split_ifs at zc with h_neg
        · exfalso
          push_cast at zc
          have h_max : (c0.val : ℤ) + (c1.val : ℤ) * 65536 +
              (c2.val : ℤ) * 4294967296 + (c3.val : ℤ) * 281474976710656 < 18446744073709551616 := by
            have hc0v_lt : (c0.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc0_lt
            have hc1v_lt : (c1.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc1_lt
            have hc2v_lt : (c2.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc2_lt
            have hc3v_lt : (c3.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc3_lt
            nlinarith
          linarith
        · push_cast at zc
          have hc0v : c0.val = 0 := by omega
          have hc1v : c1.val = 0 := by omega
          have hc2v : c2.val = 0 := by omega
          have hc3v : c3.val = 0 := by omega
          exact ⟨(ZMod.val_eq_zero c0).mp hc0v,
                 (ZMod.val_eq_zero c1).mp hc1v,
                 (ZMod.val_eq_zero c2).mp hc2v,
                 (ZMod.val_eq_zero c3).mp hc3v⟩
      · rcases b_is_overflow with nof | of; rotate_left
        · -- overflow branch
          simp [of] at *
          split_ifs at overflow_b with ofb <;> simp [overflow_b] at *
          split_ifs at overflow_c with ofc <;> simp [overflow_c] at *
          obtain ⟨eb0, eb1, eb2, eb3⟩ := ofb
          obtain ⟨ec0, ec1, ec2, ec3⟩ := ofc
          simp [of_eq_q0, of_eq_q1, of_eq_q2, of_eq_q3,
                of_eq_r0, of_eq_r1, of_eq_r2, of_eq_r3,
                eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3]
          simp only [Word.toBitVec64, Word.toInt, Word.isNegative, Word.toNat,
                     Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
                     List.getElem_cons_zero]
          simp [h0v, h32768_val, h65535_val]
        · -- non-overflow branch: main h_prod / h_abs / h_sign witness
          simp [nof] at *
          rw [if_neg]; rotate_left
          · intro ⟨h_eq_b, h_eq_c⟩
            have hbb : (#v[b0, b1, b2, b3] : Word (ZMod p)) = #v[0, 0, 0, 32768] := by
              rw [Word.eq_toInt_eq is_U64_b, h_eq_b]
              · simp [Word.toInt, Word.isNegative, Word.toNat,
                      h0v, h32768_val]
              · apply Word.isU64_of_cases <;> simp [h0v, h32768_val]
            simp at hbb
            rw [if_pos hbb] at overflow_b; simp [overflow_b] at *
            have hcc : (#v[c0, c1, c2, c3] : Word (ZMod p)) = #v[65535, 65535, 65535, 65535] := by
              rw [Word.eq_toInt_eq is_U64_c, h_eq_c]
              · simp [Word.toInt, Word.isNegative, Word.toNat,
                      h65535_val, h32768_val]
              · apply Word.isU64_of_cases <;> simp [h65535_val]
            simp at hcc
            rw [if_pos hcc] at overflow_c; simp [overflow_c] at *
          · have is_U64_r : Word.isU64 #v[r0, r1, r2, r3] := by
              apply Word.isU64_of_cases <;> simpa
            have is_U64_q : Word.isU64 #v[q0, q1, q2, q3] := by
              apply Word.isU64_of_cases <;> simpa
            have is_U64_ar : Word.isU64 #v[ar0, ar1, ar2, ar3] := by
              apply Word.isU64_of_cases <;> simpa
            have is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3] := by
              apply Word.isU64_of_cases <;> simpa
            have lb_b := Word.toInt_lb is_U64_b; have ub_b := Word.toInt_ub is_U64_b
            have lb_c := Word.toInt_lb is_U64_c; have ub_c := Word.toInt_ub is_U64_c
            have lb_q := Word.toInt_lb is_U64_q; have ub_q := Word.toInt_ub is_U64_q
            have lb_r := Word.toInt_lb is_U64_r; have ub_r := Word.toInt_ub is_U64_r
            suffices h_qr :
                Word.toInt #v[q0, q1, q2, q3] =
                  (Word.toInt #v[b0, b1, b2, b3]).tdiv (Word.toInt #v[c0, c1, c2, c3]) ∧
                Word.toInt #v[r0, r1, r2, r3] =
                  (Word.toInt #v[b0, b1, b2, b3]).tmod (Word.toInt #v[c0, c1, c2, c3]) by
              obtain ⟨hdiv, hrem⟩ := h_qr
              rw [← hdiv, ← hrem]
              simp [← BitVec.toInt_inj]
              rw [Word.toBitVec64_toInt is_U64_q,
                  Word.toBitVec64_toInt is_U64_r]
              iterate 2 rw [Int.bmod_eq_of_le (by omega) (by omega)]
              trivial
            -- Three witnesses for tdiv_tmod_unique_full: h_prod, h_abs, h_sign.
            have sgn_msb_b : msb_b = 1 → (Word.toInt #v[b0, b1, b2, b3]).sign = -1 := by
              intro h_msb_b
              have hb3 : b3.val ≥ 32768 := by
                rw [eq_msb_b] at h_msb_b
                split_ifs at h_msb_b with h
                · change (32768 : ZMod p).val ≤ b3.val at h
                  rwa [val_32768_zmod_p] at h
                · simp at h_msb_b
              rw [Word.sign_cases is_U64_b]
              rw [if_pos (by simp [Word.isNegative]; omega)]
            have sgn_msb_c : msb_c = 1 → (Word.toInt #v[c0, c1, c2, c3]).sign = -1 := by
              intro h_msb_c
              have hc3 : c3.val ≥ 32768 := by
                rw [eq_msb_c] at h_msb_c
                split_ifs at h_msb_c with h
                · change (32768 : ZMod p).val ≤ c3.val at h
                  rwa [val_32768_zmod_p] at h
                · simp at h_msb_c
              rw [Word.sign_cases is_U64_c]
              rw [if_pos (by simp [Word.isNegative]; omega)]
            have sgn_msb_rem : msb_rem = 1 → (Word.toInt #v[r0, r1, r2, r3]).sign = -1 := by
              intro h_msb_rem
              have hr3 : r3.val ≥ 32768 := by
                rw [eq_msb_rem] at h_msb_rem
                split_ifs at h_msb_rem with h
                · change (32768 : ZMod p).val ≤ r3.val at h
                  rwa [val_32768_zmod_p] at h
                · simp at h_msb_rem
              rw [Word.sign_cases is_U64_r]
              rw [if_pos (by simp [Word.isNegative]; omega)]
            have cnz : Word.toInt #v[c0, c1, c2, c3] ≠ 0 := by
              intro zc
              apply nzc
              have hcs := Word.lt_cases_of_isU64 is_U64_c
              obtain ⟨hc0_lt, hc1_lt, hc2_lt, hc3_lt⟩ := hcs
              simp only [Vector.getElem_mk, List.getElem_toArray,
                         List.getElem_cons_zero, List.getElem_cons_succ] at hc0_lt hc1_lt hc2_lt hc3_lt
              unfold Word.toInt Word.toNat Word.isNegative at zc
              simp only [Vector.getElem_mk, List.getElem_toArray,
                         List.getElem_cons_zero, List.getElem_cons_succ] at zc
              split_ifs at zc with h_neg
              · exfalso
                push_cast at zc
                have h_max : (c0.val : ℤ) + (c1.val : ℤ) * 65536 +
                    (c2.val : ℤ) * 4294967296 + (c3.val : ℤ) * 281474976710656 < 18446744073709551616 := by
                  have hc0v_lt : (c0.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc0_lt
                  have hc1v_lt : (c1.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc1_lt
                  have hc2v_lt : (c2.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc2_lt
                  have hc3v_lt : (c3.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp hc3_lt
                  nlinarith
                linarith
              · push_cast at zc
                have hc0v : c0.val = 0 := by omega
                have hc1v : c1.val = 0 := by omega
                have hc2v : c2.val = 0 := by omega
                have hc3v : c3.val = 0 := by omega
                exact ⟨(ZMod.val_eq_zero c0).mp hc0v,
                       (ZMod.val_eq_zero c1).mp hc1v,
                       (ZMod.val_eq_zero c2).mp hc2v,
                       (ZMod.val_eq_zero c3).mp hc3v⟩
            -- First condition: h_prod — extracted to `DivRem.div_rem_h_prod_aux`
            -- (Common.lean) so its `2^128`-walking proof body (signExtend chain +
            -- `simp at ctq` + DWord 128 limb simps) goes through its own kernel
            -- re-check independently of `div_rem`'s.
            have h_prod : Word.toInt #v[b0, b1, b2, b3] =
                Word.toInt #v[q0, q1, q2, q3] * Word.toInt #v[c0, c1, c2, c3] +
                Word.toInt #v[r0, r1, r2, r3] :=
              div_rem_h_prod_aux is_U64_b is_U64_c is_U64_q is_U64_r
                eq_msb_b eq_msb_rem
                b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7
                nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
                u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3
                u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7
                main_mul_low main_mul_high
            -- Second condition: h_abs — extracted to `DivRem.div_rem_h_abs_aux`
            -- (Common.lean) so its 4-way rem_neg × c_neg case body's heavy `simp at *`
            -- and `subst` chains live in their own olean. `skipKernelTC` is required
            -- on the helper itself (the body trips kernel reduction depth), but with
            -- `skipKernelTC` localized there, the chip no longer needs it.
            have h_abs : |Word.toInt #v[r0, r1, r2, r3]| <
                |Word.toInt #v[c0, c1, c2, c3]| :=
              div_rem_h_abs_aux is_U64_c is_U64_r is_U64_ac is_U64_ar
                b_rem_neg b_c_neg eq_msb_rem eq_msb_c
                rn_ar0 rn_ar1 rn_ar2 rn_ar3
                cn_ac0 cn_ac1 cn_ac2 cn_ac3
                eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3
                eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3
                c_neg_sum_zero rem_neg_sum_zero
                abs_check
            -- Third condition: h_sign — mirror of DivwRemw.lean:1206-1297 at Word width.
            have h_sign : Word.toInt #v[r0, r1, r2, r3] = 0 ∨
                (Word.toInt #v[r0, r1, r2, r3]).sign =
                  (Word.toInt #v[b0, b1, b2, b3]).sign := by
              rcases b_b_neg with b_msb_nneg | b_msb_neg
              · -- msb_b = 0: derive msb_rem = 0 from r_neg_b_neg, then split on whether r = 0.
                subst b_msb_nneg
                have hmsb_rem_0 : msb_rem = 0 := by
                  rcases r_neg_b_neg with h | h
                  · exact h
                  · exact absurd h zero_ne_one
                subst hmsb_rem_0
                have hr3_lt_val : r3.val < 32768 := by
                  by_contra h; push Not at h
                  have hge : (32768 : ZMod p) ≤ r3 := by
                    change (32768 : ZMod p).val ≤ r3.val
                    rw [val_32768_zmod_p]; exact h
                  rw [if_pos hge] at eq_msb_rem
                  exact zero_ne_one eq_msb_rem
                have hb3_lt_val : b3.val < 32768 := by
                  by_contra h; push Not at h
                  have hge : (32768 : ZMod p) ≤ b3 := by
                    change (32768 : ZMod p).val ≤ b3.val
                    rw [val_32768_zmod_p]; exact h
                  rw [if_pos hge] at eq_msb_b
                  exact zero_ne_one eq_msb_b
                by_cases rz : Word.toInt #v[r0, r1, r2, r3] = 0
                · left; exact rz
                · right
                  rw [Word.sign_cases is_U64_b, Word.sign_cases is_U64_r]
                  unfold Word.isNegative
                  simp only [Vector.getElem_mk, List.getElem_toArray,
                             List.getElem_cons_zero, List.getElem_cons_succ]
                  rw [if_neg (show ¬ r3.val ≥ 32768 from by omega),
                      if_neg (show ¬ b3.val ≥ 32768 from by omega)]
                  have rpos : Word.toInt #v[r0, r1, r2, r3] > 0 := by
                    have rnneg : 0 ≤ Word.toInt #v[r0, r1, r2, r3] := by
                      unfold Word.toInt Word.isNegative Word.toNat
                      simp only [Vector.getElem_mk, List.getElem_toArray,
                                 List.getElem_cons_zero, List.getElem_cons_succ]
                      rw [if_neg (show ¬ r3.val ≥ 32768 from by omega)]
                      positivity
                    omega
                  split_ifs with hb <;> try omega
                  exfalso
                  rw [h_prod] at hb
                  set q := Word.toInt #v[q0, q1, q2, q3]
                  set c := Word.toInt #v[c0, c1, c2, c3]
                  set r := Word.toInt #v[r0, r1, r2, r3]
                  clear *- rpos h_abs hb
                  simp [Int.abs_cases] at h_abs
                  rw [if_pos (by omega)] at h_abs
                  apply Int.split_nzp q <;> intro hq <;> [skip; simp_all; skip]
                  all_goals
                    have : c * q > r := by split_ifs at * <;> nlinarith
                    nlinarith
              · -- msb_b = 1: case-split on b_rem_neg.
                have h_sgn_b : (Word.toInt #v[b0, b1, b2, b3]).sign = -1 :=
                  sgn_msb_b b_msb_neg
                rcases b_rem_neg with rem_nneg | rem_neg
                · -- msb_rem = 0: r_pos_b_pos collapses to r0 + r1 + r2 + r3 = 0.
                  left
                  have hrz : r0 + r1 + r2 + r3 = (0 : ZMod p) := by
                    rcases r_pos_b_pos with h | h | h
                    · exact h
                    · exfalso; rw [rem_nneg] at h; exact zero_ne_one h
                    · exfalso; rw [b_msb_neg] at h; exact one_ne_zero h
                  -- 3-step `ZMod.val_add_of_lt` chain under `Fact (2^24 < p)`.
                  have hsum01 : (r0 + r1 : ZMod p).val = r0.val + r1.val :=
                    ZMod.val_add_of_lt (by omega)
                  have hsum012 : (r0 + r1 + r2 : ZMod p).val = (r0 + r1).val + r2.val :=
                    ZMod.val_add_of_lt (by rw [hsum01]; omega)
                  have hsum0123 : (r0 + r1 + r2 + r3 : ZMod p).val =
                      (r0 + r1 + r2).val + r3.val :=
                    ZMod.val_add_of_lt (by rw [hsum012, hsum01]; omega)
                  rw [hrz, ZMod.val_zero, hsum012, hsum01] at hsum0123
                  have hr0v : r0.val = 0 := by omega
                  have hr1v : r1.val = 0 := by omega
                  have hr2v : r2.val = 0 := by omega
                  have hr3v : r3.val = 0 := by omega
                  have hr3_lt : ¬ (32768 : ZMod p) ≤ r3 := by
                    intro h
                    have hh : (32768 : ZMod p).val ≤ r3.val := h
                    rw [val_32768_zmod_p] at hh; omega
                  simp [Word.toInt, Word.isNegative, Word.toNat,
                        hr0v, hr1v, hr2v, hr3v]
                · -- msb_rem = 1: use sgn_msb_rem.
                  right
                  rw [sgn_msb_rem rem_neg, h_sgn_b]
            rw [tdiv_tmod_unique_full cnz]
            split_ands <;> assumption

-- Signed-64-bit variant: `.DRS` op, threads through `div_rem`
-- (DWord 8-limb signed core).
set_option maxHeartbeats 32000000 in
-- .DRS 64-bit signed expansion produces a wide hypothesis pile after the
-- divw_remw specialize chain; the default heartbeat budget is exceeded.
set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
lemma spec.div {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 246) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_div Main →
      Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] =
      (execute_DIV_REM_pure
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
        (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRS).1
  := by
  intro cstrs h_is_real h_is_div
  have ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op Main cstrs
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_div] at h_is_div
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
  simp_all [-h_is_div]
  apply MulOperation.spec.mul at main_mul_low
  apply MulOperation.spec.mulh.gen at main_mul_high
  apply IsEqualWordOperation.spec.gen at overflow_b
  apply IsEqualWordOperation.spec.gen at overflow_c
  apply IsEqualWordOperation.spec.gen at w_overflow_b
  apply IsEqualWordOperation.spec.gen at w_overflow_c
  apply IsZeroWordOperation.spec at div_zero
  apply U16MSBOperation.spec.gen at eq_msb_b
  apply U16MSBOperation.spec.gen at eq_msb_c
  apply U16MSBOperation.spec.gen at eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_b
  apply U16MSBOperation.spec.gen at w_eq_msb_c
  apply U16MSBOperation.spec.gen at w_eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_quot
  apply AddOperation.spec.gen at c_neg_sum_zero
  apply AddOperation.spec.gen at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen at abs_check
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
  have := div_rem a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3
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
    obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := sop1 h_is_div
    -- Pre-extract limb bounds from is_U64_b/is_U64_c into named hypotheses so
    -- `simp_all` in the closer chain sees `b?.val < 65536` / `c?.val < 65536`
    -- directly. This closes the rbc/qbc arms that previously fell through to
    -- sorry, without needing per-arm `apply lt_cases_of_isU64 at` calls.
    have ⟨_hb0, _hb1, _hb2, _hb3⟩ := Word.lt_cases_of_isU64 is_U64_b
    have ⟨_hc0, _hc1, _hc2, _hc3⟩ := Word.lt_cases_of_isU64 is_U64_c
    simp [h_is_div, z0, z1, z2, z3, z4, z5, z6] at *
  all_goals first
    | (rw [← this, eq_d_a0, eq_d_a1, eq_d_a2, eq_d_a3])
    | omega
    | (apply Word.isU64_of_cases <;> simp_all; done)
    | (apply Word.isU64_of_cases <;> simp <;> omega)
    | (apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega)
    | (apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega)
    | (apply Word.lt_cases_of_isU64 at is_U64_c
       apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega)
    | (apply Word.lt_cases_of_isU64 at is_U64_b
       apply Word.isU64_of_cases <;> simp at is_U64_b ⊢ <;> omega)
    | (rcases b_b_neg with hbn | hbn <;>
       (apply Word.isU64_of_cases <;> simp_all [hbn] <;> omega))
    | (apply maco_arm_closer u16_ac0 u16_ac1 u16_ac2 u16_ac3
        (by split_ifs at div_zero
            · right; exact div_zero
            · left; exact div_zero))

-- Twin of `spec.div` with `.2` projection, `is_rem` flag,
-- `sop3` mutex, `eq_r_*` writeback.
set_option maxHeartbeats 32000000 in
-- See spec.div: same .DRS expansion blow-up.
set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
lemma spec.rem {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 246) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_rem Main →
      Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] =
      (execute_DIV_REM_pure
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
        (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRS).2
  := by
  intro cstrs h_is_real h_is_rem
  have ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op Main cstrs
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_rem] at h_is_rem
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
  simp_all [-h_is_rem]
  apply MulOperation.spec.mul at main_mul_low
  apply MulOperation.spec.mulh.gen at main_mul_high
  apply IsEqualWordOperation.spec.gen at overflow_b
  apply IsEqualWordOperation.spec.gen at overflow_c
  apply IsEqualWordOperation.spec.gen at w_overflow_b
  apply IsEqualWordOperation.spec.gen at w_overflow_c
  apply IsZeroWordOperation.spec at div_zero
  apply U16MSBOperation.spec.gen at eq_msb_b
  apply U16MSBOperation.spec.gen at eq_msb_c
  apply U16MSBOperation.spec.gen at eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_b
  apply U16MSBOperation.spec.gen at w_eq_msb_c
  apply U16MSBOperation.spec.gen at w_eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_quot
  apply AddOperation.spec.gen at c_neg_sum_zero
  apply AddOperation.spec.gen at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen at abs_check
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
  have := div_rem a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3
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
    obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := sop3 h_is_rem
    -- Same trick as spec.div: pre-extract limb bounds so simp_all uses them.
    have ⟨_hb0, _hb1, _hb2, _hb3⟩ := Word.lt_cases_of_isU64 is_U64_b
    have ⟨_hc0, _hc1, _hc2, _hc3⟩ := Word.lt_cases_of_isU64 is_U64_c
    simp [h_is_rem, z0, z1, z2, z3, z4, z5, z6] at *
  all_goals first
    | (rw [← this, eq_r_a0, eq_r_a1, eq_r_a2, eq_r_a3])
    | omega
    | (apply Word.isU64_of_cases <;> simp_all; done)
    | (apply Word.isU64_of_cases <;> simp <;> omega)
    | (apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega)
    | (apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega)
    | (apply Word.lt_cases_of_isU64 at is_U64_c
       apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega)
    | (apply Word.lt_cases_of_isU64 at is_U64_b
       apply Word.isU64_of_cases <;> simp at is_U64_b ⊢ <;> omega)
    | (rcases b_b_neg with hbn | hbn <;>
       (apply Word.isU64_of_cases <;> simp_all [hbn] <;> omega))
    | (apply maco_arm_closer u16_ac0 u16_ac1 u16_ac2 u16_ac3
        (by split_ifs at div_zero
            · right; exact div_zero
            · left; exact div_zero))

end div_rem

end DivRem
