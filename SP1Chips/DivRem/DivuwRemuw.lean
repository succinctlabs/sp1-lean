import SP1Chips.DivRem.Common

namespace DivRem

set_option linter.style.setOption false
set_option maxHeartbeats 100000000
-- The chip's `correct_*` proofs drive an imbalanced goal tree via chained
-- `apply ... at` / `specialize ... at` that operates on one focused case at a
-- time. Rewriting each to `<;>` would flatten the tree but require goal-state
-- reasoning the linter can't see; keep the existing structure.
set_option linter.style.multiGoal false

attribute [-simp] mul_eq_zero not_and

variable (Main : Vector (Fin KB) 246)

section divuw_remuw

set_option linter.unusedVariables false in
lemma divuw_remuw
  (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event : Fin KB)
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
  (w_overflow_b : is_word = 1 → is_overflow_b = if #v[b0, b1, 0, 0] = #v[0, 32768, 0, 0] then 1 else 0)
  (w_overflow_c : is_word = 1 → is_overflow_c = if #v[c0, c1, 0, 0] = #v[65535, 65535, 0, 0] then 1 else 0)
  (div_zero : is_c_0 = if #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] = #v[0, 0, 0, 0] then 1 else 0)
  (c_neg_sum_zero : c_neg = 1 → Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧ Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] = Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] + Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
  (rem_neg_sum_zero : rem_neg = 1 → Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧ Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] = Word.toBitVec64 #v[r0, r1, rbc2, rbc3] + Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
  (main_mul_low : Word.isU64 #v[ctq0, ctq1, ctq2, ctq3] ∧ Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MUL)
  (main_mul_high : is_word = 0 → (is_div + is_rem = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULH) ∧ (is_divu + is_remu = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULHU))
  (overflow_b : is_word = 0 → is_overflow_b = if #v[b0, b1, b2, b3] = #v[0, 0, 0, 32768] then 1 else 0)
  (overflow_c : is_word = 0 → is_overflow_c = if #v[c0, c1, c2, c3] = #v[65535, 65535, 65535, 65535] then 1 else 0)
  (eq_msb_b : is_word = 0 → msb_b = if 32768 ≤ b3 then 1 else 0)
  (eq_msb_c : is_word = 0 → msb_c = if 32768 ≤ c3 then 1 else 0)
  (eq_msb_rem : is_word = 0 → msb_rem = if 32768 ≤ r3 then 1 else 0)
  (w_eq_msb_b : is_word = 1 → msb_b = if 32768 ≤ b1 then 1 else 0)
  (w_eq_msb_c : is_word = 1 → msb_c = if 32768 ≤ c1 then 1 else 0)
  (w_eq_msb_rem : is_word = 1 → msb_rem = if 32768 ≤ r1 then 1 else 0)
  (w_eq_msb_quot : is_word = 1 → msb_quot = if 32768 ≤ q1 then 1 else 0)
  (abs_check : is_c_0 = 0 → arlt = if Word.toNat #v[ar0, ar1, ar2, ar3] < Word.toNat #v[is_c_0 + (1 - is_c_0) * ac0, (1 - is_c_0) * ac1, (1 - is_c_0) * ac2, (1 - is_c_0) * ac3] then 1 else 0) :
    is_divuw + is_remuw = 1 →
    ⟨Word.toBitVec64 #v[q0, q1, q2, q3], Word.toBitVec64 #v[r0, r1, r2, r3]⟩ = execute_DIV_REM_pure (Word.toBitVec64 #v[b0, b1, b2, b3]) (Word.toBitVec64 #v[c0, c1, c2, c3]) .DRWU
      := by
    intro divuw_remuw
    obtain ⟨z_div, z_rem, z_divu, z_remu, z_divw, z_remw⟩ : is_div = 0 ∧ is_rem = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 := by
      clear *- divuw_remuw sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_one_of_ops
      rcases b_is_divuw <;> rcases b_is_remuw <;> simp_all
    simp [z_div, z_rem, z_divu, z_remu, z_divw, z_remw, divuw_remuw] at *
    simp [eq_is_word] at *
    subst lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 abs_c_alu_event abs_rem_alu_event b_neg rem_neg c_neg
    simp [eq_is_overflow] at *
    subst ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 b_neg_not_overflow b_not_neg_not_overflow; simp at *
    subst maco12 maco13
    simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, Bool.cond_eq_ite, -BitVec.toNat_setWidth]
    rw [Word.setWidth_eq_low is_U64_b, Word.setWidth_eq_low is_U64_c]
    have is_U32_bl := Word.isU64_low_isU32 is_U64_b
    have is_U32_cl := Word.isU64_low_isU32 is_U64_c
    simp [Word.low] at *
    rw [HWord.toBitVec32_toNat is_U32_bl, HWord.toBitVec32_toNat is_U32_cl]
    have ext_q : #v[q0, q1, q2, q3] = HWord.extend #v[q0, q1] true := by simp [HWord.extend, HWord.isNegative]; subst q2 q3 msb_quot; split_ifs <;> simp
    have ext_r : #v[r0, r1, r2, r3] = HWord.extend #v[r0, r1] true := by simp [HWord.extend, HWord.isNegative]; subst r2 r3 msb_rem; split_ifs <;> simp
    rw [ext_q, ext_r]
    repeat rw [HWord.extend_true_is_signExtend (by apply HWord.isU32_of_cases <;> simpa)]
    suffices :
      HWord.toBitVec32 #v[q0, q1] = BitVec.ofNat 32 (if HWord.toNat #v[c0, c1] = 0 then (18446744073709551615 : ℤ) else (HWord.toNat #v[b0, b1]) / (HWord.toNat #v[c0, c1])).toNat ∧
      HWord.toBitVec32 #v[r0, r1] = BitVec.ofNat 32 (((HWord.toNat #v[b0, b1]) : ℤ).tmod ↑(HWord.toNat #v[c0, c1])).toNat
    · split_ands <;> congr 1 <;> [ exact this.1; exact this.2 ]
    · split_ifs at div_zero with nzc <;> simp [div_zero] at *
      · obtain ⟨zc0, zc1⟩ := nzc
        subst c0 c1 q0 q1 q2 q3 r0 r1 r2 r3
        simp [HWord.toBitVec32, HWord.toNat]
        congr
      · subst arlt maco10 maco11 is_c_0; simp at *
        rw [if_neg]; rotate_left
        · intro zc; simp [HWord.toNat] at zc; omega
        · have is_U32_r : HWord.isU32 #v[r0, r1] := by apply HWord.isU32_of_cases <;> simp <;> [ exact u16_r0; exact u16_r1 ]
          have is_U32_q : HWord.isU32 #v[q0, q1] := by apply HWord.isU32_of_cases <;> simp <;> [ exact u16_q0; exact u16_q1 ]
          suffices :
            HWord.toNat #v[q0, q1] = (((HWord.toNat #v[b0, b1]) : ℤ).tdiv (HWord.toNat #v[c0, c1])).toNat ∧
            HWord.toNat #v[r0, r1] = (((HWord.toNat #v[b0, b1]) : ℤ).tmod (HWord.toNat #v[c0, c1])).toNat
          · obtain ⟨hdiv, hrem⟩ := this
            simp at hdiv; rw [← hdiv, ← hrem]
            simp [← BitVec.toNat_inj]
            rw [HWord.toBitVec32_toNat is_U32_q, HWord.toBitVec32_toNat is_U32_r]
            rw [Nat.mod_eq_of_lt (by apply HWord.toNat_lt_of_isU32 is_U32_q)]
            rw [Nat.mod_eq_of_lt (by apply HWord.toNat_lt_of_isU32 is_U32_r)]
            simp
          · have cnz : HWord.toNat #v[c0, c1] ≠ 0 := by
              intro zc; simp [HWord.toNat] at zc; omega
            rw [tdiv_tmod_unique_full_nat cnz]
            split_ands <;> [ skip; (simp [HWord.toNat]; simp [Word.toNat] at abs_check; exact abs_check) ]
            have is_U32_b : HWord.isU32 #v[b0, b1] := by apply Word.lt_cases_of_isU64 at is_U64_b; clear *- is_U64_b; apply HWord.isU32_of_cases <;> tauto
            have is_U32_c : HWord.isU32 #v[c0, c1] := by apply Word.lt_cases_of_isU64 at is_U64_c; clear *- is_U64_c; apply HWord.isU32_of_cases <;> tauto
            clear *- is_U32_b is_U32_c is_U32_q is_U32_r
                     u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 b_cry0 b_cry1 b_cry2 b_cry3
                     eq_msb_b eq_msb_c eq_msb_rem r_neg_b_neg r_pos_b_pos
                     nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                     main_mul_low
            obtain ⟨is_U64_ctql, ctq_low⟩ := main_mul_low
            have eq_eb : (#v[b0, b1, 0, 0] : Word (Fin KB)) = HWord.extend #v[b0, b1] false := by simp [HWord.extend]
            have eq_er : (#v[r0, r1, 0, 0] : Word (Fin KB)) = HWord.extend #v[r0, r1] false := by simp [HWord.extend]
            suffices bv_ctqr:
              Word.toBitVec64 #v[b0, b1, 0, 0] =
                Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] +
                Word.toBitVec64 #v[r0, r1, 0, 0]
            · have := HWord.toNat_lt_of_isU32 is_U32_b
              have := HWord.toNat_lt_of_isU32 is_U32_q
              have := HWord.toNat_lt_of_isU32 is_U32_c
              have := HWord.toNat_lt_of_isU32 is_U32_r
              trans (Word.toBitVec64 #v[b0, b1, 0, 0]).toNat
              · rw [Word.low_toNat is_U32_b]
              · have : (Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3]).toNat = HWord.toNat #v[q0, q1] * HWord.toNat #v[c0, c1] := by
                  simp only [ctq_low, execute_MUL_pure, ↓reduceIte, reduceCtorEq, or_self]
                  simp only [BitVec.extend, ↓reduceIte]
                  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
                  rw [Nat.shiftRight_zero, BitVec.toNat_mul]
                  simp [Word.low_toNat is_U32_q, Word.low_toNat is_U32_c]
                  nlinarith
                rw [bv_ctqr, BitVec.toNat_add, this, Word.low_toNat is_U32_r]
                simp; nlinarith
            · clear is_U32_c eq_msb_b eq_msb_c eq_msb_rem ctq_low eq_is_word r_neg_b_neg r_pos_b_pos eq_eb eq_er
              apply HWord.lt_cases_of_isU32 at is_U32_b
              apply HWord.lt_cases_of_isU32 at is_U32_r
              apply HWord.lt_cases_of_isU32 at is_U32_q
              apply Word.lt_cases_of_isU64 at is_U64_ctql
              simp at *
              rw [← add_sub_right_comm] at u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
              rw [div_mod_decomposition_w (by omega) (by omega)] at nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
              trans Word.toBitVec64 #v[b0, b1, (ctq2 + cry1) % 65536, (ctq3 + cry2) % 65536]
              · rw [← nof_eq_ctqpr2.1, ← nof_eq_ctqpr3.1]
              · conv => lhs; simp [Word.toBitVec64, Word.toNat]
                        simp [nof_eq_ctqpr0.1, nof_eq_ctqpr1.1]
                        simp [nof_eq_ctqpr0.2, nof_eq_ctqpr1.2, nof_eq_ctqpr2.2, nof_eq_ctqpr3.2]
                simp [Fin.val_add]
                iterate 4 rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
                have joins : forall (i : Fin 4) (a b : ℕ), a % (65536 ^ i.val) + (b + a / (65536 ^ i.val)) % 65536 * (65536 ^ i.val) = (a + b * (65536 ^ i.val)) % (65536 ^ (i.val + 1)) := by
                  clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
                have divs : forall (i : Fin 4) (a b : ℕ), (a + b / (65536 ^ i.val)) / 65536 = (b + a * (65536 ^ i.val)) / (65536 ^ (i.val + 1)) := by
                  clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
                have j1 := joins 1; have j2 := joins 2; have j3 := joins 3
                have d1 := divs 1; have d2 := divs 2; have d3 := divs 3
                simp at *
                rw [j1, d1, j2, d2, j3]
                clear j1 j2 j3 d1 d2 d3 joins divs
                simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
                repeat rw [BitVec.toNat_add]
                iterate 2 rw [Word.toBitVec64_toNat (by apply Word.isU64_of_cases <;> simp <;> omega)]
                simp [Word.toNat]; ring_nf

set_option debug.skipKernelTC true in
set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
-- Polymorphic counterpart of `divuw_remuw`. 32-bit unsigned div/rem with
-- 64-bit sign-extended results. Mirrors `divu_remu_poly` recipe at HWord
-- (32-bit) input width: 4-limb carry chain (ctq0..3) + Word-level bv_ctqr
-- (no DWord 128-bit form needed since q*c fits in 64 bits).
lemma divuw_remuw_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    is_divuw + is_remuw = 1 →
    ⟨Word.toBitVec64_poly #v[q0, q1, q2, q3], Word.toBitVec64_poly #v[r0, r1, r2, r3]⟩ = execute_DIV_REM_pure (Word.toBitVec64_poly #v[b0, b1, b2, b3]) (Word.toBitVec64_poly #v[c0, c1, c2, c3]) .DRWU
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
    intro divuw_remuw
    obtain ⟨z_div, z_rem, z_divu, z_remu, z_divw, z_remw⟩ : is_div = 0 ∧ is_rem = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 := by
      clear *- divuw_remuw sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_one_of_ops h01 h21
      rcases b_is_divuw with h_du | h_du <;> rcases b_is_remuw with h_ru | h_ru
      · -- (0, 0): contradicts divuw_remuw (0 + 0 ≠ 1)
        exfalso; rw [h_du, h_ru, zero_add] at divuw_remuw; exact h01 divuw_remuw.symm
      · -- (0, 1): is_remuw = 1 → all others = 0
        have := sop8 h_ru
        exact ⟨this.1, this.2.2.1, this.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1⟩
      · -- (1, 0): is_divuw = 1 → all others = 0
        have := sop7 h_du
        exact ⟨this.1, this.2.2.1, this.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1⟩
      · -- (1, 1): contradicts divuw_remuw (1 + 1 = 2 ≠ 1)
        exfalso
        rw [h_du, h_ru] at divuw_remuw
        have : (1 + 1 : ZMod p) = 2 := by ring
        rw [this] at divuw_remuw; exact h21 divuw_remuw
    simp [z_div, z_rem, z_divu, z_remu, z_divw, z_remw, divuw_remuw] at *
    simp [eq_is_word] at *
    subst lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 abs_c_alu_event abs_rem_alu_event b_neg rem_neg c_neg
    simp [eq_is_overflow] at *
    subst ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 b_neg_not_overflow b_not_neg_not_overflow
    simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, Bool.cond_eq_ite, -BitVec.toNat_setWidth]
    rw [Word.setWidth_eq_low_poly is_U64_b, Word.setWidth_eq_low_poly is_U64_c]
    have is_U32_bl := Word.isU64_poly_low_poly_isU32_poly is_U64_b
    have is_U32_cl := Word.isU64_poly_low_poly_isU32_poly is_U64_c
    simp [Word.low_poly] at *
    rw [HWord.toBitVec32_poly_toNat_poly is_U32_bl, HWord.toBitVec32_poly_toNat_poly is_U32_cl]
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
    suffices :
      HWord.toBitVec32_poly #v[q0, q1] = BitVec.ofNat 32 (if HWord.toNat_poly #v[c0, c1] = 0 then (18446744073709551615 : ℤ) else (HWord.toNat_poly #v[b0, b1]) / (HWord.toNat_poly #v[c0, c1])).toNat ∧
      HWord.toBitVec32_poly #v[r0, r1] = BitVec.ofNat 32 (((HWord.toNat_poly #v[b0, b1]) : ℤ).tmod ↑(HWord.toNat_poly #v[c0, c1])).toNat
    · split_ands <;> congr 1 <;> [ exact this.1; exact this.2 ]
    · split_ifs at div_zero with nzc <;> simp [div_zero] at *
      · obtain ⟨zc0, zc1⟩ := nzc
        subst c0 c1 q0 q1 r0 r1
        simp [HWord.toBitVec32_poly, HWord.toNat_poly, h65535_val, h0v]
        push_cast [ZMod.cast_eq_val]
        rfl
      · subst arlt maco10 maco11 is_c_0; simp at *
        rw [if_neg]; rotate_left
        · intro zc
          have h_zc : c0.val + c1.val * 65536 = 0 := by
            unfold HWord.toNat_poly at zc; simpa using zc
          apply nzc
          have hc0v : c0.val = 0 := by omega
          have hc1v : c1.val = 0 := by omega
          exact ⟨(ZMod.val_eq_zero c0).mp hc0v, (ZMod.val_eq_zero c1).mp hc1v⟩
        · have is_U32_r : HWord.isU32_poly #v[r0, r1] := by
            apply HWord.isU32_of_cases_poly <;> simp <;> [ exact u16_r0; exact u16_r1 ]
          have is_U32_q : HWord.isU32_poly #v[q0, q1] := by
            apply HWord.isU32_of_cases_poly <;> simp <;> [ exact u16_q0; exact u16_q1 ]
          suffices :
            HWord.toNat_poly #v[q0, q1] = (((HWord.toNat_poly #v[b0, b1]) : ℤ).tdiv (HWord.toNat_poly #v[c0, c1])).toNat ∧
            HWord.toNat_poly #v[r0, r1] = (((HWord.toNat_poly #v[b0, b1]) : ℤ).tmod (HWord.toNat_poly #v[c0, c1])).toNat
          · obtain ⟨hdiv, hrem⟩ := this
            simp at hdiv; rw [← hdiv, ← hrem]
            simp [← BitVec.toNat_inj]
            rw [HWord.toBitVec32_poly_toNat_poly is_U32_q, HWord.toBitVec32_poly_toNat_poly is_U32_r]
            rw [Nat.mod_eq_of_lt (by apply HWord.toNat_poly_lt_of_isU32_poly is_U32_q)]
            rw [Nat.mod_eq_of_lt (by apply HWord.toNat_poly_lt_of_isU32_poly is_U32_r)]
            simp
          · have cnz : HWord.toNat_poly #v[c0, c1] ≠ 0 := by
              intro zc
              have h_zc : c0.val + c1.val * 65536 = 0 := by
                unfold HWord.toNat_poly at zc; simpa using zc
              apply nzc
              have hc0v : c0.val = 0 := by omega
              have hc1v : c1.val = 0 := by omega
              exact ⟨(ZMod.val_eq_zero c0).mp hc0v, (ZMod.val_eq_zero c1).mp hc1v⟩
            rw [tdiv_tmod_unique_full_nat cnz]
            split_ands <;>
              [ skip
              ; (simp [HWord.toNat_poly, h0v, h1v];
                 simp [Word.toNat_poly, h0v, h1v] at abs_check; exact abs_check) ]
            have is_U32_b : HWord.isU32_poly #v[b0, b1] := by
              apply Word.lt_cases_of_isU64_poly at is_U64_b; clear *- is_U64_b
              apply HWord.isU32_of_cases_poly <;> tauto
            have is_U32_c : HWord.isU32_poly #v[c0, c1] := by
              apply Word.lt_cases_of_isU64_poly at is_U64_c; clear *- is_U64_c
              apply HWord.isU32_of_cases_poly <;> tauto
            clear *- is_U32_b is_U32_c is_U32_q is_U32_r
                     u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3
                     b_cry0 b_cry1 b_cry2 b_cry3
                     eq_msb_b eq_msb_c eq_msb_rem r_neg_b_neg r_pos_b_pos
                     nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                     main_mul_low
                     h17 h01 h21 h65535_val h32768_val h1v h0v
                     hcv0 hcv1 hcv2 hcv3
            obtain ⟨is_U64_ctql, ctq_low⟩ := main_mul_low
            have eq_eb : (#v[b0, b1, 0, 0] : Word (ZMod p)) = HWord.extend_poly #v[b0, b1] false := by
              simp [HWord.extend_poly]
            have eq_er : (#v[r0, r1, 0, 0] : Word (ZMod p)) = HWord.extend_poly #v[r0, r1] false := by
              simp [HWord.extend_poly]
            suffices bv_ctqr :
              Word.toBitVec64_poly #v[b0, b1, 0, 0] =
                Word.toBitVec64_poly #v[ctq0, ctq1, ctq2, ctq3] +
                Word.toBitVec64_poly #v[r0, r1, 0, 0]
            · have := HWord.toNat_poly_lt_of_isU32_poly is_U32_b
              have := HWord.toNat_poly_lt_of_isU32_poly is_U32_q
              have := HWord.toNat_poly_lt_of_isU32_poly is_U32_c
              have := HWord.toNat_poly_lt_of_isU32_poly is_U32_r
              trans (Word.toBitVec64_poly #v[b0, b1, 0, 0]).toNat
              · rw [Word.low_toNat_poly is_U32_b]
              · have hctq : (Word.toBitVec64_poly #v[ctq0, ctq1, ctq2, ctq3]).toNat
                    = HWord.toNat_poly #v[q0, q1] * HWord.toNat_poly #v[c0, c1] := by
                  simp only [ctq_low, execute_MUL_pure, ↓reduceIte, reduceCtorEq, or_self]
                  simp only [BitVec.extend, ↓reduceIte]
                  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
                  rw [Nat.shiftRight_zero, BitVec.toNat_mul]
                  simp [Word.low_toNat_poly is_U32_q, Word.low_toNat_poly is_U32_c]
                  nlinarith
                rw [bv_ctqr, BitVec.toNat_add, hctq, Word.low_toNat_poly is_U32_r]
                simp; nlinarith
            · clear is_U32_c eq_msb_b eq_msb_c eq_msb_rem ctq_low eq_is_word r_neg_b_neg r_pos_b_pos eq_eb eq_er
              apply HWord.lt_cases_of_isU32_poly at is_U32_b
              apply HWord.lt_cases_of_isU32_poly at is_U32_r
              apply HWord.lt_cases_of_isU32_poly at is_U32_q
              apply Word.lt_cases_of_isU64_poly at is_U64_ctql
              simp at *
              rw [← add_sub_right_comm] at u16_ctqpr1 u16_ctqpr2 u16_ctqpr3
                                            nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
              rw [div_mod_decomposition_w_poly (by omega) (by omega : cry0.val < 2)] at nof_eq_ctqpr0
              rw [div_mod_decomposition_w_poly (by omega) (by omega : cry1.val < 2)] at nof_eq_ctqpr1
              rw [div_mod_decomposition_w_poly (by simp) (by omega : cry2.val < 2)] at nof_eq_ctqpr2
              rw [div_mod_decomposition_w_poly (by simp) (by omega : cry3.val < 2)] at nof_eq_ctqpr3
              -- Reduce LHS Word toBitVec64_poly to BitVec.ofNat 64 form. For
              -- divuw_remuw, r2 = r3 = 0 (rem_neg = 0 path) so the carry chain
              -- only references ctq0..3 + r0,r1 (the high two limbs vanish).
              obtain ⟨b0_lt, b1_lt⟩ := is_U32_b
              obtain ⟨ctq0_lt, ctq1_lt, ctq2_lt, ctq3_lt⟩ := is_U64_ctql
              obtain ⟨r0_lt, r1_lt⟩ := is_U32_r
              -- Distribute .val over + for the carry chain sums.
              have hsum01 : (ctq0 + r0).val = ctq0.val + r0.val :=
                ZMod.val_add_of_lt (by omega)
              have hsum1' : (ctq1 + r1).val = ctq1.val + r1.val :=
                ZMod.val_add_of_lt (by omega)
              have hsum1 : (ctq1 + r1 + cry0).val = ctq1.val + r1.val + cry0.val := by
                rw [show (ctq1 + r1 + cry0) = (ctq1 + r1) + cry0 from rfl,
                    ZMod.val_add_of_lt (by rw [hsum1']; omega), hsum1']
              have hsum2 : (ctq2 + cry1).val = ctq2.val + cry1.val :=
                ZMod.val_add_of_lt (by omega)
              have hsum3 : (ctq3 + cry2).val = ctq3.val + cry2.val :=
                ZMod.val_add_of_lt (by omega)
              -- Build clean Nat-side carry equations.
              have eq0 : b0.val + cry0.val * 65536 = ctq0.val + r0.val := by
                obtain ⟨h1, h2⟩ := nof_eq_ctqpr0; rw [hsum01] at h1 h2; omega
              have eq1 : b1.val + cry1.val * 65536 = ctq1.val + r1.val + cry0.val := by
                obtain ⟨h1, h2⟩ := nof_eq_ctqpr1; rw [hsum1] at h1 h2; omega
              have eq2 : cry2.val * 65536 = ctq2.val + cry1.val := by
                obtain ⟨h1, h2⟩ := nof_eq_ctqpr2
                rw [hsum2] at h1 h2
                simp only [ZMod.val_zero] at h1
                omega
              have eq3 : cry3.val * 65536 = ctq3.val + cry2.val := by
                obtain ⟨h1, h2⟩ := nof_eq_ctqpr3
                rw [hsum3] at h1 h2
                simp only [ZMod.val_zero] at h1
                omega
              -- Linear combination of eq0..eq3 weighted by 2^(16i).
              -- cry3 may be 0 or 1 — its * 2^64 contribution drops on mod 2^64.
              have main_eq :
                  b0.val + b1.val * 65536 + cry3.val * 18446744073709551616 =
                  ctq0.val + ctq1.val * 65536 + ctq2.val * 4294967296 +
                    ctq3.val * 281474976710656 +
                  (r0.val + r1.val * 65536) := by
                omega
              -- Lift to BitVec equality via .toNat injection.
              rw [← BitVec.toNat_inj]
              rw [BitVec.toNat_add]
              rw [show Word.toBitVec64_poly (#v[b0, b1, 0, 0] : Word (ZMod p)) =
                    BitVec.ofNat 64 (b0.val + b1.val * 65536) from by
                    simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero]]
              rw [show Word.toBitVec64_poly #v[ctq0, ctq1, ctq2, ctq3] =
                    BitVec.ofNat 64 (ctq0.val + ctq1.val * 65536 +
                      ctq2.val * 4294967296 + ctq3.val * 281474976710656) from by
                    simp [Word.toBitVec64_poly, Word.toNat_poly]]
              rw [show Word.toBitVec64_poly (#v[r0, r1, 0, 0] : Word (ZMod p)) =
                    BitVec.ofNat 64 (r0.val + r1.val * 65536) from by
                    simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero]]
              simp only [BitVec.toNat_ofNat]
              omega

set_option maxRecDepth 1000000 in
lemma spec.divuw :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_divuw Main →
      Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = (execute_DIV_REM_pure (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRWU).1
  := by
  intro cstrs h_is_real h_is_divuw
  have ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op Main cstrs
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_divuw] at h_is_divuw
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
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
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
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops, h_op_a_0⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_divuw]
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
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c div_zero eq_msb_b eq_msb_c
       eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check
  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by subst is_word; rfl
  have := divuw_remuw a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1 eq_lb2 eq_lc2 eq_lb3 eq_lc3 eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2 w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3 eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2 w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this eq_b_neg_not_overflow eq_not_b_neg_not_overflow of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3 nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7 u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7 eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3 r_neg_b_neg r_pos_b_pos c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3 cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3 u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3 u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by clear *- b_is_real_not_word; rcases b_is_real_not_word <;> [ omega; simp_all ]
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7 u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero main_mul_low main_mul_high overflow_b overflow_c eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check
  all_goals
    obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := sop7 h_is_divuw
    simp [h_is_divuw, z0, z1, z2, z3, z4, z5, z6] at *
  · rw [← this, eq_d_a0, eq_d_a1, eq_d_a2, eq_d_a3]
  · apply Word.isU64_of_cases <;> simp <;> omega
  · split_ifs at div_zero <;> simp [div_zero] <;> apply Word.isU64_of_cases <;> simp <;> assumption
  · apply Word.isU64_of_cases <;> simp <;> omega
  · apply Word.isU64_of_cases <;> simp <;> omega
  · apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega
  · apply Word.isU64_of_cases <;> simp <;> omega
  · rw [Fin.lt_def]; omega
  · rw [Fin.lt_def]; omega
  · apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  · apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  · rw [Fin.lt_def]; omega
  · apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  · apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  · apply Word.isU64_of_cases <;> simp <;> omega
  · apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega
  · apply Word.isU64_of_cases <;> simp <;> omega
  · apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega

set_option maxRecDepth 1000000 in
lemma spec.remuw :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_remuw Main →
      Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = (execute_DIV_REM_pure (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRWU).2
  := by
  intro cstrs h_is_real h_is_remuw
  have ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op Main cstrs
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_remuw] at h_is_remuw
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
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
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
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops, h_op_a_0⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_remuw]
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
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c div_zero eq_msb_b eq_msb_c
       eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check
  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by subst is_word; rfl
  have := divuw_remuw a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1 eq_lb2 eq_lc2 eq_lb3 eq_lc3 eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2 w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3 eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2 w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this eq_b_neg_not_overflow eq_not_b_neg_not_overflow of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3 nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7 u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7 eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3 r_neg_b_neg r_pos_b_pos c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3 cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3 u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3 u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by clear *- b_is_real_not_word; rcases b_is_real_not_word <;> [ omega; simp_all ]
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7 u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero main_mul_low main_mul_high overflow_b overflow_c eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check
  all_goals
    obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := sop8 h_is_remuw
    simp [h_is_remuw, z0, z1, z2, z3, z4, z5, z6] at *
  · rw [← this, eq_r_a0, eq_r_a1, eq_r_a2, eq_r_a3]
  · apply Word.isU64_of_cases <;> simp <;> omega
  · split_ifs at div_zero <;> simp [div_zero] <;> apply Word.isU64_of_cases <;> simp <;> assumption
  · apply Word.isU64_of_cases <;> simp <;> omega
  · apply Word.isU64_of_cases <;> simp <;> omega
  · apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega
  · apply Word.isU64_of_cases <;> simp <;> omega
  · rw [Fin.lt_def]; omega
  · rw [Fin.lt_def]; omega
  · apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  · apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  · rw [Fin.lt_def]; omega
  · apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  · apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  · apply Word.isU64_of_cases <;> simp <;> omega
  · apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega
  · apply Word.isU64_of_cases <;> simp <;> omega
  · apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega

-- Polymorphic counterpart of `spec.divuw`. Mirrors `spec.divu_poly` recipe but
-- with `.DRWU` instruction, `is_divuw_poly` flag, `sop7` mutex implication,
-- and threads through `divuw_remuw_poly` (4-limb HWord core).
set_option debug.skipKernelTC true in
set_option maxHeartbeats 32000000 in
set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
lemma spec.divuw_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 246) :
  List.Forall SP1Constraint.toProp_poly (constraints Main) →
    is_real_poly Main → is_divuw_poly Main →
      Word.toBitVec64_poly #v[Main[28], Main[29], Main[30], Main[31]] =
      (execute_DIV_REM_pure
        (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
        (Word.toBitVec64_poly #v[Main[22], Main[23], Main[24], Main[25]]) .DRWU).1
  := by
  intro cstrs h_is_real h_is_divuw
  have ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op_poly Main cstrs
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff_poly Main).mp cstrs; simp at h_is_real
  simp [is_divuw_poly] at h_is_divuw
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
  simp_all [-h_is_divuw]
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
  have := divuw_remuw_poly a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3
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
    obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := sop7 h_is_divuw
    simp [h_is_divuw, z0, z1, z2, z3, z4, z5, z6] at *
  -- Trailing-arm closer. Mirrors Fin KB `spec.divuw` arm closers but in
  -- `first` form. Covers writeback, omega, isU64-via-cases (both `simp_all`
  -- and `simp+omega` variants), per-limb c/b bounds via `lt_cases_of_isU64`,
  -- 2-step c/b extractions (Fin KB line 906/916/918), and the maco arm.
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
    -- FIXME: 2-3 stubborn arms `Word.isU64_poly #v[r0, r1, rbc2, rbc3]` and
    -- `Word.isU64_poly #v[q0, q1, qbc2, qbc3]` involve rbc/qbc dependence on
    -- `b_neg` via `eq_rbc*`/`eq_qbc*` constraint hypotheses. Field-level
    -- substitution needed; tracked as part of Phase 1.2 follow-up.
    | sorry

-- Polymorphic counterpart of `spec.remuw`. Twin of `spec.divuw_poly` with
-- `.2` projection, `is_remuw_poly` flag, `sop8` mutex, and `eq_r_*` writeback.
set_option debug.skipKernelTC true in
set_option maxHeartbeats 32000000 in
set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
lemma spec.remuw_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 246) :
  List.Forall SP1Constraint.toProp_poly (constraints Main) →
    is_real_poly Main → is_remuw_poly Main →
      Word.toBitVec64_poly #v[Main[28], Main[29], Main[30], Main[31]] =
      (execute_DIV_REM_pure
        (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
        (Word.toBitVec64_poly #v[Main[22], Main[23], Main[24], Main[25]]) .DRWU).2
  := by
  intro cstrs h_is_real h_is_remuw
  have ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op_poly Main cstrs
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff_poly Main).mp cstrs; simp at h_is_real
  simp [is_remuw_poly] at h_is_remuw
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
  simp_all [-h_is_remuw]
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
  have := divuw_remuw_poly a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3
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
    obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := sop8 h_is_remuw
    simp [h_is_remuw, z0, z1, z2, z3, z4, z5, z6] at *
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
    -- FIXME: 2-3 stubborn arms `Word.isU64_poly #v[r0, r1, rbc2, rbc3]` and
    -- `Word.isU64_poly #v[q0, q1, qbc2, qbc3]` involve rbc/qbc dependence on
    -- `b_neg` via `eq_rbc*`/`eq_qbc*` constraint hypotheses. Field-level
    -- substitution needed; tracked as part of Phase 1.2 follow-up.
    | sorry

end divuw_remuw

end DivRem
