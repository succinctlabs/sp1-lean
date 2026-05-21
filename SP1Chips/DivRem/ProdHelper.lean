import SP1Chips.DivRem.Common

namespace DivRem

set_option linter.style.setOption false
set_option maxHeartbeats 100000000
-- The DivRem h_prod helper drives an imbalanced goal tree via chained
-- `apply ... at` / `specialize ... at`; flattening to `<;>` would require
-- goal-state reasoning the linter can't see.
set_option linter.style.multiGoal false
set_option linter.style.longLine false


section divrem_kernel_helpers

/-- Opaque alias for `2 ^ 128` — referenced in the close-helpers' types so the kernel
re-check at chip call sites doesn't walk the literal. The `2^128` is walked exactly
once inside each of the custom `BitVec.toNat_*_128` lemma oleans and inside `divrem_N128_eq`. -/
@[irreducible] def divrem_N128 : ℕ := 2 ^ 128

lemma divrem_N128_eq : divrem_N128 = 2 ^ 128 := by
  unfold divrem_N128; rfl

/-- Custom `BitVec.toNat_ofNat` specialized to width 128, concluding in the opaque
`divrem_N128` alias. Use in place of `BitVec.toNat_ofNat` inside the DivRem cores'
simp sets to keep `2^128` out of the chip's proof term. -/
lemma BitVec.toNat_ofNat_128 (k : ℕ) :
    (BitVec.ofNat 128 k).toNat = k % divrem_N128 := by
  rw [divrem_N128_eq, _root_.BitVec.toNat_ofNat]

/-- Custom `BitVec.toNat_add` specialized to width 128, concluding in the opaque
`divrem_N128` alias. -/
lemma BitVec.toNat_add_128 (x y : BitVec 128) :
    (x + y).toNat = (x.toNat + y.toNat) % divrem_N128 := by
  rw [divrem_N128_eq, _root_.BitVec.toNat_add]

/-- Bare-`Nat` close-helper for `divu_remu`'s final mod step. Both type and proof
body reference `divrem_N128` (opaque). Manual `Nat.add_mod` + `Nat.add_mul_mod_self_right`
chain avoids `omega`'s `Int.toNat (… % 2^128)` certificate (which trips the kernel). -/
lemma divu_remu_close_helper
    (b0 b1 b2 b3 r0 r1 r2 r3 : ℕ)
    (ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 : ℕ)
    (cry7 : ℕ)
    (h_main :
      b0 + b1 * 65536 + b2 * 4294967296 + b3 * 281474976710656 +
        cry7 * divrem_N128 =
      ctq0 + ctq1 * 65536 + ctq2 * 4294967296 + ctq3 * 281474976710656 +
        ctq4 * 18446744073709551616 + ctq5 * 1208925819614629174706176 +
        ctq6 * 79228162514264337593543950336 +
        ctq7 * 5192296858534827628530496329220096 +
      (r0 + r1 * 65536 + r2 * 4294967296 + r3 * 281474976710656)) :
    (b0 + b1 * 65536 + b2 * 4294967296 + b3 * 281474976710656) % divrem_N128 =
      ((ctq0 + ctq1 * 65536 + ctq2 * 4294967296 + ctq3 * 281474976710656 +
          ctq4 * 18446744073709551616 + ctq5 * 1208925819614629174706176 +
          ctq6 * 79228162514264337593543950336 +
          ctq7 * 5192296858534827628530496329220096) % divrem_N128 +
        (r0 + r1 * 65536 + r2 * 4294967296 + r3 * 281474976710656) % divrem_N128) %
      divrem_N128 := by
  rw [← Nat.add_mod, ← h_main, Nat.add_mul_mod_self_right]

/-- Signed-variant close-helper for `div_rem` (mirrors `divu_remu_close_helper`
but with the `msb_b * 65535` and `msb_rem * 65535` sign-extension terms in upper limbs
of `b` and `r`). -/
lemma div_rem_close_helper
    (b0 b1 b2 b3 r0 r1 r2 r3 : ℕ)
    (ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 : ℕ)
    (msb_b_ext msb_rem_ext : ℕ)
    (cry7 : ℕ)
    (h_main :
      b0 + b1 * 65536 + b2 * 4294967296 + b3 * 281474976710656 +
        msb_b_ext * 18446744073709551616 + msb_b_ext * 1208925819614629174706176 +
        msb_b_ext * 79228162514264337593543950336 +
        msb_b_ext * 5192296858534827628530496329220096 +
        cry7 * divrem_N128 =
      ctq0 + ctq1 * 65536 + ctq2 * 4294967296 + ctq3 * 281474976710656 +
        ctq4 * 18446744073709551616 + ctq5 * 1208925819614629174706176 +
        ctq6 * 79228162514264337593543950336 +
        ctq7 * 5192296858534827628530496329220096 +
      (r0 + r1 * 65536 + r2 * 4294967296 + r3 * 281474976710656 +
        msb_rem_ext * 18446744073709551616 +
        msb_rem_ext * 1208925819614629174706176 +
        msb_rem_ext * 79228162514264337593543950336 +
        msb_rem_ext * 5192296858534827628530496329220096)) :
    (b0 + b1 * 65536 + b2 * 4294967296 + b3 * 281474976710656 +
        msb_b_ext * 18446744073709551616 + msb_b_ext * 1208925819614629174706176 +
        msb_b_ext * 79228162514264337593543950336 +
        msb_b_ext * 5192296858534827628530496329220096) % divrem_N128 =
      ((ctq0 + ctq1 * 65536 + ctq2 * 4294967296 + ctq3 * 281474976710656 +
          ctq4 * 18446744073709551616 + ctq5 * 1208925819614629174706176 +
          ctq6 * 79228162514264337593543950336 +
          ctq7 * 5192296858534827628530496329220096) % divrem_N128 +
        (r0 + r1 * 65536 + r2 * 4294967296 + r3 * 281474976710656 +
          msb_rem_ext * 18446744073709551616 +
          msb_rem_ext * 1208925819614629174706176 +
          msb_rem_ext * 79228162514264337593543950336 +
          msb_rem_ext * 5192296858534827628530496329220096) % divrem_N128) %
      divrem_N128 := by
  rw [← Nat.add_mod, ← h_main, Nat.add_mul_mod_self_right]

end divrem_kernel_helpers

section divrem_h_prod_helper

set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
-- 32M heartbeats + 1M recursion: matches `div_rem`'s budget for the same
-- proof body (8-limb DWord carry chain + Stage A signExtend + close-helper).
/-- Extracted `h_prod` for `div_rem` (signed 64-bit DRS branch).

Lifted from `SP1Chips/DivRem/DivRem.lean:429-646` so its kernel re-check runs in
its own olean independently from `div_rem`'s. The body would otherwise add
`2^128` walks (via `simp at ctq` from `combine_MUL_MULH`, the `Word.extend`
unfoldings, Stage A signExtend chain, and the Step B `DWord.toBitVec128` simps)
to `div_rem`'s kernel check, summing past the kernel's WHNF reduction depth.

Inputs are the post-`simp at *` specialized forms of the chip-level hypotheses
(non-overflow branch, `is_div + is_rem = 1` so all `is_*` flags except is_div/rem
are 0 and `is_word = 0`). Caller derives `is_U64_q`, `is_U64_r` from `u16_q*`,
`u16_r*` + `b_cry*`, and specializes `eq_msb_b`, `eq_msb_rem`, the `nof_eq_ctqpr*`
disjunctions, the `u16_ctqpr*` bounds, `main_mul_low`, and `main_mul_high` before
the call. -/
lemma div_rem_h_prod_aux {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    [Fact (2 ^ 24 < p)]
    {b0 b1 b2 b3 c0 c1 c2 c3 q0 q1 q2 q3 r0 r1 r2 r3
     ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7
     cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7
     msb_b msb_rem : ZMod p}
    (is_U64_b : Word.isU64 #v[b0, b1, b2, b3])
    (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
    (is_U64_q : Word.isU64 #v[q0, q1, q2, q3])
    (is_U64_r : Word.isU64 #v[r0, r1, r2, r3])
    (eq_msb_b : msb_b = if 32768 ≤ b3 then 1 else 0)
    (eq_msb_rem : msb_rem = if 32768 ≤ r3 then 1 else 0)
    (b_cry0 : cry0 = 0 ∨ cry0 = 1) (b_cry1 : cry1 = 0 ∨ cry1 = 1)
    (b_cry2 : cry2 = 0 ∨ cry2 = 1) (b_cry3 : cry3 = 0 ∨ cry3 = 1)
    (b_cry4 : cry4 = 0 ∨ cry4 = 1) (b_cry5 : cry5 = 0 ∨ cry5 = 1)
    (b_cry6 : cry6 = 0 ∨ cry6 = 1) (b_cry7 : cry7 = 0 ∨ cry7 = 1)
    (nof_eq_ctqpr0 : b0 = ctq0 + r0 - cry0 * 65536)
    (nof_eq_ctqpr1 : b1 = ctq1 + r1 - cry1 * 65536 + cry0)
    (nof_eq_ctqpr2 : b2 = ctq2 + r2 - cry2 * 65536 + cry1)
    (nof_eq_ctqpr3 : b3 = ctq3 + r3 - cry3 * 65536 + cry2)
    (nof_eq_ctqpr4 : ctq4 + msb_rem * 65535 - cry4 * 65536 + cry3 = msb_b * 65535)
    (nof_eq_ctqpr5 : ctq5 + msb_rem * 65535 - cry5 * 65536 + cry4 = msb_b * 65535)
    (nof_eq_ctqpr6 : ctq6 + msb_rem * 65535 - cry6 * 65536 + cry5 = msb_b * 65535)
    (nof_eq_ctqpr7 : ctq7 + msb_rem * 65535 - cry7 * 65536 + cry6 = msb_b * 65535)
    (u16_ctqpr0 : (ctq0 + r0 - cry0 * 65536).val < 65536)
    (u16_ctqpr1 : (ctq1 + r1 - cry1 * 65536 + cry0).val < 65536)
    (u16_ctqpr2 : (ctq2 + r2 - cry2 * 65536 + cry1).val < 65536)
    (u16_ctqpr3 : (ctq3 + r3 - cry3 * 65536 + cry2).val < 65536)
    (u16_ctqpr4 : (ctq4 + msb_rem * 65535 - cry4 * 65536 + cry3).val < 65536)
    (u16_ctqpr5 : (ctq5 + msb_rem * 65535 - cry5 * 65536 + cry4).val < 65536)
    (u16_ctqpr6 : (ctq6 + msb_rem * 65535 - cry6 * 65536 + cry5).val < 65536)
    (u16_ctqpr7 : (ctq7 + msb_rem * 65535 - cry7 * 65536 + cry6).val < 65536)
    (main_mul_low : Word.isU64 #v[ctq0, ctq1, ctq2, ctq3] ∧
        Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] =
          execute_MUL_pure (Word.toBitVec64 #v[q0, q1, q2, q3])
            (Word.toBitVec64 #v[c0, c1, c2, c3]) mop.MUL)
    (main_mul_high : Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧
        Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] =
          execute_MUL_pure (Word.toBitVec64 #v[q0, q1, q2, q3])
            (Word.toBitVec64 #v[c0, c1, c2, c3]) mop.MULH) :
    Word.toInt #v[b0, b1, b2, b3] =
      Word.toInt #v[q0, q1, q2, q3] * Word.toInt #v[c0, c1, c2, c3] +
      Word.toInt #v[r0, r1, r2, r3] := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  have h24 : 2 ^ 24 < p := Fact.out
  have h65535_val : (65535 : ZMod p).val = 65535 := by
    have h : ((65535 : ℕ) : ZMod p).val = 65535 := ZMod.val_natCast_of_lt (by omega)
    simpa using h
  have h32768_val : (32768 : ZMod p).val = 32768 := by
    have h : ((32768 : ℕ) : ZMod p).val = 32768 := ZMod.val_natCast_of_lt (by omega)
    exact_mod_cast h
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
  have u16_msb_b_v : (msb_b * 65535).val < 65536 := by
    rw [eq_msb_b]; split_ifs <;> simp [h0v, h65535_val]
  have u16_msb_rem_v : (msb_rem * 65535).val < 65536 := by
    rw [eq_msb_rem]; split_ifs <;> simp [h0v, h65535_val]
  have heq32_b3 : (32768 : ZMod p) ≤ b3 ↔ 32768 ≤ b3.val := by
    change (32768 : ZMod p).val ≤ b3.val ↔ _; rw [val_32768_zmod_p]
  have heq32_r3 : (32768 : ZMod p) ≤ r3 ↔ 32768 ≤ r3.val := by
    change (32768 : ZMod p).val ≤ r3.val ↔ _; rw [val_32768_zmod_p]
  obtain ⟨is_U64_ctql, ctq_low⟩ := main_mul_low
  obtain ⟨is_U64_ctqh, ctq_high⟩ := main_mul_high
  have ctq := combine_MUL_MULH is_U64_ctql is_U64_ctqh is_U64_q is_U64_c
    ctq_low ctq_high
  simp at ctq
  have eq_eb : (#v[b0, b1, b2, b3, msb_b * 65535, msb_b * 65535,
        msb_b * 65535, msb_b * 65535] : DWord (ZMod p)) =
      Word.extend #v[b0, b1, b2, b3] true := by
    simp [Word.extend, Word.isNegative, eq_msb_b, heq32_b3]
  have eq_er : (#v[r0, r1, r2, r3, msb_rem * 65535, msb_rem * 65535,
        msb_rem * 65535, msb_rem * 65535] : DWord (ZMod p)) =
      Word.extend #v[r0, r1, r2, r3] true := by
    simp [Word.extend, Word.isNegative, eq_msb_rem, heq32_r3]
  suffices bv_ctqr :
    DWord.toBitVec128 (#v[b0, b1, b2, b3, msb_b * 65535, msb_b * 65535,
        msb_b * 65535, msb_b * 65535] : DWord (ZMod p)) =
      DWord.toBitVec128 (#v[ctq0, ctq1, ctq2, ctq3,
        ctq4, ctq5, ctq6, ctq7] : DWord (ZMod p)) +
      DWord.toBitVec128 (#v[r0, r1, r2, r3, msb_rem * 65535, msb_rem * 65535,
        msb_rem * 65535, msb_rem * 65535] : DWord (ZMod p)) by
    rw [eq_eb, eq_er] at bv_ctqr
    rw [ctq] at bv_ctqr
    repeat rw [Word.extend_true_is_signExtend (by assumption)] at bv_ctqr
    simp [← BitVec.toInt_inj] at bv_ctqr
    repeat rw [BitVec.toInt_signExtend_of_le (by simp)] at bv_ctqr
    repeat rw [Word.toBitVec64_toInt (by assumption)] at bv_ctqr
    have lbq := Word.toInt_lb is_U64_q
    have ubq := Word.toInt_ub is_U64_q
    have lbr := Word.toInt_lb is_U64_r
    have ubr := Word.toInt_ub is_U64_r
    have lbc := Word.toInt_lb is_U64_c
    have ubc := Word.toInt_ub is_U64_c
    rw [bv_ctqr]
    apply Int.bmod_eq_of_le <;> simp <;> nlinarith
  · clear is_U64_c eq_msb_b eq_msb_rem ctq_low ctq_high ctq eq_eb eq_er
    apply Word.lt_cases_of_isU64 at is_U64_b
    apply Word.lt_cases_of_isU64 at is_U64_r
    apply Word.lt_cases_of_isU64 at is_U64_q
    apply Word.lt_cases_of_isU64 at is_U64_ctql
    apply Word.lt_cases_of_isU64 at is_U64_ctqh
    simp at *
    rw [eq_comm] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
    rw [← add_sub_right_comm] at u16_ctqpr1 u16_ctqpr2 u16_ctqpr3
                                 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7
                                 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                                 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6
                                 nof_eq_ctqpr7
    rw [div_mod_decomposition_w (by omega) (by omega : cry0.val < 2)]
      at nof_eq_ctqpr0
    rw [div_mod_decomposition_w (by omega) (by omega : cry1.val < 2)]
      at nof_eq_ctqpr1
    rw [div_mod_decomposition_w (by omega) (by omega : cry2.val < 2)]
      at nof_eq_ctqpr2
    rw [div_mod_decomposition_w (by omega) (by omega : cry3.val < 2)]
      at nof_eq_ctqpr3
    rw [div_mod_decomposition_w (by omega) (by omega : cry4.val < 2)]
      at nof_eq_ctqpr4
    rw [div_mod_decomposition_w (by omega) (by omega : cry5.val < 2)]
      at nof_eq_ctqpr5
    rw [div_mod_decomposition_w (by omega) (by omega : cry6.val < 2)]
      at nof_eq_ctqpr6
    rw [div_mod_decomposition_w (by omega) (by omega : cry7.val < 2)]
      at nof_eq_ctqpr7
    obtain ⟨b0_lt, b1_lt, b2_lt, b3_lt⟩ := is_U64_b
    obtain ⟨r0_lt, r1_lt, r2_lt, r3_lt⟩ := is_U64_r
    obtain ⟨ctq0_lt, ctq1_lt, ctq2_lt, ctq3_lt⟩ := is_U64_ctql
    obtain ⟨ctq4_lt, ctq5_lt, ctq6_lt, ctq7_lt⟩ := is_U64_ctqh
    have hsum01 : (ctq0 + r0).val = ctq0.val + r0.val :=
      ZMod.val_add_of_lt (by omega)
    have hsum1' : (ctq1 + r1).val = ctq1.val + r1.val :=
      ZMod.val_add_of_lt (by omega)
    have hsum1 : (ctq1 + r1 + cry0).val = ctq1.val + r1.val + cry0.val := by
      rw [show (ctq1 + r1 + cry0) = (ctq1 + r1) + cry0 from rfl,
          ZMod.val_add_of_lt (by rw [hsum1']; omega), hsum1']
    have hsum2' : (ctq2 + r2).val = ctq2.val + r2.val :=
      ZMod.val_add_of_lt (by omega)
    have hsum2 : (ctq2 + r2 + cry1).val = ctq2.val + r2.val + cry1.val := by
      rw [show (ctq2 + r2 + cry1) = (ctq2 + r2) + cry1 from rfl,
          ZMod.val_add_of_lt (by rw [hsum2']; omega), hsum2']
    have hsum3' : (ctq3 + r3).val = ctq3.val + r3.val :=
      ZMod.val_add_of_lt (by omega)
    have hsum3 : (ctq3 + r3 + cry2).val = ctq3.val + r3.val + cry2.val := by
      rw [show (ctq3 + r3 + cry2) = (ctq3 + r3) + cry2 from rfl,
          ZMod.val_add_of_lt (by rw [hsum3']; omega), hsum3']
    have hsum4' : (ctq4 + msb_rem * 65535).val =
        ctq4.val + (msb_rem * 65535).val :=
      ZMod.val_add_of_lt (by omega)
    have hsum4 : (ctq4 + msb_rem * 65535 + cry3).val =
        ctq4.val + (msb_rem * 65535).val + cry3.val := by
      rw [show (ctq4 + msb_rem * 65535 + cry3) =
            (ctq4 + msb_rem * 65535) + cry3 from rfl,
          ZMod.val_add_of_lt (by rw [hsum4']; omega), hsum4']
    have hsum5' : (ctq5 + msb_rem * 65535).val =
        ctq5.val + (msb_rem * 65535).val :=
      ZMod.val_add_of_lt (by omega)
    have hsum5 : (ctq5 + msb_rem * 65535 + cry4).val =
        ctq5.val + (msb_rem * 65535).val + cry4.val := by
      rw [show (ctq5 + msb_rem * 65535 + cry4) =
            (ctq5 + msb_rem * 65535) + cry4 from rfl,
          ZMod.val_add_of_lt (by rw [hsum5']; omega), hsum5']
    have hsum6' : (ctq6 + msb_rem * 65535).val =
        ctq6.val + (msb_rem * 65535).val :=
      ZMod.val_add_of_lt (by omega)
    have hsum6 : (ctq6 + msb_rem * 65535 + cry5).val =
        ctq6.val + (msb_rem * 65535).val + cry5.val := by
      rw [show (ctq6 + msb_rem * 65535 + cry5) =
            (ctq6 + msb_rem * 65535) + cry5 from rfl,
          ZMod.val_add_of_lt (by rw [hsum6']; omega), hsum6']
    have hsum7' : (ctq7 + msb_rem * 65535).val =
        ctq7.val + (msb_rem * 65535).val :=
      ZMod.val_add_of_lt (by omega)
    have hsum7 : (ctq7 + msb_rem * 65535 + cry6).val =
        ctq7.val + (msb_rem * 65535).val + cry6.val := by
      rw [show (ctq7 + msb_rem * 65535 + cry6) =
            (ctq7 + msb_rem * 65535) + cry6 from rfl,
          ZMod.val_add_of_lt (by rw [hsum7']; omega), hsum7']
    have eq0 : b0.val + cry0.val * 65536 = ctq0.val + r0.val := by
      obtain ⟨h1, h2⟩ := nof_eq_ctqpr0; rw [hsum01] at h1 h2; clear *- h1 h2; omega
    have eq1 : b1.val + cry1.val * 65536 = ctq1.val + r1.val + cry0.val := by
      obtain ⟨h1, h2⟩ := nof_eq_ctqpr1; rw [hsum1] at h1 h2; clear *- h1 h2; omega
    have eq2 : b2.val + cry2.val * 65536 = ctq2.val + r2.val + cry1.val := by
      obtain ⟨h1, h2⟩ := nof_eq_ctqpr2; rw [hsum2] at h1 h2; clear *- h1 h2; omega
    have eq3 : b3.val + cry3.val * 65536 = ctq3.val + r3.val + cry2.val := by
      obtain ⟨h1, h2⟩ := nof_eq_ctqpr3; rw [hsum3] at h1 h2; clear *- h1 h2; omega
    have eq4 : (msb_b * 65535).val + cry4.val * 65536 =
        ctq4.val + (msb_rem * 65535).val + cry3.val := by
      have h1 := nof_eq_ctqpr4.1; have h2 := nof_eq_ctqpr4.2
      rw [hsum4] at h1 h2; clear *- h1 h2; omega
    have eq5 : (msb_b * 65535).val + cry5.val * 65536 =
        ctq5.val + (msb_rem * 65535).val + cry4.val := by
      have h1 := nof_eq_ctqpr5.1; have h2 := nof_eq_ctqpr5.2
      rw [hsum5] at h1 h2; clear *- h1 h2; omega
    have eq6 : (msb_b * 65535).val + cry6.val * 65536 =
        ctq6.val + (msb_rem * 65535).val + cry5.val := by
      have h1 := nof_eq_ctqpr6.1; have h2 := nof_eq_ctqpr6.2
      rw [hsum6] at h1 h2; clear *- h1 h2; omega
    have eq7 : (msb_b * 65535).val + cry7.val * 65536 =
        ctq7.val + (msb_rem * 65535).val + cry6.val := by
      have h1 := nof_eq_ctqpr7.1; have h2 := nof_eq_ctqpr7.2
      rw [hsum7] at h1 h2; clear *- h1 h2; omega
    have main_eq :
        b0.val + b1.val * 65536 + b2.val * 4294967296 + b3.val * 281474976710656 +
          (msb_b * 65535).val * 18446744073709551616 +
          (msb_b * 65535).val * 1208925819614629174706176 +
          (msb_b * 65535).val * 79228162514264337593543950336 +
          (msb_b * 65535).val * 5192296858534827628530496329220096 +
          cry7.val * 340282366920938463463374607431768211456 =
        ctq0.val + ctq1.val * 65536 + ctq2.val * 4294967296 +
          ctq3.val * 281474976710656 + ctq4.val * 18446744073709551616 +
          ctq5.val * 1208925819614629174706176 +
          ctq6.val * 79228162514264337593543950336 +
          ctq7.val * 5192296858534827628530496329220096 +
        (r0.val + r1.val * 65536 + r2.val * 4294967296 +
          r3.val * 281474976710656 +
          (msb_rem * 65535).val * 18446744073709551616 +
          (msb_rem * 65535).val * 1208925819614629174706176 +
          (msb_rem * 65535).val * 79228162514264337593543950336 +
          (msb_rem * 65535).val * 5192296858534827628530496329220096) := by
      clear *- eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7; omega
    have dctq : DWord.toBitVec128
        (#v[ctq0, ctq1, ctq2, ctq3, ctq4, ctq5, ctq6, ctq7] : DWord (ZMod p)) =
      BitVec.ofNat 128
        (ctq0.val + ctq1.val * 65536 + ctq2.val * 4294967296 +
          ctq3.val * 281474976710656 + ctq4.val * 18446744073709551616 +
          ctq5.val * 1208925819614629174706176 +
          ctq6.val * 79228162514264337593543950336 +
          ctq7.val * 5192296858534827628530496329220096) := by
      simp [DWord.toBitVec128, DWord.toNat]
    have db : DWord.toBitVec128
        (#v[b0, b1, b2, b3, msb_b * 65535, msb_b * 65535, msb_b * 65535,
            msb_b * 65535] : DWord (ZMod p)) =
      BitVec.ofNat 128
        (b0.val + b1.val * 65536 + b2.val * 4294967296 +
          b3.val * 281474976710656 +
          (msb_b * 65535).val * 18446744073709551616 +
          (msb_b * 65535).val * 1208925819614629174706176 +
          (msb_b * 65535).val * 79228162514264337593543950336 +
          (msb_b * 65535).val * 5192296858534827628530496329220096) := by
      simp [DWord.toBitVec128, DWord.toNat]
    have dr : DWord.toBitVec128
        (#v[r0, r1, r2, r3, msb_rem * 65535, msb_rem * 65535, msb_rem * 65535,
            msb_rem * 65535] : DWord (ZMod p)) =
      BitVec.ofNat 128
        (r0.val + r1.val * 65536 + r2.val * 4294967296 +
          r3.val * 281474976710656 +
          (msb_rem * 65535).val * 18446744073709551616 +
          (msb_rem * 65535).val * 1208925819614629174706176 +
          (msb_rem * 65535).val * 79228162514264337593543950336 +
          (msb_rem * 65535).val * 5192296858534827628530496329220096) := by
      simp [DWord.toBitVec128, DWord.toNat]
    rw [db, dctq, dr]
    simp only [← _root_.BitVec.toNat_inj, DivRem.BitVec.toNat_ofNat_128,
      DivRem.BitVec.toNat_add_128]
    rw [show (340282366920938463463374607431768211456 : ℕ) = divrem_N128 from by
      rw [divrem_N128_eq]; decide] at main_eq
    exact div_rem_close_helper
      b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val
      ctq0.val ctq1.val ctq2.val ctq3.val
      ctq4.val ctq5.val ctq6.val ctq7.val
      (msb_b * 65535).val (msb_rem * 65535).val
      cry7.val main_eq

end divrem_h_prod_helper

end DivRem
