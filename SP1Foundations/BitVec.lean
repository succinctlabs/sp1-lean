import SP1Foundations.Field
import LeanRV64IM.Sail.Sail

@[simp] lemma BitVec.twoPow_65536_32 : 65536#32 = BitVec.twoPow 32 16 := rfl

lemma bitVec_helper_xor' (a b c d : BitVec 32)
    (ha : a < 65536) (hb : b < 65536)
    (hc : c < 65536) (hd : d < 65536) :
    (a + b <<< 16) ^^^ (c + d <<< 16) =
      (a ^^^ c) + (b ^^^ d) <<< 16 := by
  bv_check "BitVec.lean-bitVec_helper_xor'-10-2.lrat"

lemma bitVec_helper_xor (a b c d : ℕ)
    (ha : a < 2^16) (hb : b < 2^16) (hc : c < 2^16) (hd : d < 2^16) :
    let bv_a := BitVec.ofNat 32 a; let bv_b := BitVec.ofNat 32 b
    let bv_c := BitVec.ofNat 32 c; let bv_d := BitVec.ofNat 32 d
    (bv_a + bv_b <<< 16) ^^^ (bv_c + bv_d <<< 16) =
      (bv_a ^^^ bv_c) + (bv_b ^^^ bv_d) <<< 16 := by
  apply bitVec_helper_xor'
  all_goals simp [BitVec.lt_def]; omega

lemma bitVec_helper_or' (a b c d : BitVec 32)
    (ha : a < 65536) (hb : b < 65536)
    (hc : c < 65536) (hd : d < 65536) :
    (a + b <<< 16) ||| (c + d <<< 16) =
      (a ||| c) + (b ||| d) <<< 16 := by
  bv_check "BitVec.lean-bitVec_helper_or'-26-2.lrat"

lemma bitVec_helper_or (a b c d : ℕ)
    (ha : a < 2^16) (hb : b < 2^16) (hc : c < 2^16) (hd : d < 2^16) :
    let bv_a := BitVec.ofNat 32 a; let bv_b := BitVec.ofNat 32 b
    let bv_c := BitVec.ofNat 32 c; let bv_d := BitVec.ofNat 32 d
    (bv_a + bv_b <<< 16) ||| (bv_c + bv_d <<< 16) =
      (bv_a ||| bv_c) + (bv_b ||| bv_d) <<< 16 := by
  apply bitVec_helper_or'
  all_goals simp [BitVec.lt_def]; omega

lemma bitVec_helper_and' (a b c d : BitVec 32)
    (ha : a < 65536) (hb : b < 65536)
    (hc : c < 65536) (hd : d < 65536) :
    (a + b <<< 16) &&& (c + d <<< 16) =
      (a &&& c) + (b &&& d) <<< 16 := by
  bv_check "BitVec.lean-bitVec_helper_and'-42-2.lrat"

lemma bitVec_helper_and (a b c d : ℕ)
    (ha : a < 2^16) (hb : b < 2^16) (hc : c < 2^16) (hd : d < 2^16) :
    let bv_a := BitVec.ofNat 32 a; let bv_b := BitVec.ofNat 32 b
    let bv_c := BitVec.ofNat 32 c; let bv_d := BitVec.ofNat 32 d
    (bv_a + bv_b <<< 16) &&& (bv_c + bv_d <<< 16) =
      (bv_a &&& bv_c) + (bv_b &&& bv_d) <<< 16 := by
  apply bitVec_helper_and'
  all_goals simp [BitVec.lt_def]; omega

lemma and_add_and_mul_bv {x_low x_high y_low y_high : BitVec 32}
    (hx : x_low < 256) (hy : y_low < 256) :
    (x_low &&& y_low) + (x_high &&& y_high) * 256 =
      (x_low + x_high * 256) &&& (y_low + y_high * 256) := by
  bv_decide

lemma or_add_or_mul_bv {x_low x_high y_low y_high : BitVec 32}
    (hx : x_low < 256) (hy : y_low < 256) :
    (x_low ||| y_low) + (x_high ||| y_high) * 256 =
      (x_low + x_high * 256) ||| (y_low + y_high * 256) := by
  bv_decide

lemma xor_add_xor_mul_bv {x_low x_high y_low y_high : BitVec 32}
    (hx : x_low < 256) (hy : y_low < 256) :
    (x_low ^^^ y_low) + (x_high ^^^ y_high) * 256 =
      (x_low + x_high * 256) ^^^ (y_low + y_high * 256) := by
  bv_decide

def BitVec64_of_limbs (x y z w : Fin BB) : BitVec 64 :=
  BitVec.ofNat 64 (x + y * 2^16 + z * 2^32 + w * 2^48)

namespace BabyBear

lemma eq_of_bitVec_ofNat16_val_eq (x y : Fin BB)
    (h : BitVec.ofNat 64 x.val = BitVec.ofNat 64 y.val) : x = y := by
  simp [← BitVec.toNat_inj, BB, BitVec.toNat_ofNat, Nat.reducePow] at h; omega
lemma eq_of_bitVec_ofNat32_val_eq (x y : Fin BB)
    (h : BitVec.ofNat 32 x.val = BitVec.ofNat 32 y.val) : x = y := by
  simp [← BitVec.toNat_inj, BB, BitVec.toNat_ofNat, Nat.reducePow] at h; omega

lemma val_add_mul_256 {x y : Fin BB} (hx : x.val < 2^8) (hy : y.val < 2^8) :
    (x + y * 256).val = x.val + y.val * 256 := by
  simp [Fin.val_add, Fin.val_mul]; omega
lemma val_add_mul_65536 {x y : Fin BB} (hx : x.val < 2^16) (hy : y.val < 2^8) :
    (x + y * 65536).val = x.val + y.val * 65536 := by
  simp [Fin.val_add, Fin.val_mul]; omega

lemma val_add_shiftLeft8 {x y : Fin BB} (hx : x.1 < 2^8) (hy : y.1 < 2^8) :
    (x + y <<< 8).1 = x.1 + y.1 <<< 8 := by
  simp [Fin.val_add]; omega
lemma val_add_shiftLeft16 {x y : Fin BB} (hx : x.1 < 2^16) (hy : y.1 < 2^8) :
    (x + y <<< 16).1 = x.1 + y.1 <<< 16 := by
  simp [Fin.val_add]; omega

lemma and_add_and_mul256 {x_low x_high y_low y_high : Fin BB}
    (hx : x_low < 256) (hy : y_low < 256)
    (hx' : x_high < 256) (hy' : y_high < 256) :
    (x_low &&& y_low) + (x_high &&& y_high) * 256 =
      (x_low + x_high * 256) &&& (y_low + y_high * 256) := by
  apply eq_of_bitVec_ofNat32_val_eq
  simp [Fin.lt_iff_val_lt_val] at hx hy hx' hy'
  have hxs : x_low.val + x_high.val * 256 < 2^16 := by omega
  have hys : y_low.val + y_high.val * 256 < 2^16 := by omega
  have hxy : x_low.1 &&& y_low.1 < 2^8 := Nat.and_lt_two_pow (n := 8) _ hy
  have hxy' : x_high.1 &&& y_high.1 < 2^8 := Nat.and_lt_two_pow (n := 8) _ hy'
  have hxsys : (x_low.1 + x_high.1 * 256) &&& (y_low.1 + y_high.1 * 256) < 2^16 :=
    Nat.and_lt_two_pow (n := 16) _ hys
  have hxy_comb : (x_low &&& y_low).1 < 2 ^ 8 := lt_of_le_of_lt (by simp [Fin.and_val]) hxy
  have hxy_comb' : (x_high &&& y_high).1 < 2 ^ 8 := lt_of_le_of_lt (by simp [Fin.and_val]) hxy'
  simpa [val_add_mul_256 hxy_comb hxy_comb', val_add_mul_256 hx hx',
    val_add_mul_256 hy hy', BitVec.ofNat_add, BitVec.ofNat_mul]
    using and_add_and_mul_bv (by simp; omega) (by simp; omega)

lemma or_add_or_mul256 {x_low x_high y_low y_high : Fin BB}
    (hx : x_low < 256) (hy : y_low < 256)
    (hx' : x_high < 256) (hy' : y_high < 256) :
    (x_low ||| y_low) + (x_high ||| y_high) * 256 =
      (x_low + x_high * 256) ||| (y_low + y_high * 256) := by
  apply eq_of_bitVec_ofNat32_val_eq
  simp [Fin.lt_iff_val_lt_val] at hx hy hx' hy'
  have hxs : x_low.val + x_high.val * 256 < 2^16 := by omega
  have hys : y_low.val + y_high.val * 256 < 2^16 := by omega
  have hxy : x_low.1 ||| y_low.1 < 2^8 := Nat.or_lt_two_pow (n := 8) hx hy
  have hxy' : x_high.1 ||| y_high.1 < 2^8 := Nat.or_lt_two_pow (n := 8) hx' hy'
  have hxsys : (x_low.1 + x_high.1 * 256) ||| (y_low.1 + y_high.1 * 256) < 2^16 :=
    Nat.or_lt_two_pow (n := 16) hxs hys
  have hxy_comb : (x_low ||| y_low).1 < 2 ^ 8 :=
    lt_of_le_of_lt (by simp [Fin.or_val]; omega) hxy
  have hxy_comb' : (x_high ||| y_high).1 < 2 ^ 8 :=
    lt_of_le_of_lt (by simp [Fin.or_val]; omega) hxy'
  simp only [BB_eq, Fin.isValue, val_add_mul_256 hxy_comb hxy_comb', Fin.or_val,
    BitVec.ofNat_add, val_add_mul_256 hx hx', val_add_mul_256 hy hy']
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simpa [BitVec.ofNat_add, BitVec.ofNat_mul] using
    or_add_or_mul_bv (by simp; omega) (by simp; omega)

lemma xor_add_xor_mul256 {x_low x_high y_low y_high : Fin BB}
    (hx : x_low < 256) (hy : y_low < 256)
    (hx' : x_high < 256) (hy' : y_high < 256) :
    (x_low ^^^ y_low) + (x_high ^^^ y_high) * 256 =
      (x_low + x_high * 256) ^^^ (y_low + y_high * 256) := by
  apply eq_of_bitVec_ofNat32_val_eq
  simp [Fin.lt_iff_val_lt_val] at hx hy hx' hy'
  have hxs : x_low.val + x_high.val * 256 < 2^16 := by omega
  have hys : y_low.val + y_high.val * 256 < 2^16 := by omega
  have hxy : x_low.1 ^^^ y_low.1 < 2^8 := Nat.xor_lt_two_pow (n := 8) hx hy
  have hxy' : x_high.1 ^^^ y_high.1 < 2^8 := Nat.xor_lt_two_pow (n := 8) hx' hy'
  have hxsys : (x_low.1 + x_high.1 * 256) ^^^ (y_low.1 + y_high.1 * 256) < 2^16 :=
    Nat.xor_lt_two_pow (n := 16) hxs hys
  have hxy_comb : (x_low ^^^ y_low).1 < 2 ^ 8 :=
    lt_of_le_of_lt (by simp [Fin.xor_val]; omega) hxy
  have hxy_comb' : (x_high ^^^ y_high).1 < 2 ^ 8 :=
    lt_of_le_of_lt (by simp [Fin.xor_val]; omega) hxy'
  simp only [BB_eq, Fin.isValue, val_add_mul_256 hxy_comb hxy_comb', Fin.xor_val,
    BitVec.ofNat_add, val_add_mul_256 hx hx', val_add_mul_256 hy hy']
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simpa [BitVec.ofNat_add, BitVec.ofNat_mul]
    using xor_add_xor_mul_bv (by simp; omega) (by simp; omega)

-- lemma xor_add_xor_mul65536 {x_low x_high y_low y_high : Fin BB}
--     (hx : x_low < 65536) (hy : y_low < 65536)
--     (hx' : x_high < 256) (hy' : y_high < 256) :
--     (x_low ^^^ y_low) + (x_high ^^^ y_high) * 65536 =
--       (x_low + x_high * 65536) ^^^ (y_low + y_high * 65536) := by
--   apply eq_of_bitVec_ofNat32_val_eq
--   simp [Fin.lt_iff_val_lt_val] at hx hy hx' hy'
--   have hxs : x_low.val + x_high.val * 65536 < 2^32 := by omega
--   have hys : y_low.val + y_high.val * 65536 < 2^32 := by omega
--   have hxy : x_low.1 ^^^ y_low.1 < 2^16 := Nat.xor_lt_two_pow (n := 16) hx hy
--   have hxy' : x_high.1 ^^^ y_high.1 < 2^8 := Nat.xor_lt_two_pow (n := 8) hx' hy'
--   have hxsys : (x_low.1 + x_high.1 * 65536) ^^^ (y_low.1 + y_high.1 * 65536) < 2^32 :=
--     Nat.xor_lt_two_pow (n := 32) hxs hys
--   have hxy_comb : (x_low ^^^ y_low).1 < 2 ^ 16 :=
--     lt_of_le_of_lt (by simp [Fin.xor_val]; omega) hxy
--   have hxy_comb' : (x_high ^^^ y_high).1 < 2 ^ 8 :=
--     lt_of_le_of_lt (by simp [Fin.xor_val]; omega) hxy'
--   simp only [BB_eq, Fin.isValue, val_add_mul_65536 hxy_comb hxy_comb', Fin.xor_val,
--     BitVec.ofNat_add, val_add_mul_65536 hx hx', val_add_mul_65536 hy hy']
--   rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt]
--   sorry

end BabyBear

namespace BitVec

theorem useless_signExtend {x : Fin BB} {hx : x.val < 2^12}
  : let bx64 : BitVec 64 := BitVec.ofNatLT x (by linarith)
  bx64 % 4 = (BitVec.signExtend 64 (BitVec.ofNatLT (w := 12) x (by linarith))) % 4
  := by
    extract_lets bx64
    -- The key observation: sign extension preserves the lower bits
    -- and mod 4 only depends on the last 2 bits

    -- First, let's use the fact that x.val < 2^12
    have hx_bb : x.val < BB := x.isLt
    have hx_64 : x.val < 2^64 := by simp [BB] at hx_bb; omega

    -- Now prove using bit representation
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]

    -- The original value as a 64-bit vector
    have h_bx64 : bx64.toNat = x.val := by
      simp [bx64, BitVec.toNat_ofNatLT]

    -- For sign extension, we need to check the MSB of the 12-bit value
    let bx12 : BitVec 12 := BitVec.ofNatLT x.val hx

    -- The value of bx12 is x.val
    have h_bx12 : bx12.toNat = x.val := by
      simp [bx12, BitVec.toNat_ofNatLT]

    -- Key insight: for mod 4, we only care about bits 0 and 1
    -- Sign extension from 12 to 64 bits preserves these bits
    have h_sign_ext : (BitVec.signExtend 64 bx12).toNat % 4 = x.val % 4 := by
      -- Whether MSB is set or not, the lower 2 bits are preserved
      simp only [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
      split_ifs with hmsb
      · -- MSB is true, so we add 2^64 - 2^12
        -- But (2^64 - 2^12) % 4 = 0
        have hsub_mod : (2^64 - 2^12) % 4 = 0 := by norm_num
        rw [Nat.add_mod, hsub_mod, Nat.add_zero]
        -- bx12.toNat % 2^64 = bx12.toNat since bx12.toNat < 2^12 < 2^64
        have : bx12.toNat < 2^64 := by
          rw [h_bx12]
          exact hx_64
        rw [Nat.mod_eq_of_lt this, h_bx12, Nat.mod_mod_of_dvd]
        norm_num
      · -- MSB is false, value unchanged mod 2^64
        simp [Nat.add_zero]
        -- bx12.toNat % 2^64 = bx12.toNat since bx12.toNat < 2^64
        have : bx12.toNat < 2^64 := by
          rw [h_bx12]
          exact hx_64
        -- Now just need to show bx12.toNat % 4 = x.val % 4
        rw [h_bx12]

    -- Use (4 : BitVec 64).toNat = 4
    have h4 : (4 : BitVec 64).toNat = 4 := by simp

    rw [h4]
    -- Now we have x.val % 4 on the LHS
    rw [h_bx64]
    -- And we need to show x.val % 4 = (signExtend 64 (x.val#'hx)).toNat % 4
    -- which is exactly h_sign_ext with bx12 = (x.val#'hx)
    have : bx12 = BitVec.ofNatLT (w := 12) x.val hx := rfl
    rw [← this, ← h_sign_ext]

theorem useless_signExtend_add {x : Fin BB} {hx : x.val < 2^12} {y : BitVec 64}
  : let bx64 : BitVec 64 := BitVec.ofNatLT x (by linarith)
  (y + bx64) % 4 = (y + BitVec.signExtend 64 (BitVec.ofNatLT (w := 12) x (by linarith))) % 4
  := by
    extract_lets bx64
    -- Use the fact that we've already proven bx64 % 4 = signExtend(...) % 4
    have h_base := useless_signExtend (x := x) (hx := hx)
    simp [bx64] at h_base

    -- The key insight: if a % 4 = b % 4, then (y + a) % 4 = (y + b) % 4
    -- Since h_base tells us bx64 % 4 = signExtend(...) % 4, we can substitute

    -- Let's define the sign-extended value for clarity
    let sx := BitVec.signExtend 64 (BitVec.ofNatLT (w := 12) x.val hx)

    -- We know from h_base that bx64 % 4 = sx % 4
    -- We want to show (y + bx64) % 4 = (y + sx) % 4

    -- We'll prove that if two bitvectors are congruent mod 4,
    -- then adding them to any third bitvector preserves congruence mod 4

    -- First, let me state what we need to prove more explicitly
    suffices h_suff : ∀ (a b c : BitVec 64), a % 4 = b % 4 → (c + a) % 4 = (c + b) % 4 by
      exact h_suff bx64 sx y h_base

    -- Now prove the general fact
    intro a b c h_ab
    -- Since a % 4 = b % 4, we know a and b differ by a multiple of 4
    -- So (c + a) and (c + b) also differ by a multiple of 4
    -- Therefore (c + a) % 4 = (c + b) % 4

    -- Let's prove this step by step
    -- We know: a ≡ b (mod 4)
    -- Want: c + a ≡ c + b (mod 4)

    -- Hmm, let me just try bv_decide since this is a concrete property about 64-bit vectors
    bv_decide

theorem helper {a b : BitVec 64}
  (h : (a + b) % 4 = 0)
  : 18446744073709551614#64 &&& (a + b) = a + b
  :=
  by
    bv_decide

theorem mul4_add_is_mul4 {a b : BitVec 64}
  (ha : a % 4 = 0)
  (hb : b % 4 = 0)
  : (a + b) % 4 = 0
  :=
  by
    bv_decide

theorem FinBB_mul4_is_BV_mul4 {x : Fin BB}
  : x % 4 = 0 → (BitVec.ofNatLT (w := 64) x (by have := x.isLt; linarith)) % 4 = 0
  :=
  by
    intro h
    have h' : x.val % 4 = 0 := by simp [Fin.mod_def] at h; exact h
    simp [BitVec.umod_def, BitVec.toNat_ofNatLT, h']

theorem mul4_means_0_1_are_0 {x : BitVec 64}
  (hx : x % 4 = 0)
  : x[0] = false ∧ x[1] = false
  := by
    have hx' : x.toNat % 4 = 0 := by bv_omega
    apply And.intro
    · have hzero : x[0] = x[(0 : Fin 64)] := by
        aesop
      rw [hzero]
      rw [←BitVec.getLsb_eq_getElem x 0]
      clear hzero
      simp [BitVec.getLsb]
      omega
    · have hzero : x[1] = x[(1 : Fin 64)] := by
        aesop
      rw [hzero]
      rw [←BitVec.getLsb_eq_getElem x 1]
      clear hzero
      simp [BitVec.getLsb, Nat.testBit]
      omega

theorem FinBB_mul4_means_LS2B_0
  (x : Fin BB)
  : let vx := (BitVec.ofNatLT (w := 64) x (by have := x.isLt; linarith))
  x % 4 = 0 → vx[0] = false ∧ vx[1] = false
  := by
    extract_lets vx
    intro hx
    simp [vx]
    exact mul4_means_0_1_are_0 (FinBB_mul4_is_BV_mul4 hx)

end BitVec
