import Mathlib
import SP1Foundations.Field

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

lemma and_add_and_mul_bv (x_low x_high y_low y_high : BitVec 32)
    (hx : x_low < 256) (hy : y_low < 256) :
    (x_low &&& y_low) + (x_high &&& y_high) * 256 =
      (x_low + x_high * 256) &&& (y_low + y_high * 256) := by
  bv_decide

lemma or_add_or_mul_bv (x_low x_high y_low y_high : BitVec 32)
    (hx : x_low < 256) (hy : y_low < 256) :
    (x_low ||| y_low) + (x_high ||| y_high) * 256 =
      (x_low + x_high * 256) ||| (y_low + y_high * 256) := by
  bv_decide

lemma xor_add_xor_mul_bv (x_low x_high y_low y_high : BitVec 32)
    (hx : x_low < 256) (hy : y_low < 256) :
    (x_low ^^^ y_low) + (x_high ^^^ y_high) * 256 =
      (x_low + x_high * 256) ^^^ (y_low + y_high * 256) := by
  bv_decide

namespace BabyBear

-- lemma eq_of_bitVec_ofNat_val_eq' (x y : BabyBear) --(n : ℕ)
--     (h : x.val % 4294967296 = y.val % 4294967296) : x = y := by
--   sorry

-- lemma eq_of_bitVec_ofNat_val_eq (x y : BabyBear) (n : ℕ)
--     (h : BitVec.ofNat n x.val = BitVec.ofNat n y.val) : x = y := by
--   sorry

lemma eq_of_bitVec_ofNat32_val_eq' (x y : Fin BabyBearPrime)
    (h : BitVec.ofNat 32 x.val = BitVec.ofNat 32 y.val) : x = y := by
  rw [← BitVec.toNat_inj] at h
  simp only [BabyBearPrime, BitVec.toNat_ofNat, Nat.reducePow] at h
  -- rw [← Fin.val_inj]
  omega

lemma eq_of_bitVec_ofNat32_val_eq (x y : BabyBear)
    (h : BitVec.ofNat 32 x.val = BitVec.ofNat 32 y.val) : x = y := by
  rw [← BitVec.toNat_inj] at h
  simp only [BabyBearPrime, BitVec.toNat_ofNat, Nat.reducePow] at h
  rw [← Fin.val_inj]
  omega

lemma val_add_mul_256 (x y : BabyBear)
    (hx : x.val < 256) (hy : y.val < 256) :
    (x + y * 256).val = x.val + y.val * 256 := by
  rw [Fin.val_add, Fin.val_mul]
  simp
  simp [Fin.lt_iff_val_lt_val] at hx hy
  omega

lemma and_add_and_mul (x_low x_high y_low y_high : BabyBear)
    (hx : x_low < 256) (hy : y_low < 256)
    (hx' : x_high < 256) (hy' : y_high < 256) :
    (x_low &&& y_low) + (x_high &&& y_high) * 256 =
      (x_low + x_high * 256) &&& (y_low + y_high * 256) := by
  apply eq_of_bitVec_ofNat32_val_eq
  rw [val_add_mul_256]
  simp [Fin.lt_iff_val_lt_val] at hx hy
  rw [BitVec.ofNat_add]
  · simp only [BabyBearPrime, Fin.and_val, BitVec.ofNat_and, Fin.isValue]
    rw [val_add_mul_256 _ _ hx hx']
    rw [val_add_mul_256 _ _ hy hy']
    simp [BitVec.ofNat_add, BitVec.ofNat_mul]
    apply and_add_and_mul_bv
    · simp; omega
    · simp; omega
  · simp_all [Fin.lt_iff_val_lt_val]
    refine Nat.and_lt_two_pow (n := 8) ?_ ?_
    omega
  · simp_all [Fin.lt_iff_val_lt_val]
    refine Nat.and_lt_two_pow (n := 8) ?_ ?_
    omega

lemma or_add_or_mul (x_low x_high y_low y_high : BabyBear)
    (hx : x_low < 256) (hy : y_low < 256)
    (hx' : x_high < 256) (hy' : y_high < 256) :
    (x_low ||| y_low) + (x_high ||| y_high) * 256 =
      (x_low + x_high * 256) ||| (y_low + y_high * 256) := by
  apply eq_of_bitVec_ofNat32_val_eq
  rw [val_add_mul_256]
  simp [Fin.lt_iff_val_lt_val] at hx hy hx' hy'
  have hxs : x_low.val + x_high.val * 256 < 65536 := by omega
  have hys : y_low.val + y_high.val * 256 < 65536 := by omega
  rw [BitVec.ofNat_add]
  · simp [Fin.or_val]
    rw [val_add_mul_256 _ _ hx hx']
    rw [val_add_mul_256 _ _ hy hy']

    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    simp [BitVec.ofNat_add, BitVec.ofNat_mul]
    apply or_add_or_mul_bv
    · simp; omega
    · simp; omega
    · have := Nat.or_lt_two_pow (n := 16) hxs hys
      omega
    · have := Nat.or_lt_two_pow (n := 8) hx' hy'
      omega
    · have := Nat.or_lt_two_pow (n := 8) hx hy
      omega
  · simp_all [Fin.lt_iff_val_lt_val]
    rw [Fin.or_val]
    rw [Nat.mod_eq_of_lt]
    apply Nat.or_lt_two_pow (n := 8)
    · omega
    · omega
    have := Nat.or_lt_two_pow (n := 8) hx hy
    omega
  · simp_all [Fin.lt_iff_val_lt_val]
    rw [Fin.or_val]
    rw [Nat.mod_eq_of_lt]
    apply Nat.or_lt_two_pow (n := 8)
    · omega
    · omega
    have := Nat.or_lt_two_pow (n := 8) hx' hy'
    omega

lemma xor_add_xor_mul (x_low x_high y_low y_high : BabyBear)
    (hx : x_low < 256) (hy : y_low < 256)
    (hx' : x_high < 256) (hy' : y_high < 256) :
    (x_low ^^^ y_low) + (x_high ^^^ y_high) * 256 =
      (x_low + x_high * 256) ^^^ (y_low + y_high * 256) := by
  apply eq_of_bitVec_ofNat32_val_eq
  rw [val_add_mul_256]
  simp [Fin.lt_iff_val_lt_val] at hx hy hx' hy'
  have hxs : x_low.val + x_high.val * 256 < 65536 := by omega
  have hys : y_low.val + y_high.val * 256 < 65536 := by omega
  rw [BitVec.ofNat_add]
  · simp [Fin.xor_val]
    rw [val_add_mul_256 _ _ hx hx']
    rw [val_add_mul_256 _ _ hy hy']

    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    simp [BitVec.ofNat_add, BitVec.ofNat_mul]
    apply xor_add_xor_mul_bv
    · simp; omega
    · simp; omega
    · have := Nat.xor_lt_two_pow (n := 16) hxs hys
      omega
    · have := Nat.xor_lt_two_pow (n := 8) hx' hy'
      omega
    · have := Nat.xor_lt_two_pow (n := 8) hx hy
      omega
  · simp_all [Fin.lt_iff_val_lt_val]
    rw [Fin.xor_val]
    rw [Nat.mod_eq_of_lt]
    apply Nat.xor_lt_two_pow (n := 8)
    · omega
    · omega
    have := Nat.xor_lt_two_pow (n := 8) hx hy
    omega
  · simp_all [Fin.lt_iff_val_lt_val]
    rw [Fin.xor_val]
    rw [Nat.mod_eq_of_lt]
    apply Nat.xor_lt_two_pow (n := 8)
    · omega
    · omega
    have := Nat.xor_lt_two_pow (n := 8) hx' hy'
    omega

end BabyBear
