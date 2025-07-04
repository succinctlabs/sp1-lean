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
