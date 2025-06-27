import Mathlib

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
