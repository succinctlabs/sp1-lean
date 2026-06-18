import SP1Clean.Chips.DivRemChip.Populate.Bounds
import SP1Clean.Chips.DivRemChip.Populate.Glue
import SP1Clean.Chips.DivRemChip.Soundness

/-! # `DivRemChip` populate value bundles — the overflow block and the remainder-sign conditions

Value-level facts about the populate functions feeding two own-assert groups:

* **E105–E119** (the `is_overflow`-gated quotient/remainder pins): `populateIsOverflow` is boolean
  and gated off non-real rows; when it fires, the operands are exactly the overflow pair
  (`intMin`, `allOnes` — full-width on the 64-bit classes, low-32 on the W-classes), and the
  populated quotient/remainder are the wrap values `b` / `0` (`overflow_eq_one_*` /
  `overflow_quotient_*`).
* **E225/E228** (the remainder-sign conditions): the populated remainder carries the dividend's
  sign or is zero — `remNeg_imp_bNeg` (E225, implication and product forms) and
  `rem_nonzero_nonneg_imp_bNonneg` (E228, product form). The `BitVec.srem` sign facts come from
  the core case-definition lemmas (`BitVec.msb_srem`, `BitVec.intMin_sdiv_neg_one`,
  `BitVec.srem_zero_of_dvd`).

The flag hypotheses are taken in the class-trichotomy form `FlagClasses` (signed-64 / signed-word
/ unsigned), derivable from per-flag booleans + the one-hot sum via `flagClassTrichotomy`. -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## Small field constants -/

/-- `32768 = 2^15` casts cleanly (the cast is below `p`). -/
lemma val_32768_zmod_p : ((32768 : ZMod p)).val = 32768 := by
  have hp := Fact.out (p := 2 ^ 24 < p)
  exact ZMod.val_natCast_of_lt (show (32768 : ℕ) < p by omega)

/-! ## `BitVec.sdiv`/`srem` case-definition facts

The wrap case `intMin / -1` and the truncated-remainder sign, width-generic. The `srem` sign facts
are direct consequences of core's `BitVec.msb_srem`
(`(x.srem y).msb = (x.msb && decide (x.srem y ≠ 0))`). -/

/-- `intMin.sdiv allOnes = intMin` — the wrapping `i64::MIN / -1` case. -/
lemma intMin_sdiv_allOnes {w : ℕ} :
    (BitVec.intMin w).sdiv (BitVec.allOnes w) = BitVec.intMin w := by
  rw [← BitVec.neg_one_eq_allOnes]
  exact BitVec.intMin_sdiv_neg_one

/-- `intMin.srem allOnes = 0` — the wrapping `i64::MIN % -1` case (`-1` divides everything). -/
lemma intMin_srem_allOnes {w : ℕ} (hw : 0 < w) :
    (BitVec.intMin w).srem (BitVec.allOnes w) = 0 := by
  apply BitVec.srem_zero_of_dvd
  rw [BitVec.toInt_allOnes, if_pos hw]
  exact ⟨-(BitVec.intMin w).toInt, by ring⟩

/-- `srem` keeps a nonnegative dividend nonnegative. -/
lemma srem_msb_false_of_msb_false {w : ℕ} {x : BitVec w} (y : BitVec w)
    (hx : x.msb = false) : (x.srem y).msb = false := by
  rw [BitVec.msb_srem, hx, Bool.false_and]

/-- The truncated signed remainder of a negative dividend is zero or negative. -/
lemma srem_eq_zero_or_msb_of_msb {w : ℕ} {x : BitVec w} (y : BitVec w)
    (hx : x.msb = true) : x.srem y = 0 ∨ (x.srem y).msb = true := by
  by_cases hz : x.srem y = 0
  · exact Or.inl hz
  · right
    rw [BitVec.msb_srem, hx, Bool.true_and]
    exact decide_eq_true hz

/-- `allOnes ≠ 0` on a positive width. -/
lemma allOnes_ne_zero {w : ℕ} (hw : 0 < w) : BitVec.allOnes w ≠ 0 := by
  intro h
  have h' := congrArg BitVec.toNat h
  have h0 : (0 : BitVec w).toNat = 0 := by simp
  rw [BitVec.toNat_allOnes, h0] at h'
  have h2 : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  omega

/-- Sign-extending the zero word gives zero. -/
lemma signExtend_zero32 : (0 : BitVec 32).signExtend 64 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_signExtend, if_neg (by simp)]
  simp

/-- The 64-bit sign extension of `intMin 32` is `0xFFFFFFFF80000000`. -/
lemma toNat_signExtend_intMin32 :
    ((BitVec.intMin 32).signExtend 64).toNat = 2 ^ 64 - 2 ^ 31 := by
  have hmsb : (BitVec.intMin 32).msb = true := by rw [BitVec.msb_intMin]; rfl
  rw [BitVec.toNat_signExtend, if_pos hmsb, BitVec.toNat_setWidth,
    BitVec.toNat_intMin_of_pos (by norm_num)]
  omega

/-- u16 limb 1 of a sign-extended 32-bit value is `≥ 2^15` when the value is negative. -/
lemma signExtend_toNat_limb1_ge {x : BitVec 32} (hm : x.msb = true) :
    32768 ≤ (x.signExtend 64).toNat / 2 ^ 16 % 2 ^ 16 := by
  have hx := x.isLt
  have hge := BitVec.le_toNat_of_msb_true hm
  rw [BitVec.toNat_signExtend, if_pos hm, BitVec.toNat_setWidth]
  omega

/-- u16 limb 1 of a sign-extended 32-bit value is `< 2^15` when the value is nonnegative. -/
lemma signExtend_toNat_limb1_lt {x : BitVec 32} (hm : x.msb = false) :
    (x.signExtend 64).toNat / 2 ^ 16 % 2 ^ 16 < 32768 := by
  have hlt := BitVec.toNat_lt_of_msb_false hm
  rw [BitVec.toNat_signExtend, if_neg (by rw [hm]; exact Bool.false_ne_true),
    BitVec.toNat_setWidth]
  omega

/-! ## §1 Result characterizations -/

set_option linter.unusedSectionVars false in
/-- The populated `IsZeroWordOperation` result, in if-form: `1` exactly on the zero word. -/
lemma isZeroWord_populate_result (w : Word (ZMod p)) :
    (IsZeroWordOperation.populate w).result
      = if w[0] = 0 ∧ w[1] = 0 ∧ w[2] = 0 ∧ w[3] = 0 then 1 else 0 := by
  simp only [IsZeroWordOperation.populate, IsZeroOperation.populate]
  by_cases h0 : w[0] = 0 <;> by_cases h1 : w[1] = 0 <;> by_cases h2 : w[2] = 0 <;>
    by_cases h3 : w[3] = 0 <;> simp [h0, h1, h2, h3]

/-- The populated `IsEqualWordOperation` result, in if-form: `1` exactly on limb-wise equality. -/
lemma isEqualWord_populate_result (a b : Word (ZMod p)) :
    (IsEqualWordOperation.populate a b).is_diff_zero.result
      = if a[0] = b[0] ∧ a[1] = b[1] ∧ a[2] = b[2] ∧ a[3] = b[3] then 1 else 0 := by
  simp only [IsEqualWordOperation.populate]
  rw [isZeroWord_populate_result]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, sub_eq_zero]

/-- The witnessed `is_overflow_b` result is boolean (any `ir`, any flags). -/
lemma ovbWitness_result_bool (ir : ZMod p) (B : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (ovbWitness ir B f).is_diff_zero.result = 0
      ∨ (ovbWitness ir B f).is_diff_zero.result = 1 := by
  unfold ovbWitness
  split
  · split <;>
      (rw [isEqualWord_populate_result]; split
       · exact Or.inr rfl
       · exact Or.inl rfl)
  · exact Or.inl rfl

/-- The witnessed `is_overflow_c` result is boolean. -/
lemma ovcWitness_result_bool (ir : ZMod p) (C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (ovcWitness ir C f).is_diff_zero.result = 0
      ∨ (ovcWitness ir C f).is_diff_zero.result = 1 := by
  unfold ovcWitness
  split
  · split <;>
      (rw [isEqualWord_populate_result]; split
       · exact Or.inr rfl
       · exact Or.inl rfl)
  · exact Or.inl rfl

/-- The populated `is_overflow` cell is boolean given the signed-class flag sum is. -/
lemma populateIsOverflow_bool (ir : ZMod p) (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hsig : f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1) :
    populateIsOverflow ir B C f = 0 ∨ populateIsOverflow ir B C f = 1 := by
  unfold populateIsOverflow
  rcases ovbWitness_result_bool ir B f with hb | hb <;>
    rcases ovcWitness_result_bool ir C f with hc | hc <;>
      rcases hsig with hs | hs <;>
        rw [hb, hc, hs] <;>
        simp

set_option linter.unusedSectionVars false in
/-- The populated `is_overflow` cell is zero off the real gate (the gated structs are all-zero). -/
lemma populateIsOverflow_zero_of_not_real {ir : ZMod p} (B C : Word (ZMod p))
    (f : Vector (ZMod p) 8) (h : ir ≠ 1) :
    populateIsOverflow ir B C f = 0 := by
  unfold populateIsOverflow ovbWitness ovcWitness
  rw [if_neg h, if_neg h]
  show (0 : ZMod p) * 0 * _ = 0
  rw [zero_mul, zero_mul]

/-! ## MSB-cell bridges -/

/-- `populate_msb a = 1` iff the high bit of (16-bit) `a` is set. -/
lemma populate_msb_eq_one_iff {a : ZMod p} (ha : a.val < 2 ^ 16) :
    U16MSBOperation.populate_msb a = 1 ↔ 32768 ≤ a.val := by
  unfold U16MSBOperation.populate_msb
  constructor
  · intro h
    by_contra hlt
    rw [show a.val / 32768 = 0 by omega, Nat.cast_zero] at h
    exact zero_ne_one h
  · intro h
    rw [show a.val / 32768 = 1 by omega, Nat.cast_one]

/-- `populate_msb a = 0` iff the high bit of (16-bit) `a` is clear. -/
lemma populate_msb_eq_zero_iff {a : ZMod p} (ha : a.val < 2 ^ 16) :
    U16MSBOperation.populate_msb a = 0 ↔ a.val < 32768 := by
  unfold U16MSBOperation.populate_msb
  constructor
  · intro h
    by_contra hge
    rw [show a.val / 32768 = 1 by omega, Nat.cast_one] at h
    exact one_ne_zero h
  · intro h
    rw [show a.val / 32768 = 0 by omega, Nat.cast_zero]

/-- `populate_msb 32768 = 1`. -/
lemma populate_msb_32768 : U16MSBOperation.populate_msb (32768 : ZMod p) = 1 := by
  unfold U16MSBOperation.populate_msb
  rw [val_32768_zmod_p]
  norm_num

set_option linter.unusedSectionVars false in
/-- The low-32 truncation of an `isU64` word is negative iff limb 1's high bit is set. -/
lemma toBitVec64_setWidth32_msb_iff {w : Word (ZMod p)} (hw : w.isU64) :
    ((Word.toBitVec64 w).setWidth 32).msb = true ↔ 32768 ≤ (w[1]).val := by
  obtain ⟨h0, h1, _, _⟩ := Word.lt_cases_of_isU64 hw
  rw [BitVec.msb_eq_decide, decide_eq_true_eq, BitVec.toNat_setWidth,
    Word.toBitVec64_toNat hw, Word.toNat_def]
  omega

/-- Limb 1 of the populated remainder, at the `remBits` value. -/
lemma populateRemainder_limb1_val (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    ((populateRemainder B C f)[1]).val = (remBits B C f).toNat / 2 ^ 16 % 2 ^ 16 := by
  unfold populateRemainder wordOfBits
  rw [wordOfNat_val _ 1 (by norm_num)]

set_option linter.unusedSectionVars false in
/-- `wordOfBits 0` is the zero word. -/
lemma wordOfBits_zero : wordOfBits (p := p) 0 = #v[0, 0, 0, 0] := by
  simp [wordOfBits, wordOfNat]

/-- The sign-extended word-overflow operand `#v[0, 32768, 65535, 65535]` is `isU64`. -/
private lemma negWord_isU64 :
    Word.isU64 (#v[0, 32768, 65535, 65535] : Word (ZMod p)) := by
  apply Word.isU64_of_cases <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    first
      | (rw [ZMod.val_zero]; norm_num)
      | (rw [val_32768_zmod_p]; norm_num)
      | (rw [val_65535_zmod_p]; norm_num)

/-! ## §2 The overflow case (E105–E119) -/

/-- `is_overflow = 1` on a 64-bit signed class pins the raw-read limbs to the overflow pair
`(i64::MIN, -1)`. -/
private lemma overflow_limbs_64 {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hsig64 : f[0] + f[2] = 1) (hw4 : f[4] = 0) (hw5 : f[5] = 0) (hw6 : f[6] = 0)
    (hw7 : f[7] = 0) (hov : populateIsOverflow 1 B C f = 1) :
    (B[0] = 0 ∧ B[1] = 0 ∧ B[2] = 0 ∧ B[3] = (32768 : ZMod p))
      ∧ (C[0] = (65535 : ZMod p) ∧ C[1] = 65535 ∧ C[2] = 65535 ∧ C[3] = 65535) := by
  have hW : ¬(f[4] + f[5] + f[6] + f[7] = 1) := by
    rw [hw4, hw5, hw6, hw7, add_zero, add_zero, add_zero]
    exact zero_ne_one
  have hsig : f[0] + f[2] + f[4] + f[5] = 1 := by
    rw [hw4, hw5, add_zero, add_zero]
    exact hsig64
  unfold populateIsOverflow ovbWitness ovcWitness at hov
  rw [if_pos rfl, if_pos rfl, if_neg hW, if_neg hW, hsig, mul_one,
    isEqualWord_populate_result, isEqualWord_populate_result] at hov
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at hov
  by_cases hPb : B[0] = 0 ∧ B[1] = 0 ∧ B[2] = 0 ∧ B[3] = (32768 : ZMod p)
  · by_cases hPc : C[0] = (65535 : ZMod p) ∧ C[1] = 65535 ∧ C[2] = 65535 ∧ C[3] = 65535
    · exact ⟨hPb, hPc⟩
    · rw [if_pos hPb, if_neg hPc, one_mul] at hov
      exact absurd hov zero_ne_one
  · rw [if_neg hPb, zero_mul] at hov
    exact absurd hov zero_ne_one

/-- **E105–E119, 64-bit operand pin**: on a 64-bit signed class, `is_overflow = 1` forces
`b = i64::MIN` and `c = -1` as 64-bit values. -/
lemma overflow_eq_one_64 {B C : Word (ZMod p)} (hB : B.isU64) (hC : C.isU64)
    {f : Vector (ZMod p) 8} (hsig64 : f[0] + f[2] = 1) (hw4 : f[4] = 0) (hw5 : f[5] = 0)
    (hw6 : f[6] = 0) (hw7 : f[7] = 0) (hov : populateIsOverflow 1 B C f = 1) :
    Word.toBitVec64 B = BitVec.intMin 64 ∧ Word.toBitVec64 C = BitVec.allOnes 64 := by
  obtain ⟨⟨hb0, hb1, hb2, hb3⟩, ⟨hc0, hc1, hc2, hc3⟩⟩ :=
    overflow_limbs_64 hsig64 hw4 hw5 hw6 hw7 hov
  constructor
  · rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hB, Word.toNat_def, hb0, hb1, hb2, hb3,
      ZMod.val_zero, val_32768_zmod_p, BitVec.toNat_intMin_of_pos (by norm_num)]
    omega
  · rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hC, Word.toNat_def, hc0, hc1, hc2, hc3,
      val_65535_zmod_p, BitVec.toNat_allOnes]
    omega

/-- **E105–E119, 64-bit value pin**: on the 64-bit overflow row the populated quotient is the
committed operand `b` and the populated remainder is the zero word. -/
lemma overflow_quotient_64 {B C : Word (ZMod p)} (hB : B.isU64) (hC : C.isU64)
    {f : Vector (ZMod p) 8} (hsig64 : f[0] + f[2] = 1) (hw4 : f[4] = 0) (hw5 : f[5] = 0)
    (hw6 : f[6] = 0) (hw7 : f[7] = 0) (hov : populateIsOverflow 1 B C f = 1) :
    populateQuotient B C f = bComp B f ∧ populateRemainder B C f = #v[0, 0, 0, 0] := by
  obtain ⟨hb, hc⟩ := overflow_eq_one_64 hB hC hsig64 hw4 hw5 hw6 hw7 hov
  have h45 : ¬(f[4] + f[5] = 1) := by rw [hw4, hw5, add_zero]; exact zero_ne_one
  have h67 : ¬(f[6] + f[7] = 1) := by rw [hw6, hw7, add_zero]; exact zero_ne_one
  have hcne : Word.toBitVec64 C ≠ 0 := by
    rw [hc]
    exact allOnes_ne_zero (by norm_num)
  constructor
  · have hquot : quotBits B C f = BitVec.intMin 64 := by
      simp only [quotBits]
      rw [if_neg h45, if_neg h67, if_pos hsig64, if_neg hcne, hb, hc, intMin_sdiv_allOnes]
    have hbComp : bComp B f = B := by
      simp only [bComp]
      rw [if_neg h45, if_neg h67]
    rw [hbComp]
    unfold populateQuotient
    rw [hquot]
    exact word_eq_of_toBitVec64_eq (wordOfBits_isU64 _) hB (by rw [wordOfBits_toBitVec64, hb])
  · have hrem : remBits B C f = 0 := by
      simp only [remBits]
      rw [if_neg h45, if_neg h67, if_pos hsig64, if_neg hcne, hb, hc,
        intMin_srem_allOnes (by norm_num)]
    unfold populateRemainder
    rw [hrem]
    exact wordOfBits_zero

/-- `is_overflow = 1` on the signed-word class pins the low raw-read limbs to the 32-bit
overflow pair `(i32::MIN, -1)`. -/
private lemma overflow_limbs_word {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0) (hf2 : f[2] = 0) (hw6 : f[6] = 0) (hw7 : f[7] = 0)
    (hsigW : f[4] + f[5] = 1) (hov : populateIsOverflow 1 B C f = 1) :
    (B[0] = 0 ∧ B[1] = (32768 : ZMod p))
      ∧ (C[0] = (65535 : ZMod p) ∧ C[1] = 65535) := by
  have hW : f[4] + f[5] + f[6] + f[7] = 1 := by
    rw [hw6, hw7, add_zero, add_zero]
    exact hsigW
  have hsig : f[0] + f[2] + f[4] + f[5] = 1 := by
    rw [hf0, hf2, zero_add, zero_add]
    exact hsigW
  unfold populateIsOverflow ovbWitness ovcWitness at hov
  rw [if_pos rfl, if_pos rfl, if_pos hW, if_pos hW, hsig, mul_one,
    isEqualWord_populate_result, isEqualWord_populate_result] at hov
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, and_true] at hov
  by_cases hPb : B[0] = 0 ∧ B[1] = (32768 : ZMod p)
  · by_cases hPc : C[0] = (65535 : ZMod p) ∧ C[1] = 65535
    · exact ⟨hPb, hPc⟩
    · rw [if_pos hPb, if_neg hPc, one_mul] at hov
      exact absurd hov zero_ne_one
  · rw [if_neg hPb, zero_mul] at hov
    exact absurd hov zero_ne_one

/-- **E105–E119, W-variant operand pin**: on the signed-word class, `is_overflow = 1` forces
`b as u32 = i32::MIN` and `c as u32 = -1`. -/
lemma overflow_eq_one_word {B C : Word (ZMod p)} (hB : B.isU64) (hC : C.isU64)
    {f : Vector (ZMod p) 8} (hf0 : f[0] = 0) (hf2 : f[2] = 0) (hw6 : f[6] = 0)
    (hw7 : f[7] = 0) (hsigW : f[4] + f[5] = 1) (hov : populateIsOverflow 1 B C f = 1) :
    (Word.toBitVec64 B).setWidth 32 = BitVec.intMin 32
      ∧ (Word.toBitVec64 C).setWidth 32 = BitVec.allOnes 32 := by
  obtain ⟨⟨hb0, hb1⟩, hc0, hc1⟩ := overflow_limbs_word hf0 hf2 hw6 hw7 hsigW hov
  constructor
  · rw [← BitVec.toNat_inj, BitVec.toNat_setWidth, Word.toBitVec64_toNat hB, Word.toNat_def,
      hb0, hb1, ZMod.val_zero, val_32768_zmod_p, BitVec.toNat_intMin_of_pos (by norm_num)]
    omega
  · rw [← BitVec.toNat_inj, BitVec.toNat_setWidth, Word.toBitVec64_toNat hC, Word.toNat_def,
      hc0, hc1, val_65535_zmod_p, BitVec.toNat_allOnes]
    omega

/-- **E105–E119, W-variant value pin**: on the signed-word overflow row the populated quotient is
the committed (sign-extended) operand `b` and the populated remainder is the zero word. -/
lemma overflow_quotient_word {B C : Word (ZMod p)} (hB : B.isU64) (hC : C.isU64)
    {f : Vector (ZMod p) 8} (hf0 : f[0] = 0) (hf2 : f[2] = 0) (hw6 : f[6] = 0)
    (hw7 : f[7] = 0) (hsigW : f[4] + f[5] = 1) (hov : populateIsOverflow 1 B C f = 1) :
    populateQuotient B C f = bComp B f ∧ populateRemainder B C f = #v[0, 0, 0, 0] := by
  obtain ⟨⟨hb0, hb1⟩, _, _⟩ := overflow_limbs_word hf0 hf2 hw6 hw7 hsigW hov
  obtain ⟨hsw, hcw⟩ := overflow_eq_one_word hB hC hf0 hf2 hw6 hw7 hsigW hov
  have hcne : (Word.toBitVec64 C).setWidth 32 ≠ 0 := by
    rw [hcw]
    exact allOnes_ne_zero (by norm_num)
  constructor
  · have hquot : quotBits B C f = (BitVec.intMin 32).signExtend 64 := by
      simp only [quotBits]
      rw [if_pos hsigW, if_neg hcne, hsw, hcw, intMin_sdiv_allOnes]
    have hbc : bComp B f = #v[B[0], B[1], U16MSBOperation.populate_msb B[1] * 65535,
        U16MSBOperation.populate_msb B[1] * 65535] := by
      simp only [bComp]
      rw [if_pos hsigW]
    have hmsb1 : U16MSBOperation.populate_msb B[1] = 1 := by
      rw [hb1]
      exact populate_msb_32768
    unfold populateQuotient
    rw [hquot, hbc, hmsb1, one_mul, hb0, hb1]
    apply word_eq_of_toBitVec64_eq (wordOfBits_isU64 _) negWord_isU64
    rw [wordOfBits_toBitVec64, ← BitVec.toNat_inj, toNat_signExtend_intMin32,
      Word.toBitVec64_toNat negWord_isU64, Word.toNat_def]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero, val_32768_zmod_p, val_65535_zmod_p]
    norm_num
  · have hrem : remBits B C f = 0 := by
      simp only [remBits]
      rw [if_pos hsigW, if_neg hcne, hsw, hcw, intMin_srem_allOnes (by norm_num),
        signExtend_zero32]
    unfold populateRemainder
    rw [hrem]
    exact wordOfBits_zero

/-! ## §3 Remainder-sign conditions (E225/E228) -/

/-- The flag-class trichotomy the sign lemmas case on: signed 64-bit (`div`/`rem`), signed word
(`divw`/`remw`), or unsigned (the signed-class sum is `0`). Derivable from per-flag booleans + the
one-hot sum via `flagClassTrichotomy`. -/
abbrev FlagClasses (f : Vector (ZMod p) 8) : Prop :=
  (f[0] + f[2] = 1 ∧ f[4] = 0 ∧ f[5] = 0 ∧ f[6] = 0 ∧ f[7] = 0)
    ∨ (f[4] + f[5] = 1 ∧ f[0] = 0 ∧ f[2] = 0 ∧ f[6] = 0 ∧ f[7] = 0)
    ∨ f[0] + f[2] + f[4] + f[5] = 0

/-- One-hot flags fall into the three sign classes. -/
lemma flagClassTrichotomy {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    FlagClasses f := by
  have hp : 2 ^ 24 < p := Fact.out
  have key : ∀ x : ZMod p, x = 0 ∨ x = 1 → ∃ v : ℕ, v ≤ 1 ∧ x = (v : ZMod p) := by
    rintro x (rfl | rfl)
    · exact ⟨0, by norm_num, by norm_num⟩
    · exact ⟨1, le_refl 1, by norm_num⟩
  obtain ⟨v0, hv0le, hv0⟩ := key _ hf0
  obtain ⟨v1, hv1le, hv1⟩ := key _ hf1
  obtain ⟨v2, hv2le, hv2⟩ := key _ hf2
  obtain ⟨v3, hv3le, hv3⟩ := key _ hf3
  obtain ⟨v4, hv4le, hv4⟩ := key _ hf4
  obtain ⟨v5, hv5le, hv5⟩ := key _ hf5
  obtain ⟨v6, hv6le, hv6⟩ := key _ hf6
  obtain ⟨v7, hv7le, hv7⟩ := key _ hf7
  have hcast : ((v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 : ℕ) : ZMod p) = 1 := by
    push_cast
    rw [← hv0, ← hv1, ← hv2, ← hv3, ← hv4, ← hv5, ← hv6, ← hv7]
    exact hsum
  have hval : v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 = 1 := by
    have h := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_one] at h
  rcases show (v0 + v2 = 1 ∧ v4 = 0 ∧ v5 = 0 ∧ v6 = 0 ∧ v7 = 0)
      ∨ (v4 + v5 = 1 ∧ v0 = 0 ∧ v2 = 0 ∧ v6 = 0 ∧ v7 = 0)
      ∨ (v0 = 0 ∧ v2 = 0 ∧ v4 = 0 ∧ v5 = 0) by omega with h | h | h
  · exact Or.inl ⟨by rw [hv0, hv2, ← Nat.cast_add, h.1, Nat.cast_one],
      by rw [hv4, h.2.1, Nat.cast_zero], by rw [hv5, h.2.2.1, Nat.cast_zero],
      by rw [hv6, h.2.2.2.1, Nat.cast_zero], by rw [hv7, h.2.2.2.2, Nat.cast_zero]⟩
  · exact Or.inr (Or.inl ⟨by rw [hv4, hv5, ← Nat.cast_add, h.1, Nat.cast_one],
      by rw [hv0, h.2.1, Nat.cast_zero], by rw [hv2, h.2.2.1, Nat.cast_zero],
      by rw [hv6, h.2.2.2.1, Nat.cast_zero], by rw [hv7, h.2.2.2.2, Nat.cast_zero]⟩)
  · refine Or.inr (Or.inr ?_)
    rw [hv0, hv2, hv4, hv5, h.1, h.2.1, h.2.2.1, h.2.2.2]
    norm_num

set_option linter.unusedSectionVars false in
/-- The signed-class flag sum is boolean in every class. -/
lemma sig_bool_of_class {f : Vector (ZMod p) 8} (hclass : FlagClasses f) :
    f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1 := by
  rcases hclass with ⟨hcl, h4, h5, _, _⟩ | ⟨hcl, h0, h2, _, _⟩ | hcl
  · right; rw [h4, h5, add_zero, add_zero]; exact hcl
  · right; rw [h0, h2, zero_add, zero_add]; exact hcl
  · left; exact hcl

/-- `rem_neg = 0` on the unsigned classes. -/
lemma populateRemNeg_zero_of_unsigned (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (h : f[0] + f[2] + f[4] + f[5] = 0) : populateRemNeg B C f = 0 := by
  unfold populateRemNeg
  rw [h, zero_mul]

set_option linter.unusedSectionVars false in
/-- `b_neg = 0` on the unsigned classes. -/
lemma populateBNeg_zero_of_unsigned (B : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (h : f[0] + f[2] + f[4] + f[5] = 0) : populateBNeg B f = 0 := by
  unfold populateBNeg
  rw [h, zero_mul]

set_option linter.unusedSectionVars false in
/-- `c_neg = 0` on the unsigned classes. -/
lemma populateCNeg_zero_of_unsigned (C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (h : f[0] + f[2] + f[4] + f[5] = 0) : populateCNeg C f = 0 := by
  unfold populateCNeg
  rw [h, zero_mul]

/-- **E225 at the populate** (implication form): a negative populated remainder forces a negative
dividend — truncated remainders carry the dividend's sign. -/
lemma remNeg_imp_bNeg {B C : Word (ZMod p)} (hB : B.isU64) {f : Vector (ZMod p) 8}
    (hclass : FlagClasses f) :
    populateRemNeg B C f = 1 → populateBNeg B f = 1 := by
  intro hrn
  obtain ⟨_, hB1, _, hB3⟩ := Word.lt_cases_of_isU64 hB
  obtain ⟨_, hR1, _, hR3⟩ := Word.lt_cases_of_isU64 (populateRemainder_isU64 B C f)
  rcases hclass with ⟨hcl, h4, h5, h6, h7⟩ | ⟨hcl, h0, h2, h6, h7⟩ | hcl
  · -- signed 64-bit class
    have hsig : f[0] + f[2] + f[4] + f[5] = 1 := by
      rw [h4, h5, add_zero, add_zero]; exact hcl
    have hWne : ¬(f[4] + f[5] + f[6] + f[7] = 1) := by
      rw [h4, h5, h6, h7, add_zero, add_zero, add_zero]; exact zero_ne_one
    have hrneg : populateRemNeg B C f
        = U16MSBOperation.populate_msb (populateRemainder B C f)[3] := by
      unfold populateRemNeg remMsbCell
      rw [hsig, one_mul, if_neg hWne]
    have hbneg : populateBNeg B f = U16MSBOperation.populate_msb B[3] := by
      unfold populateBNeg bMsbCell
      rw [hsig, one_mul, if_neg hWne]
    rw [hrneg] at hrn
    rw [hbneg]
    have hTB : Word.toBitVec64 (populateRemainder B C f) = remBits B C f := by
      unfold populateRemainder
      exact wordOfBits_toBitVec64 _
    have hrmsb : (remBits B C f).msb = true := by
      rw [← hTB]
      exact (toBitVec64_msb_iff (populateRemainder_isU64 B C f)).mpr
        ((populate_msb_eq_one_iff hR3).mp hrn)
    have hbr : remBits B C f = if Word.toBitVec64 C = 0 then Word.toBitVec64 B
        else (Word.toBitVec64 B).srem (Word.toBitVec64 C) := by
      simp only [remBits]
      rw [if_neg (by rw [h4, h5, add_zero]; exact zero_ne_one),
        if_neg (by rw [h6, h7, add_zero]; exact zero_ne_one), if_pos hcl]
    rw [hbr] at hrmsb
    have hbmsb : (Word.toBitVec64 B).msb = true := by
      by_cases hc0 : Word.toBitVec64 C = 0
      · rwa [if_pos hc0] at hrmsb
      · rw [if_neg hc0] at hrmsb
        rcases Bool.eq_false_or_eq_true (Word.toBitVec64 B).msb with hb | hb
        · exact hb
        · rw [srem_msb_false_of_msb_false _ hb] at hrmsb
          exact absurd hrmsb Bool.false_ne_true
    exact (populate_msb_eq_one_iff hB3).mpr ((toBitVec64_msb_iff hB).mp hbmsb)
  · -- signed word class
    have hsig : f[0] + f[2] + f[4] + f[5] = 1 := by
      rw [h0, h2, zero_add, zero_add]; exact hcl
    have hW : f[4] + f[5] + f[6] + f[7] = 1 := by
      rw [h6, h7, add_zero, add_zero]; exact hcl
    have hrneg : populateRemNeg B C f
        = U16MSBOperation.populate_msb (populateRemainder B C f)[1] := by
      unfold populateRemNeg remMsbCell
      rw [hsig, one_mul, if_pos hW]
    have hbneg : populateBNeg B f = U16MSBOperation.populate_msb B[1] := by
      unfold populateBNeg bMsbCell
      rw [hsig, one_mul, if_pos hW]
    rw [hrneg] at hrn
    rw [hbneg]
    have hr1 : 32768 ≤ (remBits B C f).toNat / 2 ^ 16 % 2 ^ 16 := by
      rw [← populateRemainder_limb1_val]
      exact (populate_msb_eq_one_iff hR1).mp hrn
    have hb32 : ((Word.toBitVec64 B).setWidth 32).msb = true := by
      by_cases hc0 : (Word.toBitVec64 C).setWidth 32 = 0
      · have hbr : remBits B C f = ((Word.toBitVec64 B).setWidth 32).signExtend 64 := by
          simp only [remBits]
          rw [if_pos hcl, if_pos hc0]
        rw [hbr] at hr1
        rcases Bool.eq_false_or_eq_true ((Word.toBitVec64 B).setWidth 32).msb with hb | hb
        · exact hb
        · exact absurd hr1 (Nat.not_le.mpr (signExtend_toNat_limb1_lt hb))
      · have hbr : remBits B C f = (((Word.toBitVec64 B).setWidth 32).srem
            ((Word.toBitVec64 C).setWidth 32)).signExtend 64 := by
          simp only [remBits]
          rw [if_pos hcl, if_neg hc0]
        rw [hbr] at hr1
        have hsmsb : (((Word.toBitVec64 B).setWidth 32).srem
            ((Word.toBitVec64 C).setWidth 32)).msb = true := by
          rcases Bool.eq_false_or_eq_true (((Word.toBitVec64 B).setWidth 32).srem
              ((Word.toBitVec64 C).setWidth 32)).msb with hs | hs
          · exact hs
          · exact absurd hr1 (Nat.not_le.mpr (signExtend_toNat_limb1_lt hs))
        rcases Bool.eq_false_or_eq_true ((Word.toBitVec64 B).setWidth 32).msb with hb | hb
        · exact hb
        · rw [srem_msb_false_of_msb_false _ hb] at hsmsb
          exact absurd hsmsb Bool.false_ne_true
    exact (populate_msb_eq_one_iff hB1).mpr ((toBitVec64_setWidth32_msb_iff hB).mp hb32)
  · -- unsigned classes
    rw [populateRemNeg_zero_of_unsigned B C hcl] at hrn
    exact absurd hrn zero_ne_one

/-- **E225 at the populate** (product form): `rem_neg · (b_neg − 1) = 0`. -/
lemma remNeg_mul_bNeg_sub_one {B C : Word (ZMod p)} (hB : B.isU64) {f : Vector (ZMod p) 8}
    (hclass : FlagClasses f) :
    populateRemNeg B C f * (populateBNeg B f - 1) = 0 := by
  rcases populateRemNeg_bool B C (sig_bool_of_class hclass) with h | h
  · rw [h, zero_mul]
  · rw [h, one_mul, remNeg_imp_bNeg hB hclass h, sub_self]

/-- **E228 at the populate** (product form): a nonzero, nonnegative populated remainder forces a
nonnegative dividend — `(Σᵢ remainder[i]) · (1 − rem_neg) · b_neg = 0`. In the live case
(`b_neg = 1`, `rem_neg = 0`) the populated remainder is the zero word, so the limb sum vanishes. -/
lemma rem_nonzero_nonneg_imp_bNonneg {B C : Word (ZMod p)} (hB : B.isU64)
    {f : Vector (ZMod p) 8} (hclass : FlagClasses f) :
    ((populateRemainder B C f)[0] + (populateRemainder B C f)[1]
        + (populateRemainder B C f)[2] + (populateRemainder B C f)[3])
      * (1 - populateRemNeg B C f) * populateBNeg B f = 0 := by
  obtain ⟨_, hB1, _, hB3⟩ := Word.lt_cases_of_isU64 hB
  obtain ⟨_, hR1, _, hR3⟩ := Word.lt_cases_of_isU64 (populateRemainder_isU64 B C f)
  rcases hclass with ⟨hcl, h4, h5, h6, h7⟩ | ⟨hcl, h0, h2, h6, h7⟩ | hcl
  · -- signed 64-bit class
    have hsig : f[0] + f[2] + f[4] + f[5] = 1 := by
      rw [h4, h5, add_zero, add_zero]; exact hcl
    have hWne : ¬(f[4] + f[5] + f[6] + f[7] = 1) := by
      rw [h4, h5, h6, h7, add_zero, add_zero, add_zero]; exact zero_ne_one
    have hrneg : populateRemNeg B C f
        = U16MSBOperation.populate_msb (populateRemainder B C f)[3] := by
      unfold populateRemNeg remMsbCell
      rw [hsig, one_mul, if_neg hWne]
    have hbneg : populateBNeg B f = U16MSBOperation.populate_msb B[3] := by
      unfold populateBNeg bMsbCell
      rw [hsig, one_mul, if_neg hWne]
    rcases U16MSBOperation.populate_msb_bool hB3 with hb | hb
    · rw [hbneg, hb, mul_zero]
    rcases U16MSBOperation.populate_msb_bool hR3 with hr | hr
    · -- the live case: b negative, remainder nonnegative ⇒ remainder = 0
      have hbmsb : (Word.toBitVec64 B).msb = true :=
        (toBitVec64_msb_iff hB).mpr ((populate_msb_eq_one_iff hB3).mp hb)
      have hTB : Word.toBitVec64 (populateRemainder B C f) = remBits B C f := by
        unfold populateRemainder
        exact wordOfBits_toBitVec64 _
      have hrmsb : (remBits B C f).msb = false := by
        rcases Bool.eq_false_or_eq_true (remBits B C f).msb with hm | hm
        · exfalso
          have hge := (toBitVec64_msb_iff (populateRemainder_isU64 B C f)).mp
            (by rw [hTB]; exact hm)
          have hlt := (populate_msb_eq_zero_iff hR3).mp hr
          omega
        · exact hm
      have hbr : remBits B C f = if Word.toBitVec64 C = 0 then Word.toBitVec64 B
          else (Word.toBitVec64 B).srem (Word.toBitVec64 C) := by
        simp only [remBits]
        rw [if_neg (by rw [h4, h5, add_zero]; exact zero_ne_one),
          if_neg (by rw [h6, h7, add_zero]; exact zero_ne_one), if_pos hcl]
      have hzero : remBits B C f = 0 := by
        rw [hbr] at hrmsb ⊢
        by_cases hc0 : Word.toBitVec64 C = 0
        · exfalso
          rw [if_pos hc0, hbmsb] at hrmsb
          exact Bool.false_ne_true hrmsb.symm
        · rw [if_neg hc0] at hrmsb ⊢
          rcases srem_eq_zero_or_msb_of_msb (Word.toBitVec64 C) hbmsb with hz | hm
          · exact hz
          · rw [hm] at hrmsb
            exact absurd hrmsb.symm Bool.false_ne_true
      have hword : populateRemainder B C f = #v[0, 0, 0, 0] := by
        unfold populateRemainder
        rw [hzero]
        exact wordOfBits_zero
      rw [hword]
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, add_zero, zero_mul]
    · rw [hrneg, hr, sub_self, mul_zero, zero_mul]
  · -- signed word class
    have hsig : f[0] + f[2] + f[4] + f[5] = 1 := by
      rw [h0, h2, zero_add, zero_add]; exact hcl
    have hW : f[4] + f[5] + f[6] + f[7] = 1 := by
      rw [h6, h7, add_zero, add_zero]; exact hcl
    have hrneg : populateRemNeg B C f
        = U16MSBOperation.populate_msb (populateRemainder B C f)[1] := by
      unfold populateRemNeg remMsbCell
      rw [hsig, one_mul, if_pos hW]
    have hbneg : populateBNeg B f = U16MSBOperation.populate_msb B[1] := by
      unfold populateBNeg bMsbCell
      rw [hsig, one_mul, if_pos hW]
    rcases U16MSBOperation.populate_msb_bool hB1 with hb | hb
    · rw [hbneg, hb, mul_zero]
    rcases U16MSBOperation.populate_msb_bool hR1 with hr | hr
    · -- the live case on the word class
      have hb32 : ((Word.toBitVec64 B).setWidth 32).msb = true :=
        (toBitVec64_setWidth32_msb_iff hB).mpr ((populate_msb_eq_one_iff hB1).mp hb)
      have hr1lt : (remBits B C f).toNat / 2 ^ 16 % 2 ^ 16 < 32768 := by
        rw [← populateRemainder_limb1_val]
        exact (populate_msb_eq_zero_iff hR1).mp hr
      by_cases hc0 : (Word.toBitVec64 C).setWidth 32 = 0
      · exfalso
        have hbr : remBits B C f = ((Word.toBitVec64 B).setWidth 32).signExtend 64 := by
          simp only [remBits]
          rw [if_pos hcl, if_pos hc0]
        rw [hbr] at hr1lt
        exact absurd hr1lt (Nat.not_lt.mpr (signExtend_toNat_limb1_ge hb32))
      · have hbr : remBits B C f = (((Word.toBitVec64 B).setWidth 32).srem
            ((Word.toBitVec64 C).setWidth 32)).signExtend 64 := by
          simp only [remBits]
          rw [if_pos hcl, if_neg hc0]
        rw [hbr] at hr1lt
        have hinner : ((Word.toBitVec64 B).setWidth 32).srem
            ((Word.toBitVec64 C).setWidth 32) = 0 := by
          rcases srem_eq_zero_or_msb_of_msb ((Word.toBitVec64 C).setWidth 32) hb32 with hz | hm
          · exact hz
          · exact absurd hr1lt (Nat.not_lt.mpr (signExtend_toNat_limb1_ge hm))
        have hword : populateRemainder B C f = #v[0, 0, 0, 0] := by
          unfold populateRemainder
          rw [hbr, hinner, signExtend_zero32]
          exact wordOfBits_zero
        rw [hword]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, add_zero, zero_mul]
    · rw [hrneg, hr, sub_self, mul_zero, zero_mul]
  · -- unsigned classes
    rw [populateBNeg_zero_of_unsigned B hcl, mul_zero]

end SP1Clean.DivRemChip
