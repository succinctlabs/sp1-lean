import SP1Clean.Proofs.Chips.DivRemChip.Populate

/-! # `DivRemChip` populate value bundles — limb bounds

The `< 2^16` / boolean facts about the populate functions that feed the completeness proof's
byte-range pulls and `isU64` obligations: every `wordOfNat`/`wordOfBits` limb is a u16 by
construction, the eight `populateCtq` limbs are u16 residues, the eight `populateCarry` entries
are boolean (the chain adds two u16s and a boolean carry), and the `U16MSBOperation.populate_msb`
cells are boolean on u16 limbs. -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Every `wordOfNat` limb value is its u16 residue (the cast is below `p`). -/
lemma wordOfNat_val (n : ℕ) (i : ℕ) (hi : i < 4) :
    ((wordOfNat (p := p) n)[i]'hi).val = n / 2 ^ (16 * i) % 2 ^ 16 := by
  have hp : 2 ^ 24 < p := Fact.out
  interval_cases i <;>
    · simp only [wordOfNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      rw [ZMod.val_natCast_of_lt (by omega)]
      try omega

/-- Every `wordOfNat` limb is `< 2^16`. -/
lemma wordOfNat_val_lt (n : ℕ) (i : ℕ) (hi : i < 4) :
    ((wordOfNat (p := p) n)[i]'hi).val < 2 ^ 16 := by
  rw [wordOfNat_val n i hi]; exact Nat.mod_lt _ (by norm_num)

/-- `wordOfNat` words are `isU64`. -/
lemma wordOfNat_isU64 (n : ℕ) : Word.isU64 (wordOfNat (p := p) n) :=
  Word.isU64_of_cases (wordOfNat_val_lt n 0 (by norm_num)) (wordOfNat_val_lt n 1 (by norm_num))
    (wordOfNat_val_lt n 2 (by norm_num)) (wordOfNat_val_lt n 3 (by norm_num))

/-- `wordOfBits` words are `isU64`. -/
lemma wordOfBits_isU64 (x : BitVec 64) : Word.isU64 (wordOfBits (p := p) x) :=
  wordOfNat_isU64 x.toNat

/-- The committed `quotient` is `isU64` (unconditionally — it is a `wordOfBits`). -/
lemma populateQuotient_isU64 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Word.isU64 (populateQuotient B C f) := wordOfBits_isU64 _

/-- The committed `remainder` is `isU64`. -/
lemma populateRemainder_isU64 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Word.isU64 (populateRemainder B C f) := wordOfBits_isU64 _

/-- The committed `quotient_comp` is `isU64`. -/
lemma populateQuotComp_isU64 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Word.isU64 (populateQuotComp B C f) := wordOfBits_isU64 _

/-- The committed `remainder_comp` is `isU64`. -/
lemma populateRemComp_isU64 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Word.isU64 (populateRemComp B C f) := wordOfBits_isU64 _

omit [Fact p.Prime] in
/-- A four-limb literal word is `isU64` as soon as each limb's value is a u16. The shared
`#v[…]`-getElem reduction behind `zeroWord_isU64` / `oneWord_isU64` / `signFill_isU64` /
`zeroFill_isU64`. -/
private lemma vecLit_isU64 {a b c d : ZMod p} (ha : a.val < 2 ^ 16) (hb : b.val < 2 ^ 16)
    (hc : c.val < 2 ^ 16) (hd : d.val < 2 ^ 16) :
    Word.isU64 (#v[a, b, c, d] : Word (ZMod p)) := by
  apply Word.isU64_of_cases <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    assumption

/-- The zero word is `isU64`. -/
lemma zeroWord_isU64 : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
  vecLit_isU64 (by simp) (by simp) (by simp) (by simp)

/-- The committed result `a` is `isU64` (all three branches). -/
lemma populateA_isU64 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Word.isU64 (populateA B C f) := by
  unfold populateA
  split
  · exact populateQuotient_isU64 B C f
  · split
    exacts [populateRemainder_isU64 B C f, zeroWord_isU64]

/-- A sign-fill word `#v[x, y, m·65535, m·65535]` is `isU64` for u16 `x`/`y` and boolean `m`. -/
private lemma signFill_isU64 {x y m : ZMod p} (hx : x.val < 2 ^ 16) (hy : y.val < 2 ^ 16)
    (hm : m = 0 ∨ m = 1) :
    Word.isU64 (#v[x, y, m * 65535, m * 65535] : Word (ZMod p)) := by
  have h65535 : ((m * 65535 : ZMod p)).val < 2 ^ 16 := by
    rcases hm with h | h <;> rw [h]
    · rw [zero_mul, ZMod.val_zero]; norm_num
    · rw [one_mul, val_65535_zmod_p]; norm_num
  exact vecLit_isU64 hx hy h65535 h65535

/-- A zero-extension word `#v[x, y, 0, 0]` is `isU64` for u16 `x`/`y`. -/
private lemma zeroFill_isU64 {x y : ZMod p} (hx : x.val < 2 ^ 16) (hy : y.val < 2 ^ 16) :
    Word.isU64 (#v[x, y, 0, 0] : Word (ZMod p)) :=
  vecLit_isU64 hx hy (by simp) (by simp)

/-- The committed operand `b` is `isU64` given the raw read is. -/
lemma bComp_isU64 {B : Word (ZMod p)} (hB : B.isU64) (f : Vector (ZMod p) 8) :
    Word.isU64 (bComp B f) := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hB
  unfold bComp
  split
  · exact signFill_isU64 h0 h1 (U16MSBOperation.populate_msb_bool h1)
  · split
    exacts [zeroFill_isU64 h0 h1, hB]

/-- The committed operand `c` is `isU64` given the raw read is. -/
lemma cComp_isU64 {C : Word (ZMod p)} (hC : C.isU64) (f : Vector (ZMod p) 8) :
    Word.isU64 (cComp C f) := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hC
  unfold cComp
  split
  · exact signFill_isU64 h0 h1 (U16MSBOperation.populate_msb_bool h1)
  · split
    exacts [zeroFill_isU64 h0 h1, hC]

/-- The committed `abs_c` is `isU64` given the raw read is. -/
lemma populateAbsC_isU64 {C : Word (ZMod p)} (hC : C.isU64) (f : Vector (ZMod p) 8) :
    Word.isU64 (populateAbsC C f) := by
  unfold populateAbsC
  split
  exacts [wordOfBits_isU64 _, cComp_isU64 hC f]

/-- The committed `abs_remainder` is `isU64`. -/
lemma populateAbsRem_isU64 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Word.isU64 (populateAbsRem B C f) := by
  unfold populateAbsRem
  split
  exacts [wordOfBits_isU64 _, populateRemComp_isU64 B C f]

/-- The word `#v[1, 0, 0, 0]` is `isU64`. -/
private lemma oneWord_isU64 : Word.isU64 (#v[1, 0, 0, 0] : Word (ZMod p)) :=
  vecLit_isU64 (by rw [ZMod.val_one]; norm_num) (by simp) (by simp) (by simp)

/-- The committed `max_abs_c_or_1` is `isU64` given the raw read is. -/
lemma populateMaxAbsCOr1_isU64 {C : Word (ZMod p)} (hC : C.isU64) (f : Vector (ZMod p) 8) :
    Word.isU64 (populateMaxAbsCOr1 C f) := by
  have heq : populateMaxAbsCOr1 C f
      = if Word.toNat (populateAbsC C f) = 0 then #v[1, 0, 0, 0] else populateAbsC C f := rfl
  rw [heq]
  split
  exacts [oneWord_isU64, populateAbsC_isU64 hC f]

/-- Each `populateCtq` limb value is its u16 residue. -/
lemma populateCtq_val (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) (i : ℕ) (hi : i < 8) :
    ((populateCtq B C f)[i]'hi).val = ctqLimbNat B C f i := by
  have hp : 2 ^ 24 < p := Fact.out
  have hlt : ctqLimbNat B C f i < 2 ^ 16 := Nat.mod_lt _ (by norm_num)
  simp only [populateCtq, Vector.getElem_ofFn]
  rw [ZMod.val_natCast_of_lt (by omega)]

/-- Each `populateCtq` limb is `< 2^16`. -/
lemma populateCtq_val_lt (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) (i : ℕ) (hi : i < 8) :
    ((populateCtq B C f)[i]'hi).val < 2 ^ 16 := by
  rw [populateCtq_val B C f i hi]; exact Nat.mod_lt _ (by norm_num)

/-- The MSB witness cells are boolean given the raw reads are `isU64`. -/
lemma bMsbCell_bool {B : Word (ZMod p)} (hB : B.isU64) (f : Vector (ZMod p) 8) :
    bMsbCell B f = 0 ∨ bMsbCell B f = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hB
  unfold bMsbCell
  split
  exacts [U16MSBOperation.populate_msb_bool h1, U16MSBOperation.populate_msb_bool h3]

/-- As `bMsbCell_bool`, for `c`. -/
lemma cMsbCell_bool {C : Word (ZMod p)} (hC : C.isU64) (f : Vector (ZMod p) 8) :
    cMsbCell C f = 0 ∨ cMsbCell C f = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hC
  unfold cMsbCell
  split
  exacts [U16MSBOperation.populate_msb_bool h1, U16MSBOperation.populate_msb_bool h3]

/-- The remainder MSB cell is boolean (the populated remainder is always `isU64`). -/
lemma remMsbCell_bool (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    remMsbCell B C f = 0 ∨ remMsbCell B C f = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 (populateRemainder_isU64 B C f)
  unfold remMsbCell
  split
  exacts [U16MSBOperation.populate_msb_bool h1, U16MSBOperation.populate_msb_bool h3]

/-- The quotient MSB cell is boolean. -/
lemma quotMsbCell_bool (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    quotMsbCell B C f = 0 ∨ quotMsbCell B C f = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 (populateQuotient_isU64 B C f)
  unfold quotMsbCell
  split
  exacts [U16MSBOperation.populate_msb_bool h1, Or.inl rfl]

/-- The sign/neg cells are boolean given the signed-class flag sum is. -/
lemma populateRemNeg_bool (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hsig : f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1) :
    populateRemNeg B C f = 0 ∨ populateRemNeg B C f = 1 := by
  unfold populateRemNeg
  rcases hsig with h | h
  · rw [h, zero_mul]; exact Or.inl rfl
  · rw [h, one_mul]; exact remMsbCell_bool B C f

/-- As `populateRemNeg_bool`, for `b_neg`. -/
lemma populateBNeg_bool {B : Word (ZMod p)} (hB : B.isU64) {f : Vector (ZMod p) 8}
    (hsig : f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1) :
    populateBNeg B f = 0 ∨ populateBNeg B f = 1 := by
  unfold populateBNeg
  rcases hsig with h | h
  · rw [h, zero_mul]; exact Or.inl rfl
  · rw [h, one_mul]; exact bMsbCell_bool hB f

/-- As `populateRemNeg_bool`, for `c_neg`. -/
lemma populateCNeg_bool {C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (hsig : f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1) :
    populateCNeg C f = 0 ∨ populateCNeg C f = 1 := by
  unfold populateCNeg
  rcases hsig with h | h
  · rw [h, zero_mul]; exact Or.inl rfl
  · rw [h, one_mul]; exact cMsbCell_bool hC f

/-- The remainder carry-chain addend limbs are `< 2^16` (low limbs are `remainder_comp` u16s; the
sign-fill limbs are `rem_neg · 65535` with a boolean `rem_neg`). -/
lemma remAddendNat_lt (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hsig : f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1) (i : ℕ) :
    remAddendNat B C f i < 2 ^ 16 := by
  unfold remAddendNat
  split
  · next h =>
    have := wordOfNat_val_lt (p := p) (remCompBits B C f).toNat i h
    simpa [populateRemComp, wordOfBits] using this
  · rcases populateRemNeg_bool B C hsig with h | h <;> rw [h] <;> simp [ZMod.val_one]

/-- Every chain carry is boolean (ℕ form): two u16 addends plus a boolean carry stay below
`2 · 2^16`, so the quotient by `2^16` is at most `1`. -/
lemma carryNat_le_one (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hsig : f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1) (i : ℕ) :
    carryNat B C f i ≤ 1 := by
  have hctq : ∀ j, ctqLimbNat B C f j < 2 ^ 16 := fun _ => Nat.mod_lt _ (by norm_num)
  induction i with
  | zero => have := hctq 0; have := remAddendNat_lt B C hsig 0; unfold carryNat; omega
  | succ n ih =>
    have := hctq (n + 1); have := remAddendNat_lt B C hsig (n + 1); unfold carryNat; omega

/-- The generic u16 `Range` byte-table row: every `is_real`-gated pull in the chip's byte tail is a
width-16 `Range` row on a populate value with a known `< 2^16` bound. -/
theorem byteRow_range16 {x : ZMod p} (h : x.val < 2 ^ 16) :
    ByteRowSpec (⟨6, x, 16, 0⟩ : ByteRow (ZMod p)) := by
  simpa only [Nat.cast_ofNat] using (byteRowSpec_range x sixteen_lt).mpr h

/-- Every committed carry cell is boolean. -/
lemma populateCarry_bool (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hsig : f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1) (i : ℕ) (hi : i < 8) :
    (populateCarry B C f)[i]'hi = 0 ∨ (populateCarry B C f)[i]'hi = 1 := by
  have h := carryNat_le_one B C hsig i
  simp only [populateCarry, Vector.getElem_ofFn]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h <;> rw [h] <;> norm_num

end SP1Clean.DivRemChip
