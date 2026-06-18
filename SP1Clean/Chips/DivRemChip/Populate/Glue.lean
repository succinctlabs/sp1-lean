import SP1Clean.Chips.DivRemChip.Populate.Bounds

/-! # `DivRemChip` populate value bundles — the `c_times_quotient` ↔ `MulOperation` glue

Ingredients for the eight glue equalities at the populate values: the low/high four `populateCtq`
limbs, viewed as words, are exactly the low/high 64-bit slices of the 128-bit product
`quotient_comp · c` (`ctqLo_eq_*`/`ctqHi_eq_*`), and `MulOperation.semantic_populate` pins the
populated product struct's `resultWord` to the same slices — so the per-limb glue follows from
limb-uniqueness of `isU64` words (`word_eq_of_toBitVec64_eq`). -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

set_option linter.unusedSectionVars false in
/-- Two `isU64` words with the same 64-bit value are equal (per-limb base-2^16 uniqueness). -/
lemma word_eq_of_toBitVec64_eq {w w' : Word (ZMod p)} (hw : Word.isU64 w) (hw' : Word.isU64 w')
    (h : Word.toBitVec64 w = Word.toBitVec64 w') : w = w' := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hw
  obtain ⟨g0, g1, g2, g3⟩ := Word.lt_cases_of_isU64 hw'
  have hn : Word.toNat w = Word.toNat w' := by
    have := congrArg BitVec.toNat h
    rwa [Word.toBitVec64_toNat hw, Word.toBitVec64_toNat hw'] at this
  rw [Word.toNat_def, Word.toNat_def] at hn
  apply Vector.ext; intro i hi
  interval_cases i <;> exact ZMod.val_injective _ (by omega)

/-- `wordOfBits` round-trips through `toBitVec64`. -/
lemma wordOfBits_toBitVec64 (x : BitVec 64) : Word.toBitVec64 (wordOfBits (p := p) x) = x := by
  have hx := x.isLt
  have hn : Word.toNat (wordOfBits (p := p) x) = x.toNat := by
    rw [Word.toNat_def, wordOfBits, wordOfNat_val _ 0 (by norm_num),
      wordOfNat_val _ 1 (by norm_num), wordOfNat_val _ 2 (by norm_num),
      wordOfNat_val _ 3 (by norm_num)]
    omega
  rw [← BitVec.toNat_inj, Word.toBitVec64_toNat (wordOfBits_isU64 x), hn]

/-- The 128-bit sign-extended product truncates to the wrapping 64-bit product. -/
private lemma setWidth_signExtend_mul (x y : BitVec 64) :
    (x.signExtend 128 * y.signExtend 128).setWidth 64 = x * y := by
  have hself : ∀ z : BitVec 64, (z.signExtend 128).setWidth 64 = z := by
    intro z
    rw [← BitVec.toNat_inj, BitVec.toNat_setWidth, BitVec.toNat_signExtend]
    have hz : z.toNat < 2 ^ 64 := z.isLt
    rcases Bool.eq_false_or_eq_true z.msb with h | h <;> rw [h] <;> simp <;> omega
  rw [BitVec.setWidth_mul _ _ (by norm_num), hself, hself]

/-- The 128-bit zero-extended product truncates to the wrapping 64-bit product. -/
private lemma setWidth_setWidth_mul (x y : BitVec 64) :
    (x.setWidth 128 * y.setWidth 128).setWidth 64 = x * y := by
  rw [BitVec.setWidth_mul _ _ (by norm_num), BitVec.setWidth_setWidth, BitVec.setWidth_eq,
    BitVec.setWidth_setWidth, BitVec.setWidth_eq]
  all_goals omega

/-- In **every** flag class, the 128-bit `ctqProd` truncates to the wrapping product
`quotient_comp · c` — the low four `populateCtq` limbs never see the sign choice. -/
lemma ctqProd_setWidth (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (ctqProd B C f).setWidth 64
      = Word.toBitVec64 (populateQuotComp B C f) * Word.toBitVec64 (cComp C f) := by
  unfold ctqProd
  split
  · exact setWidth_signExtend_mul _ _
  · exact setWidth_setWidth_mul _ _

/-- The low four `populateCtq` limbs, as a word: the wrapping product `quotient_comp · c`. -/
lemma ctqLo_eq (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (#v[(populateCtq B C f)[0], (populateCtq B C f)[1],
        (populateCtq B C f)[2], (populateCtq B C f)[3]] : Word (ZMod p))
      = wordOfBits (Word.toBitVec64 (populateQuotComp B C f) * Word.toBitVec64 (cComp C f)) := by
  rw [← ctqProd_setWidth B C f]
  have hP := (ctqProd B C f).isLt
  apply Vector.ext; intro i hi
  have hval : ∀ k (hk : k < 4),
      ((wordOfBits (p := p) ((ctqProd B C f).setWidth 64))[k]'hk).val
        = (ctqProd B C f).toNat / 2 ^ (16 * k) % 2 ^ 16 := by
    intro k hk
    rw [wordOfBits, wordOfNat_val _ k hk, BitVec.toNat_setWidth]
    interval_cases k <;> omega
  interval_cases i <;>
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      apply ZMod.val_injective
      rw [populateCtq_val B C f _ (by norm_num), hval _ (by norm_num), ctqLimbNat]

/-- The high four `populateCtq` limbs, as a word: the high 64-bit slice of `ctqProd`. -/
lemma ctqHi_eq (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (#v[(populateCtq B C f)[4], (populateCtq B C f)[5],
        (populateCtq B C f)[6], (populateCtq B C f)[7]] : Word (ZMod p))
      = wordOfBits ((ctqProd B C f >>> 64).setWidth 64) := by
  have hP := (ctqProd B C f).isLt
  apply Vector.ext; intro i hi
  have hval : ∀ k (hk : k < 4),
      ((wordOfBits (p := p) ((ctqProd B C f >>> 64).setWidth 64))[k]'hk).val
        = (ctqProd B C f).toNat / 2 ^ (16 * (4 + k)) % 2 ^ 16 := by
    intro k hk
    rw [wordOfBits, wordOfNat_val _ k hk, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    have hdd : (ctqProd B C f).toNat / 2 ^ 64 / 2 ^ (16 * k)
        = (ctqProd B C f).toNat / 2 ^ (16 * (4 + k)) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, show 64 + 16 * k = 16 * (4 + k) from by omega]
    have hmod : (ctqProd B C f).toNat / 2 ^ 64 % 2 ^ 64 = (ctqProd B C f).toNat / 2 ^ 64 :=
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hP))
    rw [hmod, hdd]
  interval_cases i <;>
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      apply ZMod.val_injective
      rw [populateCtq_val B C f _ (by norm_num), hval _ (by norm_num), ctqLimbNat]

end SP1Clean.DivRemChip
