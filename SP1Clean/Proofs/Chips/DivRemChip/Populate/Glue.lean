import SP1Clean.Proofs.Chips.DivRemChip.Populate.Bounds
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Shapes
import SP1Clean.Proofs.Operations.MulOperation.Formal

/-! # `DivRemChip` populate value bundles — the `c_times_quotient` ↔ `MulOperation` glue

Ingredients for the eight glue equalities at the populate values: the low/high four `populateCtq`
limbs, viewed as words, are exactly the low/high 64-bit slices of the 128-bit product
`quotient_comp · c` (`ctqLo_eq_*`/`ctqHi_eq_*`), and `MulOperation.semantic_populate` pins the
populated product struct's `resultWord` to the same slices — so the per-limb glue follows from
limb-uniqueness of `isU64` words (`word_eq_of_toBitVec64_eq`). -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

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
    rcases Bool.eq_false_or_eq_true z.msb with h | h
    · rw [h]; simp; omega
    · rw [h]; simp
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

/-- On a real row, each low `c_times_quotient` limb is the corresponding pair of bytes in the
lower-product witness.  Kept opaque so the whole-chip completeness proof does not accumulate the
semantic Mul argument and its populated record in its proof term. -/
lemma populateMulLower_product_pair (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (ir : ZMod p) (hcU : Word.isU64 C) :
    ir = 1 → ∀ (k : ℕ) (hk : k < 4),
      (populateCtq B C f)[k]'(by omega)
        = (populateMulLower ir B C f).product[2 * k]'(by omega)
          + (populateMulLower ir B C f).product[2 * k + 1]'(by omega) * 256 := by
  intro h1 k hk
  rw [populateMulLower, if_pos h1]
  have hloU : Word.isU64 (#v[(populateCtq B C f)[0], (populateCtq B C f)[1],
      (populateCtq B C f)[2], (populateCtq B C f)[3]] : Word (ZMod p)) := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] <;>
      exact populateCtq_val_lt B C f _ (by norm_num)
  have hsem := MulOperation.semantic_populate (populateQuotComp_isU64 B C f)
    (cComp_isU64 hcU f) 1 0 0 0 0 (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    (Or.inl rfl) (Or.inr (by norm_num))
  obtain ⟨hru, hmul, -, -, -, -⟩ := hsem
  have hword := word_eq_of_toBitVec64_eq hloU hru (by
    rw [ctqLo_eq, wordOfBits_toBitVec64]
    exact (hmul rfl).symm)
  simp [MulOperation.resultWord, MulOperation.productVal] at hword
  obtain ⟨w0, w1, w2, w3⟩ := hword
  interval_cases k <;> assumption

/-- On a real division row, each high `c_times_quotient` limb is the corresponding pair of bytes in
the upper-product witness.  The one-hot flag facts choose the signed or unsigned Mul semantics. -/
lemma populateMulUpper_product_pair (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (ir : ZMod p) (hcU : Word.isU64 C)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    ir = 1 → f[0] + f[1] + f[2] + f[3] = 1 → ∀ (k : ℕ) (hk : k < 4),
      (populateCtq B C f)[4 + k]'(by omega)
        = (populateMulUpper ir B C f).product[8 + 2 * k]'(by omega)
          + (populateMulUpper ir B C f).product[8 + 2 * k + 1]'(by omega) * 256 := by
  intro h1 hg k hk
  rw [populateMulUpper, if_pos ⟨h1, hg⟩]
  have hhiU : Word.isU64 (#v[(populateCtq B C f)[4], (populateCtq B C f)[5],
      (populateCtq B C f)[6], (populateCtq B C f)[7]] : Word (ZMod p)) := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] <;>
      exact populateCtq_val_lt B C f _ (by norm_num)
  have hsigned : f[0] + f[2] = 1 → f[0] + f[2] + f[4] + f[5] = 1 →
      (populateCtq B C f)[4 + k]'(by omega)
        = (MulOperation.populate (populateQuotComp B C f) (cComp C f)
            (f[0] + f[2]) 0 0).product[8 + 2 * k]'(by omega)
          + (MulOperation.populate (populateQuotComp B C f) (cComp C f)
              (f[0] + f[2]) 0 0).product[8 + 2 * k + 1]'(by omega) * 256 := by
    intro hs hsg
    rw [hs]
    have hsem := MulOperation.semantic_populate (populateQuotComp_isU64 B C f)
      (cComp_isU64 hcU f) 0 1 0 0 0 (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inr (by norm_num))
    obtain ⟨hru, -, -, hmulh, -, -⟩ := hsem
    have hword := word_eq_of_toBitVec64_eq hhiU hru (by
      rw [ctqHi_eq, wordOfBits_toBitVec64]
      refine Eq.trans ?_ (hmulh rfl).symm
      simp [ctqProd, hsg])
    simp [MulOperation.resultWord, MulOperation.productVal] at hword
    obtain ⟨w0, w1, w2, w3⟩ := hword
    interval_cases k <;> assumption
  have hunsigned : f[0] + f[2] = 0 → f[0] + f[2] + f[4] + f[5] = 0 →
      (populateCtq B C f)[4 + k]'(by omega)
        = (MulOperation.populate (populateQuotComp B C f) (cComp C f)
            (f[0] + f[2]) 0 0).product[8 + 2 * k]'(by omega)
          + (MulOperation.populate (populateQuotComp B C f) (cComp C f)
              (f[0] + f[2]) 0 0).product[8 + 2 * k + 1]'(by omega) * 256 := by
    intro hs hsg
    rw [hs]
    have hsem := MulOperation.semantic_populate (populateQuotComp_isU64 B C f)
      (cComp_isU64 hcU f) 0 0 1 0 0 (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inr (by norm_num))
    obtain ⟨hru, -, hmulhu, -, -, -⟩ := hsem
    have hword := word_eq_of_toBitVec64_eq hhiU hru (by
      rw [ctqHi_eq, wordOfBits_toBitVec64]
      refine Eq.trans ?_ (hmulhu rfl).symm
      simp [ctqProd, hsg])
    simp [MulOperation.resultWord, MulOperation.productVal] at hword
    obtain ⟨w0, w1, w2, w3⟩ := hword
    interval_cases k <;> assumption
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with
      h | h | h | h | h | h | h | h
  all_goals obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := h
  · exact hsigned (by rw [g0, g2]; norm_num) (by rw [g0, g2, g4, g5]; norm_num)
  · exact hunsigned (by rw [g0, g2]; norm_num) (by rw [g0, g2, g4, g5]; norm_num)
  · exact hsigned (by rw [g0, g2]; norm_num) (by rw [g0, g2, g4, g5]; norm_num)
  · exact hunsigned (by rw [g0, g2]; norm_num) (by rw [g0, g2, g4, g5]; norm_num)
  all_goals
    rw [g0, g1, g2, g3] at hg
    norm_num at hg

/-- Every committed product limb is zero on SP1's canonical DivRem padding template. -/
lemma populateCtq_padding (k : ℕ) (hk : k < 8) :
    (populateCtq (#v[0, 0, 0, 0] : Word (ZMod p)) #v[1, 0, 0, 0]
      #v[0, 1, 0, 0, 0, 0, 0, 0])[k]'hk = 0 := by
  have hb0 : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0 := by
    simp [Word.toBitVec64, Word.toNat]
  have hc1 : Word.toBitVec64 (#v[1, 0, 0, 0] : Word (ZMod p)) = 1 := by
    simp [Word.toBitVec64, Word.toNat, ZMod.val_one]
  have hqb : quotBits (#v[0, 0, 0, 0] : Word (ZMod p)) #v[1, 0, 0, 0]
      #v[0, 1, 0, 0, 0, 0, 0, 0] = 0 := by
    simp only [quotBits, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    rw [hb0, hc1, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
      if_neg (by decide)]
    decide
  have hqc : populateQuotComp (#v[0, 0, 0, 0] : Word (ZMod p)) #v[1, 0, 0, 0]
      #v[0, 1, 0, 0, 0, 0, 0, 0] = wordOfBits 0 := by
    simp only [populateQuotComp, quotCompBits, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    rw [if_neg (by norm_num), hqb]
  have hprod : ctqProd (#v[0, 0, 0, 0] : Word (ZMod p)) #v[1, 0, 0, 0]
      #v[0, 1, 0, 0, 0, 0, 0, 0] = 0 := by
    simp only [ctqProd, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    rw [if_neg (by norm_num), hqc, wordOfBits_toBitVec64]
    simp
  simp [populateCtq, ctqLimbNat, hprod]

/-- Equality-oriented wrapper for applying `populateCtq_padding` without unfolding the large
populate term in a parent theorem. -/
lemma populateCtq_padding_of_eq {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hB : B = #v[0, 0, 0, 0]) (hC : C = #v[1, 0, 0, 0])
    (hf : f = #v[0, 1, 0, 0, 0, 0, 0, 0]) (k : ℕ) (hk : k < 8) :
    (populateCtq B C f)[k]'hk = 0 := by
  subst B C f
  exact populateCtq_padding k hk

/-- Program-row form of the padding lemma, consuming the canonical padding-template contract in
one opaque application. -/
lemma populateCtq_padding_of_template {ir : ZMod p} {B C : Word (ZMod p)}
    {f : Vector (ZMod p) 8}
    (hpad : ir = 0 → B = #v[0, 0, 0, 0] ∧ C = #v[1, 0, 0, 0] ∧
      f = #v[0, 1, 0, 0, 0, 0, 0, 0]) :
    ir = 0 → ∀ (k : ℕ) (hk : k < 8), (populateCtq B C f)[k]'hk = 0 := by
  intro h0 k hk
  obtain ⟨hB, hC, hf⟩ := hpad h0
  exact populateCtq_padding_of_eq hB hC hf k hk

end SP1Clean.DivRemChip
