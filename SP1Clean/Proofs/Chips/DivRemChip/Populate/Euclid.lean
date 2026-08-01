import SP1Clean.Proofs.Chips.DivRemChip.Populate.Glue
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Shapes

/-! # `DivRemChip` populate value bundles — carry-chain / Euclidean-identity facts

The arithmetic heart of the populate direction: the honest witnesses satisfy the chip's
carry-chain constraints.

* **§1 Chain residues** (`chainResidueNat`, `chain_residue_field_0` … `_7`): the field value of
  each byte-pull operand E123/E127/E131/E135/E139/E143/E147/E151 — the carry-chain residue
  `c_times_quotient[i] + remainder-addend[i] + carry[i-1] - carry[i]·2^16` — is the cast of the
  `< 2^16` natural `chainResidueNat i`, unconditionally (pure `Nat.div_add_mod` bookkeeping on
  `carryNat`).
* **§2 Master Euclidean limb identities** (`EuclidLimbEqs`, `euclid_limbs_{s64,u64,sW,uW}`): on
  each one-hot variant class (no-overflow form for the signed classes, taken as the primitive
  `hnotmin` divisor/dividend exclusion), the chain's eight limb equations against the committed
  operand `b` hold at the populate values — the de-gated own-asserts E154/E157/E160/E163/E167/
  E171/E175/E179. Proved by **route (a)**: one 128-bit aggregate congruence
  `ctqProd + remExtNat ≡ bExtNat (mod 2^128)` per class (the genuine Euclidean identity, via
  `udiv`/`umod` `toNat` facts resp. the `sdiv`/`srem → tdiv`/`tmod` bridge
  `BitVec.toInt_sdiv_of_ne_or_ne` + `Int.mul_tdiv_add_tmod`), transported to the eight limb
  equations by the generic digit-extraction lemma `chain_limbs_of_sum`.
* **§3 Carry top**: the dropped `2^128` overflow is absorbed by `chain_limbs_of_sum`'s top digit
  equation — no separate deliverable. -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## §0 Shared helpers -/

set_option linter.unusedSectionVars false in
/-- `wordOfBits` round-trips through `Word.toNat`. -/
private lemma toNat_wordOfBits (x : BitVec 64) : Word.toNat (wordOfBits (p := p) x) = x.toNat := by
  rw [← Word.toBitVec64_toNat (wordOfBits_isU64 x), wordOfBits_toBitVec64]

/-- `toInt` as `toNat` minus the msb-gated `2^64` (local copy of the `Soundness.lean` private). -/
private lemma toInt_eq_toNat_sub64' (x : BitVec 64) :
    x.toInt = (x.toNat : ℤ) - (if x.msb then 2 ^ 64 else 0) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.msb_eq_decide]
  have hlt : x.toNat < 2 ^ 64 := x.isLt
  split <;> rename_i h <;> simp only [decide_eq_true_eq] at * <;> split <;> omega

/-- As `toInt_eq_toNat_sub64'`, at width 32. -/
private lemma toInt_eq_toNat_sub32' (x : BitVec 32) :
    x.toInt = (x.toNat : ℤ) - (if x.msb then 2 ^ 32 else 0) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.msb_eq_decide]
  have hlt : x.toNat < 2 ^ 32 := x.isLt
  split <;> rename_i h <;> simp only [decide_eq_true_eq] at * <;> split <;> omega

/-- As `toInt_eq_toNat_sub64'`, at width 128. -/
private lemma toInt_eq_toNat_sub128' (x : BitVec 128) :
    x.toInt = (x.toNat : ℤ) - (if x.msb then 2 ^ 128 else 0) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.msb_eq_decide]
  have hlt : x.toNat < 2 ^ 128 := x.isLt
  split <;> rename_i h <;> simp only [decide_eq_true_eq] at * <;> split <;> omega

set_option linter.unusedSectionVars false in
/-- `populate_msb` as an indicator of the high bit of a u16 cell. -/
private lemma populate_msb_eq_ite {a : ZMod p} (ha : a.val < 2 ^ 16) :
    U16MSBOperation.populate_msb a = if 32768 ≤ a.val then 1 else 0 := by
  simp only [U16MSBOperation.populate_msb]
  by_cases h : 32768 ≤ a.val
  · rw [if_pos h, (by omega : a.val / 32768 = 1), Nat.cast_one]
  · rw [if_neg h, (by omega : a.val / 32768 = 0), Nat.cast_zero]

set_option linter.unusedSectionVars false in
/-- The msb cell read off limb 3 of a committed 64-bit word is the word's sign bit. -/
private lemma populate_msb_limb3 (x : BitVec 64) :
    U16MSBOperation.populate_msb ((wordOfBits (p := p) x)[3]) = if x.msb then 1 else 0 := by
  have h3 : ((wordOfBits (p := p) x)[3]).val = x.toNat / 2 ^ 48 % 2 ^ 16 :=
    wordOfNat_val x.toNat 3 (by norm_num)
  have hxlt := x.isLt
  rw [populate_msb_eq_ite (by rw [h3]; exact Nat.mod_lt _ (by norm_num)), h3,
    BitVec.msb_eq_decide]
  rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h | h
  · rw [if_neg (by omega), if_neg (by simp only [decide_eq_true_eq]; omega)]
  · rw [if_pos (by omega), if_pos (by simp only [decide_eq_true_eq]; omega)]

set_option linter.unusedSectionVars false in
/-- The msb cell read off limb 1 of a committed 64-bit word is bit 31 of its low half. -/
private lemma populate_msb_limb1 (x : BitVec 64) :
    U16MSBOperation.populate_msb ((wordOfBits (p := p) x)[1])
      = if 2 ^ 31 ≤ x.toNat % 2 ^ 32 then 1 else 0 := by
  have h1 : ((wordOfBits (p := p) x)[1]).val = x.toNat / 2 ^ 16 % 2 ^ 16 :=
    wordOfNat_val x.toNat 1 (by norm_num)
  rw [populate_msb_eq_ite (by rw [h1]; exact Nat.mod_lt _ (by norm_num)), h1]
  rcases Nat.lt_or_ge (x.toNat % 2 ^ 32) (2 ^ 31) with h | h
  · rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_pos (by omega), if_pos (by omega)]

set_option linter.unusedSectionVars false in
/-- `.val` of a boolean indicator. -/
private lemma val_ite01 {c : Prop} [Decidable c] :
    (if c then (1 : ZMod p) else 0).val = if c then 1 else 0 := by
  split <;> simp [ZMod.val_one]

/-- **The `sdiv`/`srem` → `tdiv`/`tmod` bridge.** Outside the lone wrapping point
`(intMin, allOnes)`, truncated signed division satisfies the Euclidean identity on `toInt`
(`BitVec.toInt_sdiv_of_ne_or_ne` + `BitVec.toInt_srem` + `Int.mul_tdiv_add_tmod`); the divisor-zero
case is included (`tdiv _ 0 = 0`, `tmod _ 0 = _`). -/
private lemma sdiv_srem_toInt_identity {w : ℕ} {b c : BitVec w}
    (hno : b ≠ BitVec.intMin w ∨ c ≠ BitVec.allOnes w) :
    b.toInt = c.toInt * (b.sdiv c).toInt + (b.srem c).toInt := by
  rw [BitVec.toInt_sdiv_of_ne_or_ne b c ?hno', BitVec.toInt_srem]
  · exact (Int.mul_tdiv_add_tmod b.toInt c.toInt).symm
  case hno' =>
    rcases hno with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [BitVec.neg_one_eq_allOnes]; exact h)

/-- A 64-bit value plus an msb-gated `2^128 - 2^64` fill, cast to `ℤ`: the value's `toInt` plus an
msb-gated `2^128` (the sign-extension-to-128-bits bookkeeping of the high chain limbs). -/
private lemma extNat_int64 (v : BitVec 64) {fv : ℕ} (hf : fv = if v.msb then 1 else 0) :
    ((v.toNat + fv * (2 ^ 128 - 2 ^ 64) : ℕ) : ℤ)
      = v.toInt + (if v.msb then (2 : ℤ) ^ 128 else 0) := by
  have hI := toInt_eq_toNat_sub64' v
  have hlt := v.isLt
  subst hf
  by_cases hm : v.msb
  · rw [if_pos hm] at hI ⊢; rw [if_pos hm]; push_cast; omega
  · rw [if_neg hm] at hI ⊢; rw [if_neg hm]; push_cast; omega

/-- As `extNat_int64`, for a sign-extended 32-bit value (the word classes' committed shape). -/
private lemma extNat_int32 (v : BitVec 32) {fv : ℕ} (hf : fv = if v.msb then 1 else 0) :
    (((v.signExtend 64).toNat + fv * (2 ^ 128 - 2 ^ 64) : ℕ) : ℤ)
      = v.toInt + (if v.msb then (2 : ℤ) ^ 128 else 0) := by
  have hI := toInt_eq_toNat_sub32' v
  have hlt := v.isLt
  have hse : (v.signExtend 64).toNat = v.toNat + if v.msb then 2 ^ 64 - 2 ^ 32 else 0 := by
    rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by norm_num)]
  subst hf
  by_cases hm : v.msb
  · rw [if_pos hm] at hI hse ⊢; rw [if_pos hm, hse]; push_cast; omega
  · rw [if_neg hm] at hI hse ⊢; rw [if_neg hm, hse]; push_cast; omega

set_option linter.unusedSectionVars false in
/-- The low-32 truncation of a committed u64 word reads off its two low limbs. -/
private lemma setWidth32_toNat {B : Word (ZMod p)} (hB : B.isU64) :
    ((Word.toBitVec64 B).setWidth 32).toNat = B[0].val + B[1].val * 2 ^ 16 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hB
  rw [BitVec.toNat_setWidth, Word.toBitVec64_toNat hB, Word.toNat_def]; omega

/-- Truncating a sign-extended 32-bit value back to 32 bits recovers its `toNat`. -/
private lemma sext64_toNat_mod32 (y : BitVec 32) :
    (y.signExtend 64).toNat % 2 ^ 32 = y.toNat := by
  have hse : (y.signExtend 64).toNat = y.toNat + if y.msb then 2 ^ 64 - 2 ^ 32 else 0 := by
    rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by norm_num)]
  have hyl := y.isLt
  rw [hse]; split <;> omega

/-! ## §0 Cast identifications (field cell = cast of its defining natural) -/

/-- `populateCtq` limb `i` is the cast of `ctqLimbNat i`. -/
private lemma populateCtq_cast (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (i : ℕ) (hi : i < 8) :
    (populateCtq B C f)[i]'hi = ((ctqLimbNat B C f i : ℕ) : ZMod p) := by
  rw [← populateCtq_val B C f i hi, ZMod.natCast_zmod_val]

set_option linter.unusedSectionVars false in
/-- `populateCarry` cell `i` is the cast of `carryNat i`. -/
private lemma populateCarry_cast (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (i : ℕ) (hi : i < 8) :
    (populateCarry B C f)[i]'hi = ((carryNat B C f i : ℕ) : ZMod p) := by
  simp only [populateCarry, Vector.getElem_ofFn]

set_option linter.unusedSectionVars false in
/-- `populateRemComp` limb `i < 4` is the cast of the chain addend `remAddendNat i`. -/
private lemma populateRemComp_cast (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (i : ℕ) (hi : i < 4) :
    (populateRemComp B C f)[i]'hi = ((remAddendNat B C f i : ℕ) : ZMod p) := by
  simp only [remAddendNat]
  rw [dif_pos hi, ZMod.natCast_zmod_val]

set_option linter.unusedSectionVars false in
/-- The high-limb chain addend `rem_neg · 65535` is the cast of `remAddendNat i` (`i ≥ 4`). -/
private lemma remNeg_fill_cast (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    {i : ℕ} (hi : ¬i < 4) :
    populateRemNeg B C f * 65535 = ((remAddendNat B C f i : ℕ) : ZMod p) := by
  simp only [remAddendNat]
  rw [dif_neg hi, Nat.cast_mul, ZMod.natCast_zmod_val]
  norm_num

set_option linter.unusedSectionVars false in
/-- The high-limb chain target `b_neg · 65535` is the cast of its `.val` form. -/
private lemma bNeg_fill_cast (B : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    populateBNeg B f * 65535 = (((populateBNeg B f).val * 65535 : ℕ) : ZMod p) := by
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  norm_num

/-! ## §1 Chain residues (the E123–E151 byte-pull operands) -/

/-- The `< 2^16` residue of chain step `i`: what remains of
`c_times_quotient[i] + remainder-addend[i] + carry[i-1]` after the carry `carryNat i` is split
off — the natural the byte pull at E123/E127/…/E151 range-checks. -/
def chainResidueNat (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) (i : ℕ) : ℕ :=
  (ctqLimbNat B C f i + remAddendNat B C f i
    + if i = 0 then 0 else carryNat B C f (i - 1)) % 2 ^ 16

set_option linter.unusedSectionVars false in
/-- Every chain residue is a u16. -/
lemma chainResidueNat_lt (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) (i : ℕ) :
    chainResidueNat B C f i < 2 ^ 16 :=
  Nat.mod_lt _ (by norm_num)

set_option linter.unusedSectionVars false in
/-- The field-cast chain residue is a u16, in the `ZMod.val` form the `byteRow_range16` pull wants. -/
lemma chainResidue_field_val_lt (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) (i : ℕ) :
    (((chainResidueNat B C f i : ℕ) : ZMod p)).val < 2 ^ 16 := by
  have hp : 2 ^ 24 < p := Fact.out
  have hlt : chainResidueNat B C f i < 2 ^ 16 := chainResidueNat_lt B C f i
  rw [ZMod.val_natCast_of_lt (by omega)]
  exact hlt

set_option linter.unusedSectionVars false in
/-- Cast core for the chain-residue identities, step 0 (no incoming carry). -/
private lemma residue_field_core0 {x r res cy : ℕ} {Xf Rf CYf : ZMod p}
    (hXf : Xf = (x : ZMod p)) (hRf : Rf = (r : ZMod p)) (hCYf : CYf = (cy : ZMod p))
    (hN : x + r = res + cy * 65536) :
    Xf + Rf - CYf * 65536 = ((res : ℕ) : ZMod p) := by
  subst hXf hRf hCYf
  have hc := congrArg (Nat.cast (R := ZMod p)) hN
  push_cast at hc
  linear_combination hc

set_option linter.unusedSectionVars false in
/-- Cast core for the chain-residue identities, steps 1–7 (incoming carry `cyp`). -/
private lemma residue_field_coreS {x r cyp res cy : ℕ} {Xf Rf CYPf CYf : ZMod p}
    (hXf : Xf = (x : ZMod p)) (hRf : Rf = (r : ZMod p)) (hCYPf : CYPf = (cyp : ZMod p))
    (hCYf : CYf = (cy : ZMod p))
    (hN : x + r + cyp = res + cy * 65536) :
    Xf + Rf - CYf * 65536 + CYPf = ((res : ℕ) : ZMod p) := by
  subst hXf hRf hCYPf hCYf
  have hc := congrArg (Nat.cast (R := ZMod p)) hN
  push_cast at hc
  linear_combination hc

/-- The carry split shared by all eight chain-residue identities: the residue is the `2 ^ 16`
remainder of the step sum and the carry its `2 ^ 16` quotient. -/
private lemma residue_carry_split {s res cy : ℕ} (hres : res = s % 2 ^ 16)
    (hcy : cy = s / 2 ^ 16) : s = res + cy * 65536 := by omega

/-- E123's value form: the step-0 byte-pull operand is the cast of `chainResidueNat 0`. -/
lemma chain_residue_field_0 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateCtq B C f)[0] + (populateRemComp B C f)[0] - (populateCarry B C f)[0] * 65536
      = ((chainResidueNat B C f 0 : ℕ) : ZMod p) :=
  residue_field_core0 (populateCtq_cast B C f 0 (by norm_num))
    (populateRemComp_cast B C f 0 (by norm_num)) (populateCarry_cast B C f 0 (by norm_num))
    (residue_carry_split (by simp [chainResidueNat]) rfl)

/-- E127's value form (step 1, incoming carry `carry[0]`). -/
lemma chain_residue_field_1 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateCtq B C f)[1] + (populateRemComp B C f)[1] - (populateCarry B C f)[1] * 65536
      + (populateCarry B C f)[0]
      = ((chainResidueNat B C f 1 : ℕ) : ZMod p) :=
  residue_field_coreS (populateCtq_cast B C f 1 (by norm_num))
    (populateRemComp_cast B C f 1 (by norm_num)) (populateCarry_cast B C f 0 (by norm_num))
    (populateCarry_cast B C f 1 (by norm_num))
    (residue_carry_split (by simp [chainResidueNat]) rfl)

/-- E131's value form (step 2). -/
lemma chain_residue_field_2 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateCtq B C f)[2] + (populateRemComp B C f)[2] - (populateCarry B C f)[2] * 65536
      + (populateCarry B C f)[1]
      = ((chainResidueNat B C f 2 : ℕ) : ZMod p) :=
  residue_field_coreS (populateCtq_cast B C f 2 (by norm_num))
    (populateRemComp_cast B C f 2 (by norm_num)) (populateCarry_cast B C f 1 (by norm_num))
    (populateCarry_cast B C f 2 (by norm_num))
    (residue_carry_split (by simp [chainResidueNat]) rfl)

/-- E135's value form (step 3). -/
lemma chain_residue_field_3 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateCtq B C f)[3] + (populateRemComp B C f)[3] - (populateCarry B C f)[3] * 65536
      + (populateCarry B C f)[2]
      = ((chainResidueNat B C f 3 : ℕ) : ZMod p) :=
  residue_field_coreS (populateCtq_cast B C f 3 (by norm_num))
    (populateRemComp_cast B C f 3 (by norm_num)) (populateCarry_cast B C f 2 (by norm_num))
    (populateCarry_cast B C f 3 (by norm_num))
    (residue_carry_split (by simp [chainResidueNat]) rfl)

/-- E139's value form (step 4, the `rem_neg · 65535` sign-fill addend). -/
lemma chain_residue_field_4 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateCtq B C f)[4] + populateRemNeg B C f * 65535 - (populateCarry B C f)[4] * 65536
      + (populateCarry B C f)[3]
      = ((chainResidueNat B C f 4 : ℕ) : ZMod p) :=
  residue_field_coreS (populateCtq_cast B C f 4 (by norm_num))
    (remNeg_fill_cast B C f (by norm_num)) (populateCarry_cast B C f 3 (by norm_num))
    (populateCarry_cast B C f 4 (by norm_num))
    (residue_carry_split (by simp [chainResidueNat]) rfl)

/-- E143's value form (step 5). -/
lemma chain_residue_field_5 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateCtq B C f)[5] + populateRemNeg B C f * 65535 - (populateCarry B C f)[5] * 65536
      + (populateCarry B C f)[4]
      = ((chainResidueNat B C f 5 : ℕ) : ZMod p) :=
  residue_field_coreS (populateCtq_cast B C f 5 (by norm_num))
    (remNeg_fill_cast B C f (by norm_num)) (populateCarry_cast B C f 4 (by norm_num))
    (populateCarry_cast B C f 5 (by norm_num))
    (residue_carry_split (by simp [chainResidueNat]) rfl)

/-- E147's value form (step 6). -/
lemma chain_residue_field_6 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateCtq B C f)[6] + populateRemNeg B C f * 65535 - (populateCarry B C f)[6] * 65536
      + (populateCarry B C f)[5]
      = ((chainResidueNat B C f 6 : ℕ) : ZMod p) :=
  residue_field_coreS (populateCtq_cast B C f 6 (by norm_num))
    (remNeg_fill_cast B C f (by norm_num)) (populateCarry_cast B C f 5 (by norm_num))
    (populateCarry_cast B C f 6 (by norm_num))
    (residue_carry_split (by simp [chainResidueNat]) rfl)

/-- E151's value form (step 7, the top byte pull). -/
lemma chain_residue_field_7 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateCtq B C f)[7] + populateRemNeg B C f * 65535 - (populateCarry B C f)[7] * 65536
      + (populateCarry B C f)[6]
      = ((chainResidueNat B C f 7 : ℕ) : ZMod p) :=
  residue_field_coreS (populateCtq_cast B C f 7 (by norm_num))
    (remNeg_fill_cast B C f (by norm_num)) (populateCarry_cast B C f 6 (by norm_num))
    (populateCarry_cast B C f 7 (by norm_num))
    (residue_carry_split (by simp [chainResidueNat]) rfl)

/-! ## §2 The master Euclidean limb identities

Route (a): per class, one 128-bit aggregate congruence; the generic digit-extraction lemma
`chain_limbs_of_sum` then turns it into the eight chain limb equations, and the converter
`euclid_limbs_of_agg` casts those to the field. -/

/-- The 128-bit "extended remainder": the committed `remainder_comp` value with the
`rem_neg`-gated sign fill `2^128 - 2^64` above it — exactly what the chain's eight addends
`remAddendNat` reassemble to in base `2^16`. -/
def remExtNat (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : ℕ :=
  Word.toNat (populateRemComp B C f) + (populateRemNeg B C f).val * (2 ^ 128 - 2 ^ 64)

/-- The 128-bit "extended operand `b`": the committed operand `bComp` with the `b_neg`-gated
sign fill — what the chain's eight limb targets reassemble to. -/
def bExtNat (B : Word (ZMod p)) (f : Vector (ZMod p) 8) : ℕ :=
  Word.toNat (bComp B f) + (populateBNeg B f).val * (2 ^ 128 - 2 ^ 64)

set_option linter.unusedSectionVars false in
/-- The extended remainder in terms of the raw `remainder_comp` bit-vector. -/
private lemma remExtNat_eq (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    remExtNat B C f
      = (remCompBits B C f).toNat + (populateRemNeg B C f).val * (2 ^ 128 - 2 ^ 64) := by
  have hrcv : Word.toNat (populateRemComp B C f) = (remCompBits B C f).toNat :=
    toNat_wordOfBits _
  simp only [remExtNat, hrcv]

/-- The extended remainder fits in 128 bits: a u64 `remainder_comp` under a boolean sign fill. -/
private lemma remExtNat_lt (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hsig : f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1) :
    remExtNat B C f < 2 ^ 128 := by
  have h1 : Word.toNat (populateRemComp B C f) < 2 ^ 64 :=
    toNat_lt_2_64 (populateRemComp_isU64 B C f)
  have h2 : (populateRemNeg B C f).val ≤ 1 := by
    rcases populateRemNeg_bool B C hsig with h | h <;> rw [h] <;> simp [ZMod.val_one]
  simp only [remExtNat]; omega

/-- As `remExtNat_lt`, for the extended operand `b`. -/
private lemma bExtNat_lt {B : Word (ZMod p)} (hB : B.isU64) {f : Vector (ZMod p) 8}
    (hsig : f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1) :
    bExtNat B f < 2 ^ 128 := by
  have h1 : Word.toNat (bComp B f) < 2 ^ 64 := toNat_lt_2_64 (bComp_isU64 hB f)
  have h2 : (populateBNeg B f).val ≤ 1 := by
    rcases populateBNeg_bool hB hsig with h | h <;> rw [h] <;> simp [ZMod.val_one]
  simp only [bExtNat]; omega

set_option linter.unusedSectionVars false in
/-- Low 64-bit digit reconstruction of `X` (helper for `chain_limbs_of_sum`). -/
private lemma chain_recon_lo (X : ℕ) :
    X % 2 ^ 64 = X % 2 ^ 16 + X / 2 ^ 16 % 2 ^ 16 * 2 ^ 16
      + X / 2 ^ 32 % 2 ^ 16 * 2 ^ 32 + X / 2 ^ 48 % 2 ^ 16 * 2 ^ 48 := by
  omega

set_option linter.unusedSectionVars false in
/-- The carry out of the low 64 bits in closed form — keeps the high-limb omegas shallow
(no deep nested carry chain). -/
private lemma chain_carry_lo {X r0 r1 r2 r3 cy0 cy1 cy2 cy3 : ℕ}
    (hcy0 : cy0 = (X % 2 ^ 16 + r0) / 2 ^ 16)
    (hcy1 : cy1 = (X / 2 ^ 16 % 2 ^ 16 + r1 + cy0) / 2 ^ 16)
    (hcy2 : cy2 = (X / 2 ^ 32 % 2 ^ 16 + r2 + cy1) / 2 ^ 16)
    (hcy3 : cy3 = (X / 2 ^ 48 % 2 ^ 16 + r3 + cy2) / 2 ^ 16) :
    cy3 = (X % 2 ^ 64 + (r0 + r1 * 2 ^ 16 + r2 * 2 ^ 32 + r3 * 2 ^ 48)) / 2 ^ 64 := by
  have h := chain_recon_lo X
  omega

set_option linter.unusedSectionVars false in
/-- The two equation-form half-sum constraints, derived from the 128-bit aggregate. The
equation form (`= Z%2^64 + cy3·2^64`) is what keeps each per-limb omega shallow. -/
private lemma chain_half_constraints {X Z k r0 r1 r2 r3 r4 r5 r6 r7 cy3 : ℕ}
    (hB : cy3 = (X % 2 ^ 64 + (r0 + r1 * 2 ^ 16 + r2 * 2 ^ 32 + r3 * 2 ^ 48)) / 2 ^ 64)
    (hsum : X + (r0 + r1 * 2 ^ 16 + r2 * 2 ^ 32 + r3 * 2 ^ 48 + r4 * 2 ^ 64 + r5 * 2 ^ 80
        + r6 * 2 ^ 96 + r7 * 2 ^ 112) = Z + 2 ^ 128 * k) :
    (X % 2 ^ 64 + (r0 + r1 * 2 ^ 16 + r2 * 2 ^ 32 + r3 * 2 ^ 48) = Z % 2 ^ 64 + cy3 * 2 ^ 64) ∧
    (X / 2 ^ 64 + (r4 + r5 * 2 ^ 16 + r6 * 2 ^ 32 + r7 * 2 ^ 48) + cy3
      = Z / 2 ^ 64 + 2 ^ 64 * k) := by
  subst hB
  exact ⟨by omega, by omega⟩

set_option linter.unusedSectionVars false in
/-- Low ripple: the four low chain limb equations from the low half-sum constraint. -/
private lemma chain_low_limbs {X Z r0 r1 r2 r3 cy0 cy1 cy2 cy3 : ℕ}
    (hcy0 : cy0 = (X % 2 ^ 16 + r0) / 2 ^ 16)
    (hcy1 : cy1 = (X / 2 ^ 16 % 2 ^ 16 + r1 + cy0) / 2 ^ 16)
    (hcy2 : cy2 = (X / 2 ^ 32 % 2 ^ 16 + r2 + cy1) / 2 ^ 16)
    (hcy3 : cy3 = (X / 2 ^ 48 % 2 ^ 16 + r3 + cy2) / 2 ^ 16)
    (hloeq : X % 2 ^ 64 + (r0 + r1 * 2 ^ 16 + r2 * 2 ^ 32 + r3 * 2 ^ 48)
      = Z % 2 ^ 64 + cy3 * 2 ^ 64) :
    X % 2 ^ 16 + r0 = Z % 2 ^ 16 + cy0 * 2 ^ 16 ∧
    X / 2 ^ 16 % 2 ^ 16 + r1 + cy0 = Z / 2 ^ 16 % 2 ^ 16 + cy1 * 2 ^ 16 ∧
    X / 2 ^ 32 % 2 ^ 16 + r2 + cy1 = Z / 2 ^ 32 % 2 ^ 16 + cy2 * 2 ^ 16 ∧
    X / 2 ^ 48 % 2 ^ 16 + r3 + cy2 = Z / 2 ^ 48 % 2 ^ 16 + cy3 * 2 ^ 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

set_option linter.unusedSectionVars false in
/-- High ripple: the four high chain limb equations from the high half-sum constraint, with the
incoming carry `cy3` taken as a flat atom. -/
private lemma chain_high_limbs {X Z k r4 r5 r6 r7 cy3 cy4 cy5 cy6 cy7 : ℕ}
    (hcy4 : cy4 = (X / 2 ^ 64 % 2 ^ 16 + r4 + cy3) / 2 ^ 16)
    (hcy5 : cy5 = (X / 2 ^ 80 % 2 ^ 16 + r5 + cy4) / 2 ^ 16)
    (hcy6 : cy6 = (X / 2 ^ 96 % 2 ^ 16 + r6 + cy5) / 2 ^ 16)
    (hcy7 : cy7 = (X / 2 ^ 112 % 2 ^ 16 + r7 + cy6) / 2 ^ 16)
    (hhi : X / 2 ^ 64 + (r4 + r5 * 2 ^ 16 + r6 * 2 ^ 32 + r7 * 2 ^ 48) + cy3
      = Z / 2 ^ 64 + 2 ^ 64 * k) :
    X / 2 ^ 64 % 2 ^ 16 + r4 + cy3 = Z / 2 ^ 64 % 2 ^ 16 + cy4 * 2 ^ 16 ∧
    X / 2 ^ 80 % 2 ^ 16 + r5 + cy4 = Z / 2 ^ 80 % 2 ^ 16 + cy5 * 2 ^ 16 ∧
    X / 2 ^ 96 % 2 ^ 16 + r6 + cy5 = Z / 2 ^ 96 % 2 ^ 16 + cy6 * 2 ^ 16 ∧
    X / 2 ^ 112 % 2 ^ 16 + r7 + cy6 = Z / 2 ^ 112 % 2 ^ 16 + cy7 * 2 ^ 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

set_option linter.unusedVariables false in
/-- **Generic digit extraction.** If `X + R = Z + 2^128·k` with `X, Z < 2^128` and `R` the
base-`2^16` reassembly of eight u16 addends `r0…r7`, then the carry recursion
`cy_i = (x_i + r_i + cy_{i-1}) / 2^16` on the digits `x_i` of `X` satisfies the eight chain limb
equations against the digits `z_i` of `Z`. Composed from the five minimal-context helpers above
(low/high-half ripples + the closed-form boundary carry `chain_carry_lo`); each helper is a
shallow `omega`, which keeps elaboration to seconds (a monolithic `omega` here does not scale). -/
private lemma chain_limbs_of_sum
    {X Z k x0 x1 x2 x3 x4 x5 x6 x7 r0 r1 r2 r3 r4 r5 r6 r7
     z0 z1 z2 z3 z4 z5 z6 z7 cy0 cy1 cy2 cy3 cy4 cy5 cy6 cy7 : ℕ}
    (hX : X < 2 ^ 128) (hZ : Z < 2 ^ 128)
    (hx0 : x0 = X % 2 ^ 16) (hx1 : x1 = X / 2 ^ 16 % 2 ^ 16)
    (hx2 : x2 = X / 2 ^ 32 % 2 ^ 16) (hx3 : x3 = X / 2 ^ 48 % 2 ^ 16)
    (hx4 : x4 = X / 2 ^ 64 % 2 ^ 16) (hx5 : x5 = X / 2 ^ 80 % 2 ^ 16)
    (hx6 : x6 = X / 2 ^ 96 % 2 ^ 16) (hx7 : x7 = X / 2 ^ 112 % 2 ^ 16)
    (hz0 : z0 = Z % 2 ^ 16) (hz1 : z1 = Z / 2 ^ 16 % 2 ^ 16)
    (hz2 : z2 = Z / 2 ^ 32 % 2 ^ 16) (hz3 : z3 = Z / 2 ^ 48 % 2 ^ 16)
    (hz4 : z4 = Z / 2 ^ 64 % 2 ^ 16) (hz5 : z5 = Z / 2 ^ 80 % 2 ^ 16)
    (hz6 : z6 = Z / 2 ^ 96 % 2 ^ 16) (hz7 : z7 = Z / 2 ^ 112 % 2 ^ 16)
    (hr0 : r0 < 2 ^ 16) (hr1 : r1 < 2 ^ 16) (hr2 : r2 < 2 ^ 16) (hr3 : r3 < 2 ^ 16)
    (hr4 : r4 < 2 ^ 16) (hr5 : r5 < 2 ^ 16) (hr6 : r6 < 2 ^ 16) (hr7 : r7 < 2 ^ 16)
    (hcy0 : cy0 = (x0 + r0) / 2 ^ 16)
    (hcy1 : cy1 = (x1 + r1 + cy0) / 2 ^ 16) (hcy2 : cy2 = (x2 + r2 + cy1) / 2 ^ 16)
    (hcy3 : cy3 = (x3 + r3 + cy2) / 2 ^ 16) (hcy4 : cy4 = (x4 + r4 + cy3) / 2 ^ 16)
    (hcy5 : cy5 = (x5 + r5 + cy4) / 2 ^ 16) (hcy6 : cy6 = (x6 + r6 + cy5) / 2 ^ 16)
    (hcy7 : cy7 = (x7 + r7 + cy6) / 2 ^ 16)
    (hsum : X + (r0 + r1 * 2 ^ 16 + r2 * 2 ^ 32 + r3 * 2 ^ 48 + r4 * 2 ^ 64 + r5 * 2 ^ 80
        + r6 * 2 ^ 96 + r7 * 2 ^ 112) = Z + 2 ^ 128 * k) :
    x0 + r0 = z0 + cy0 * 2 ^ 16 ∧
    x1 + r1 + cy0 = z1 + cy1 * 2 ^ 16 ∧
    x2 + r2 + cy1 = z2 + cy2 * 2 ^ 16 ∧
    x3 + r3 + cy2 = z3 + cy3 * 2 ^ 16 ∧
    x4 + r4 + cy3 = z4 + cy4 * 2 ^ 16 ∧
    x5 + r5 + cy4 = z5 + cy5 * 2 ^ 16 ∧
    x6 + r6 + cy5 = z6 + cy6 * 2 ^ 16 ∧
    x7 + r7 + cy6 = z7 + cy7 * 2 ^ 16 := by
  subst hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7
  have hB := chain_carry_lo hcy0 hcy1 hcy2 hcy3
  obtain ⟨hloeq, hhi⟩ := chain_half_constraints hB hsum
  obtain ⟨e0, e1, e2, e3⟩ := chain_low_limbs hcy0 hcy1 hcy2 hcy3 hloeq
  obtain ⟨e4, e5, e6, e7⟩ := chain_high_limbs hcy4 hcy5 hcy6 hcy7 hhi
  exact ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩

/-- **The eight de-gated chain limb equations** at the populate values — the value-level forms of
the own-asserts E154/E157/E160/E163 (low limbs, against `bComp`) and E167/E171/E175/E179 (high
limbs, against the `b_neg · 65535` sign fill). -/
def EuclidLimbEqs (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Prop :=
  (bComp B f)[0] = (populateCtq B C f)[0] + (populateRemComp B C f)[0]
      - (populateCarry B C f)[0] * 65536 ∧
  (bComp B f)[1] = (populateCtq B C f)[1] + (populateRemComp B C f)[1]
      - (populateCarry B C f)[1] * 65536 + (populateCarry B C f)[0] ∧
  (bComp B f)[2] = (populateCtq B C f)[2] + (populateRemComp B C f)[2]
      - (populateCarry B C f)[2] * 65536 + (populateCarry B C f)[1] ∧
  (bComp B f)[3] = (populateCtq B C f)[3] + (populateRemComp B C f)[3]
      - (populateCarry B C f)[3] * 65536 + (populateCarry B C f)[2] ∧
  populateBNeg B f * 65535 = (populateCtq B C f)[4] + populateRemNeg B C f * 65535
      - (populateCarry B C f)[4] * 65536 + (populateCarry B C f)[3] ∧
  populateBNeg B f * 65535 = (populateCtq B C f)[5] + populateRemNeg B C f * 65535
      - (populateCarry B C f)[5] * 65536 + (populateCarry B C f)[4] ∧
  populateBNeg B f * 65535 = (populateCtq B C f)[6] + populateRemNeg B C f * 65535
      - (populateCarry B C f)[6] * 65536 + (populateCarry B C f)[5] ∧
  populateBNeg B f * 65535 = (populateCtq B C f)[7] + populateRemNeg B C f * 65535
      - (populateCarry B C f)[7] * 65536 + (populateCarry B C f)[6]

set_option linter.unusedSectionVars false in
/-- Cast core for a chain limb equation, step 0. -/
private lemma limb_field_lo {x r z cy : ℕ} {Xf Rf Zf CYf : ZMod p}
    (hXf : Xf = (x : ZMod p)) (hRf : Rf = (r : ZMod p)) (hZf : Zf = (z : ZMod p))
    (hCYf : CYf = (cy : ZMod p)) (hN : x + r = z + cy * 2 ^ 16) :
    Zf = Xf + Rf - CYf * 65536 := by
  subst hXf hRf hZf hCYf
  have hc := congrArg (Nat.cast (R := ZMod p)) hN
  push_cast at hc
  linear_combination -hc

set_option linter.unusedSectionVars false in
/-- Cast core for a chain limb equation, steps 1–7 (incoming carry). -/
private lemma limb_field_hi {x r cyp z cy : ℕ} {Xf Rf CYPf Zf CYf : ZMod p}
    (hXf : Xf = (x : ZMod p)) (hRf : Rf = (r : ZMod p)) (hCYPf : CYPf = (cyp : ZMod p))
    (hZf : Zf = (z : ZMod p)) (hCYf : CYf = (cy : ZMod p))
    (hN : x + r + cyp = z + cy * 2 ^ 16) :
    Zf = Xf + Rf - CYf * 65536 + CYPf := by
  subst hXf hRf hCYPf hZf hCYf
  have hc := congrArg (Nat.cast (R := ZMod p)) hN
  push_cast at hc
  linear_combination -hc

-- 4.30: the `hz5`/`hz6`/`hz7` extended-digit extractions run `omega` on the aggregate
-- `Word.toNat (bComp B f) + (populateBNeg B f).val * (2^128 - 2^64)` divided by `2^80`/`2^96`/`2^112`.
-- Against those opaque subterms `omega` hits `maxRecDepth`; over fresh `t`/`b` (with `interval_cases b`
-- splitting the boolean) it discharges cleanly, so we factor the arithmetic into these three helpers.
set_option maxRecDepth 10000 in
private lemma fill_digit_80 (t b : ℕ) (ht : t < 2 ^ 64) (hb : b ≤ 1) :
    b * 65535 = (t + b * (2 ^ 128 - 2 ^ 64)) / 2 ^ 80 % 2 ^ 16 := by interval_cases b <;> omega

set_option maxRecDepth 10000 in
private lemma fill_digit_96 (t b : ℕ) (ht : t < 2 ^ 64) (hb : b ≤ 1) :
    b * 65535 = (t + b * (2 ^ 128 - 2 ^ 64)) / 2 ^ 96 % 2 ^ 16 := by interval_cases b <;> omega

set_option maxRecDepth 10000 in
private lemma fill_digit_112 (t b : ℕ) (ht : t < 2 ^ 64) (hb : b ≤ 1) :
    b * 65535 = (t + b * (2 ^ 128 - 2 ^ 64)) / 2 ^ 112 % 2 ^ 16 := by interval_cases b <;> omega

/-- **Aggregate → limb equations.** Any class that proves the 128-bit aggregate congruence
`ctqProd + remExtNat = bExtNat + 2^128·k` gets the eight field limb equations: digit-extract
with `chain_limbs_of_sum`, then cast each digit equation. -/
private lemma euclid_limbs_of_agg {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hB : B.isU64)
    (hsig : f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1)
    (hagg : ∃ k : ℕ, (ctqProd B C f).toNat + remExtNat B C f = bExtNat B f + 2 ^ 128 * k) :
    EuclidLimbEqs B C f := by
  obtain ⟨k, hagg⟩ := hagg
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 (bComp_isU64 hB f)
  have hbnv : (populateBNeg B f).val ≤ 1 := by
    rcases populateBNeg_bool hB hsig with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have hXlt : (ctqProd B C f).toNat < 2 ^ 128 := (ctqProd B C f).isLt
  have hZlt : bExtNat B f < 2 ^ 128 := bExtNat_lt hB hsig
  have hc : Word.toNat (bComp B f) < 2 ^ 64 := toNat_lt_2_64 (bComp_isU64 hB f)
  -- the committed-operand digits of `bExtNat`
  have hz0 : ((bComp B f)[0]).val = bExtNat B f % 2 ^ 16 := by
    simp only [bExtNat, Word.toNat_def]; omega
  have hz1 : ((bComp B f)[1]).val = bExtNat B f / 2 ^ 16 % 2 ^ 16 := by
    simp only [bExtNat, Word.toNat_def]; omega
  have hz2 : ((bComp B f)[2]).val = bExtNat B f / 2 ^ 32 % 2 ^ 16 := by
    simp only [bExtNat, Word.toNat_def]; omega
  have hz3 : ((bComp B f)[3]).val = bExtNat B f / 2 ^ 48 % 2 ^ 16 := by
    simp only [bExtNat, Word.toNat_def]; omega
  have hz4 : (populateBNeg B f).val * 65535 = bExtNat B f / 2 ^ 64 % 2 ^ 16 := by
    simp only [bExtNat, Word.toNat_def]; omega
  have hz5 : (populateBNeg B f).val * 65535 = bExtNat B f / 2 ^ 80 % 2 ^ 16 := by
    simp only [bExtNat]; exact fill_digit_80 _ _ hc hbnv
  have hz6 : (populateBNeg B f).val * 65535 = bExtNat B f / 2 ^ 96 % 2 ^ 16 := by
    simp only [bExtNat]; exact fill_digit_96 _ _ hc hbnv
  have hz7 : (populateBNeg B f).val * 65535 = bExtNat B f / 2 ^ 112 % 2 ^ 16 := by
    simp only [bExtNat]; exact fill_digit_112 _ _ hc hbnv
  -- the product digits
  have hx0 : ctqLimbNat B C f 0 = (ctqProd B C f).toNat % 2 ^ 16 := by
    norm_num [ctqLimbNat]
  have hx1 : ctqLimbNat B C f 1 = (ctqProd B C f).toNat / 2 ^ 16 % 2 ^ 16 := by
    norm_num [ctqLimbNat]
  have hx2 : ctqLimbNat B C f 2 = (ctqProd B C f).toNat / 2 ^ 32 % 2 ^ 16 := by
    norm_num [ctqLimbNat]
  have hx3 : ctqLimbNat B C f 3 = (ctqProd B C f).toNat / 2 ^ 48 % 2 ^ 16 := by
    norm_num [ctqLimbNat]
  have hx4 : ctqLimbNat B C f 4 = (ctqProd B C f).toNat / 2 ^ 64 % 2 ^ 16 := by
    norm_num [ctqLimbNat]
  have hx5 : ctqLimbNat B C f 5 = (ctqProd B C f).toNat / 2 ^ 80 % 2 ^ 16 := by
    norm_num [ctqLimbNat]
  have hx6 : ctqLimbNat B C f 6 = (ctqProd B C f).toNat / 2 ^ 96 % 2 ^ 16 := by
    norm_num [ctqLimbNat]
  have hx7 : ctqLimbNat B C f 7 = (ctqProd B C f).toNat / 2 ^ 112 % 2 ^ 16 := by
    norm_num [ctqLimbNat]
  -- the carry recursion, definitional at literal indices
  have hcy0 : carryNat B C f 0 = (ctqLimbNat B C f 0 + remAddendNat B C f 0) / 2 ^ 16 := rfl
  have hcy1 : carryNat B C f 1
      = (ctqLimbNat B C f 1 + remAddendNat B C f 1 + carryNat B C f 0) / 2 ^ 16 := rfl
  have hcy2 : carryNat B C f 2
      = (ctqLimbNat B C f 2 + remAddendNat B C f 2 + carryNat B C f 1) / 2 ^ 16 := rfl
  have hcy3 : carryNat B C f 3
      = (ctqLimbNat B C f 3 + remAddendNat B C f 3 + carryNat B C f 2) / 2 ^ 16 := rfl
  have hcy4 : carryNat B C f 4
      = (ctqLimbNat B C f 4 + remAddendNat B C f 4 + carryNat B C f 3) / 2 ^ 16 := rfl
  have hcy5 : carryNat B C f 5
      = (ctqLimbNat B C f 5 + remAddendNat B C f 5 + carryNat B C f 4) / 2 ^ 16 := rfl
  have hcy6 : carryNat B C f 6
      = (ctqLimbNat B C f 6 + remAddendNat B C f 6 + carryNat B C f 5) / 2 ^ 16 := rfl
  have hcy7 : carryNat B C f 7
      = (ctqLimbNat B C f 7 + remAddendNat B C f 7 + carryNat B C f 6) / 2 ^ 16 := rfl
  -- the addend reassembly
  have hRsum : remExtNat B C f
      = remAddendNat B C f 0 + remAddendNat B C f 1 * 2 ^ 16 + remAddendNat B C f 2 * 2 ^ 32
        + remAddendNat B C f 3 * 2 ^ 48 + remAddendNat B C f 4 * 2 ^ 64
        + remAddendNat B C f 5 * 2 ^ 80 + remAddendNat B C f 6 * 2 ^ 96
        + remAddendNat B C f 7 * 2 ^ 112 := by
    have e0 : remAddendNat B C f 0 = ((populateRemComp B C f)[0]).val := by
      simp [remAddendNat]
    have e1 : remAddendNat B C f 1 = ((populateRemComp B C f)[1]).val := by
      simp [remAddendNat]
    have e2 : remAddendNat B C f 2 = ((populateRemComp B C f)[2]).val := by
      simp [remAddendNat]
    have e3 : remAddendNat B C f 3 = ((populateRemComp B C f)[3]).val := by
      simp [remAddendNat]
    have e4 : remAddendNat B C f 4 = (populateRemNeg B C f).val * 65535 := by
      simp [remAddendNat]
    have e5 : remAddendNat B C f 5 = (populateRemNeg B C f).val * 65535 := by
      simp [remAddendNat]
    have e6 : remAddendNat B C f 6 = (populateRemNeg B C f).val * 65535 := by
      simp [remAddendNat]
    have e7 : remAddendNat B C f 7 = (populateRemNeg B C f).val * 65535 := by
      simp [remAddendNat]
    rw [e0, e1, e2, e3, e4, e5, e6, e7]
    simp only [remExtNat, Word.toNat_def]
    omega
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ :=
    chain_limbs_of_sum hXlt hZlt hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7
      hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7
      (remAddendNat_lt B C hsig 0) (remAddendNat_lt B C hsig 1) (remAddendNat_lt B C hsig 2)
      (remAddendNat_lt B C hsig 3) (remAddendNat_lt B C hsig 4) (remAddendNat_lt B C hsig 5)
      (remAddendNat_lt B C hsig 6) (remAddendNat_lt B C hsig 7)
      hcy0 hcy1 hcy2 hcy3 hcy4 hcy5 hcy6 hcy7
      (by rw [← hRsum]; exact hagg)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact limb_field_lo (populateCtq_cast B C f 0 (by norm_num))
      (populateRemComp_cast B C f 0 (by norm_num)) (ZMod.natCast_zmod_val _).symm
      (populateCarry_cast B C f 0 (by norm_num)) e0
  · exact limb_field_hi (populateCtq_cast B C f 1 (by norm_num))
      (populateRemComp_cast B C f 1 (by norm_num)) (populateCarry_cast B C f 0 (by norm_num))
      (ZMod.natCast_zmod_val _).symm (populateCarry_cast B C f 1 (by norm_num)) e1
  · exact limb_field_hi (populateCtq_cast B C f 2 (by norm_num))
      (populateRemComp_cast B C f 2 (by norm_num)) (populateCarry_cast B C f 1 (by norm_num))
      (ZMod.natCast_zmod_val _).symm (populateCarry_cast B C f 2 (by norm_num)) e2
  · exact limb_field_hi (populateCtq_cast B C f 3 (by norm_num))
      (populateRemComp_cast B C f 3 (by norm_num)) (populateCarry_cast B C f 2 (by norm_num))
      (ZMod.natCast_zmod_val _).symm (populateCarry_cast B C f 3 (by norm_num)) e3
  · exact limb_field_hi (populateCtq_cast B C f 4 (by norm_num))
      (remNeg_fill_cast B C f (by norm_num)) (populateCarry_cast B C f 3 (by norm_num))
      (bNeg_fill_cast B f) (populateCarry_cast B C f 4 (by norm_num)) e4
  · exact limb_field_hi (populateCtq_cast B C f 5 (by norm_num))
      (remNeg_fill_cast B C f (by norm_num)) (populateCarry_cast B C f 4 (by norm_num))
      (bNeg_fill_cast B f) (populateCarry_cast B C f 5 (by norm_num)) e5
  · exact limb_field_hi (populateCtq_cast B C f 6 (by norm_num))
      (remNeg_fill_cast B C f (by norm_num)) (populateCarry_cast B C f 5 (by norm_num))
      (bNeg_fill_cast B f) (populateCarry_cast B C f 6 (by norm_num)) e6
  · exact limb_field_hi (populateCtq_cast B C f 7 (by norm_num))
      (remNeg_fill_cast B C f (by norm_num)) (populateCarry_cast B C f 6 (by norm_num))
      (bNeg_fill_cast B f) (populateCarry_cast B C f 7 (by norm_num)) e7

/-! ## §2 Class cores: the aggregate congruence per variant class -/

set_option linter.unusedSectionVars false in
/-- The signed cores' carry disjunction, factored over **abstract** `A R Z` and msb booleans so the
kernel never has to reduce the underlying `BitVec` terms (`ctqProd`/`srem`/…), which would trigger
`(kernel) deep recursion`. Each core derives its 128-bit `hcomb` congruence and applies this. -/
private lemma signed_agg {A R Z : ℕ} {b1 b2 b3 : Bool}
    (hA : A < 2 ^ 128) (hR : R < 2 ^ 128) (hZ : Z < 2 ^ 128)
    (hcomb : (A : ℤ) + (R : ℤ) = (Z : ℤ)
      + ((if b1 then (2 : ℤ) ^ 128 else 0) + (if b2 then (2 : ℤ) ^ 128 else 0)
        - (if b3 then (2 : ℤ) ^ 128 else 0))) :
    ∃ k : ℕ, A + R = Z + 2 ^ 128 * k := by
  have hk : A + R = Z ∨ A + R = Z + 2 ^ 128 := by split_ifs at hcomb <;> omega
  rcases hk with h | h
  · exact ⟨0, by omega⟩
  · exact ⟨1, by omega⟩

/-- Signed 64-bit class core (`div`/`rem`), from the reduced flag sums. -/
private lemma euclid_limbs_s64_core {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hB : B.isU64)
    (h45 : f[4] + f[5] = 0) (h67 : f[6] + f[7] = 0) (h02 : f[0] + f[2] = 1)
    (hnotmin : ¬(Word.toBitVec64 B = BitVec.intMin 64
        ∧ Word.toBitVec64 C = BitVec.allOnes 64)) :
    EuclidLimbEqs B C f := by
  have hsig : f[0] + f[2] + f[4] + f[5] = 1 := by linear_combination h02 + h45
  have h4567 : f[4] + f[5] + f[6] + f[7] = 0 := by linear_combination h45 + h67
  have hn45 : ¬f[4] + f[5] = 1 := by rw [h45]; exact zero_ne_one
  have hn67 : ¬f[6] + f[7] = 1 := by rw [h67]; exact zero_ne_one
  have hn4567 : ¬f[4] + f[5] + f[6] + f[7] = 1 := by rw [h4567]; exact zero_ne_one
  obtain ⟨hb0v, hb1v, hb2v, hb3v⟩ := Word.lt_cases_of_isU64 hB
  -- populate shapes on this class
  have hqb : quotBits B C f
      = if Word.toBitVec64 C = 0 then BitVec.allOnes 64
        else (Word.toBitVec64 B).sdiv (Word.toBitVec64 C) := by
    simp only [quotBits]; rw [if_neg hn45, if_neg hn67, if_pos h02]
  have hrb : remBits B C f
      = if Word.toBitVec64 C = 0 then Word.toBitVec64 B
        else (Word.toBitVec64 B).srem (Word.toBitVec64 C) := by
    simp only [remBits]; rw [if_neg hn45, if_neg hn67, if_pos h02]
  have hqcb : quotCompBits B C f = quotBits B C f := by
    simp only [quotCompBits]; rw [if_neg hn67]
  have hrcb : remCompBits B C f = remBits B C f := by
    simp only [remCompBits]; rw [if_neg hn67]
  have hbc : bComp B f = B := by
    simp only [bComp]; rw [if_neg hn45, if_neg hn67]
  have hcc : cComp C f = C := by
    simp only [cComp]; rw [if_neg hn45, if_neg hn67]
  have hprod : ctqProd B C f
      = (Word.toBitVec64 (populateQuotComp B C f)).signExtend 128
        * (Word.toBitVec64 (cComp C f)).signExtend 128 := by
    simp only [ctqProd]; rw [if_pos hsig]
  have hqcv : Word.toBitVec64 (populateQuotComp B C f) = quotCompBits B C f :=
    wordOfBits_toBitVec64 _
  -- sign cells: `b_neg = msb b`, `rem_neg = msb remBits`
  have hbn : populateBNeg B f = if (Word.toBitVec64 B).msb then 1 else 0 := by
    rw [populateBNeg_def, hsig, one_mul]
    simp only [bMsbCell]
    rw [if_neg hn4567, populate_msb_eq_ite hb3v]
    by_cases hge : 32768 ≤ B[3].val
    · rw [if_pos hge, if_pos ((toBitVec64_msb_iff hB).mpr hge)]
    · rw [if_neg hge, if_neg (fun hm => hge ((toBitVec64_msb_iff hB).mp hm))]
  have hrn : populateRemNeg B C f = if (remBits B C f).msb then 1 else 0 := by
    rw [populateRemNeg_def, hsig, one_mul]
    simp only [remMsbCell, populateRemainder]
    rw [if_neg hn4567]
    exact populate_msb_limb3 (remBits B C f)
  -- the extended values
  have hZdef : bExtNat B f = (Word.toBitVec64 B).toNat
      + (if (Word.toBitVec64 B).msb then 1 else 0) * (2 ^ 128 - 2 ^ 64) := by
    simp only [bExtNat]
    rw [hbc, ← Word.toBitVec64_toNat hB, hbn, val_ite01]
  have hRdef_of : ∀ y : BitVec 64, remBits B C f = y →
      remExtNat B C f = y.toNat + (if y.msb then 1 else 0) * (2 ^ 128 - 2 ^ 64) := by
    intro y hy
    rw [remExtNat_eq, hrcb, hrn, hy, val_ite01]
  by_cases hc0 : Word.toBitVec64 C = 0
  · -- divisor zero: `X = 0`, `R = Z`, `k = 0`
    have hX0 : (ctqProd B C f).toNat = 0 := by
      rw [hprod, hcc, hc0]
      have hz1 : ((0 : BitVec 64).signExtend 128) = 0 := by
        rw [← BitVec.toNat_inj]
        simp
      rw [hz1]
      simp
    have hy : remBits B C f = Word.toBitVec64 B := by rw [hrb, if_pos hc0]
    refine euclid_limbs_of_agg hB (Or.inr hsig) ⟨0, ?_⟩
    rw [hX0, hRdef_of _ hy, hZdef]
    simp
  · -- `c ≠ 0`: the signed Euclidean identity over `ℤ`, mod-`2^128` transfer
    have hq : quotCompBits B C f = (Word.toBitVec64 B).sdiv (Word.toBitVec64 C) := by
      rw [hqcb, hqb, if_neg hc0]
    have hy : remBits B C f = (Word.toBitVec64 B).srem (Word.toBitVec64 C) := by
      rw [hrb, if_neg hc0]
    have hident := sdiv_srem_toInt_identity (not_and_or.mp hnotmin)
    have hPint : (ctqProd B C f).toInt
        = ((Word.toBitVec64 B).sdiv (Word.toBitVec64 C)).toInt
          * (Word.toBitVec64 C).toInt := by
      rw [hprod, hqcv, hq, hcc, signed_prod_toInt]
    have hXint : ((ctqProd B C f).toNat : ℤ)
        = ((Word.toBitVec64 B).sdiv (Word.toBitVec64 C)).toInt * (Word.toBitVec64 C).toInt
          + (if (ctqProd B C f).msb then (2 : ℤ) ^ 128 else 0) := by
      have h128 := toInt_eq_toNat_sub128' (ctqProd B C f)
      rw [hPint] at h128
      linear_combination -h128
    have hRint : (remExtNat B C f : ℤ)
        = ((Word.toBitVec64 B).srem (Word.toBitVec64 C)).toInt
          + (if ((Word.toBitVec64 B).srem (Word.toBitVec64 C)).msb
              then (2 : ℤ) ^ 128 else 0) := by
      rw [hRdef_of _ hy]
      exact extNat_int64 _ rfl
    have hZint : (bExtNat B f : ℤ) = (Word.toBitVec64 B).toInt
        + (if (Word.toBitVec64 B).msb then (2 : ℤ) ^ 128 else 0) := by
      rw [hZdef]
      exact extNat_int64 _ rfl
    have hcomb : ((ctqProd B C f).toNat : ℤ) + (remExtNat B C f : ℤ)
        = (bExtNat B f : ℤ)
          + ((if (ctqProd B C f).msb then (2 : ℤ) ^ 128 else 0)
            + (if ((Word.toBitVec64 B).srem (Word.toBitVec64 C)).msb
                then (2 : ℤ) ^ 128 else 0)
            - (if (Word.toBitVec64 B).msb then (2 : ℤ) ^ 128 else 0)) := by
      rw [hXint, hRint, hZint]
      linear_combination -hident
    exact euclid_limbs_of_agg hB (Or.inr hsig)
      (signed_agg (ctqProd B C f).isLt (remExtNat_lt B C (Or.inr hsig))
        (bExtNat_lt hB (Or.inr hsig)) hcomb)

/-- Unsigned 64-bit class core (`divu`/`remu`): `k = 0`, pure `Nat.div_add_mod`. -/
private lemma euclid_limbs_u64_core {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hB : B.isU64)
    (h45 : f[4] + f[5] = 0) (h67 : f[6] + f[7] = 0) (h02 : f[0] + f[2] = 0) :
    EuclidLimbEqs B C f := by
  have hsig0 : f[0] + f[2] + f[4] + f[5] = 0 := by linear_combination h02 + h45
  have hn45 : ¬f[4] + f[5] = 1 := by rw [h45]; exact zero_ne_one
  have hn67 : ¬f[6] + f[7] = 1 := by rw [h67]; exact zero_ne_one
  have hn02 : ¬f[0] + f[2] = 1 := by rw [h02]; exact zero_ne_one
  have hnsig : ¬f[0] + f[2] + f[4] + f[5] = 1 := by rw [hsig0]; exact zero_ne_one
  have hqb : quotBits B C f
      = if Word.toBitVec64 C = 0 then BitVec.allOnes 64
        else (Word.toBitVec64 B).udiv (Word.toBitVec64 C) := by
    simp only [quotBits]; rw [if_neg hn45, if_neg hn67, if_neg hn02]
  have hrb : remBits B C f
      = if Word.toBitVec64 C = 0 then Word.toBitVec64 B
        else (Word.toBitVec64 B).umod (Word.toBitVec64 C) := by
    simp only [remBits]; rw [if_neg hn45, if_neg hn67, if_neg hn02]
  have hqcb : quotCompBits B C f = quotBits B C f := by
    simp only [quotCompBits]; rw [if_neg hn67]
  have hrcb : remCompBits B C f = remBits B C f := by
    simp only [remCompBits]; rw [if_neg hn67]
  have hbc : bComp B f = B := by
    simp only [bComp]; rw [if_neg hn45, if_neg hn67]
  have hcc : cComp C f = C := by
    simp only [cComp]; rw [if_neg hn45, if_neg hn67]
  have hprod : ctqProd B C f
      = (Word.toBitVec64 (populateQuotComp B C f)).setWidth 128
        * (Word.toBitVec64 (cComp C f)).setWidth 128 := by
    simp only [ctqProd]; rw [if_neg hnsig]
  have hbn0 : populateBNeg B f = 0 := by rw [populateBNeg_def, hsig0, zero_mul]
  have hrn0 : populateRemNeg B C f = 0 := by rw [populateRemNeg_def, hsig0, zero_mul]
  have hZn : bExtNat B f = (Word.toBitVec64 B).toNat := by
    simp only [bExtNat]
    rw [hbc, ← Word.toBitVec64_toNat hB, hbn0, ZMod.val_zero]
    omega
  have hRn : remExtNat B C f = (remBits B C f).toNat := by
    rw [remExtNat_eq, hrcb, hrn0, ZMod.val_zero]
    omega
  have hXn : (ctqProd B C f).toNat
      = (quotBits B C f).toNat * (Word.toBitVec64 C).toNat := by
    have hql := (quotBits B C f).isLt
    have hcl := (Word.toBitVec64 C).isLt
    have hmul : (quotBits B C f).toNat * (Word.toBitVec64 C).toNat < 2 ^ 128 := by
      have h := Nat.mul_le_mul (show (quotBits B C f).toNat ≤ 2 ^ 64 - 1 by omega)
        (show (Word.toBitVec64 C).toNat ≤ 2 ^ 64 - 1 by omega)
      omega
    have h1 : Word.toBitVec64 (populateQuotComp B C f) = quotBits B C f :=
      (wordOfBits_toBitVec64 _).trans hqcb
    rw [hprod, h1, hcc, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (show (quotBits B C f).toNat < 2 ^ 128 by omega),
        Nat.mod_eq_of_lt (show (Word.toBitVec64 C).toNat < 2 ^ 128 by omega),
        Nat.mod_eq_of_lt hmul]
  by_cases hc0 : Word.toBitVec64 C = 0
  · refine euclid_limbs_of_agg hB (Or.inl hsig0) ⟨0, ?_⟩
    have hcz : (Word.toBitVec64 C).toNat = 0 := by rw [hc0]; rfl
    rw [hXn, hcz, hRn, hrb, if_pos hc0, hZn]
    omega
  · refine euclid_limbs_of_agg hB (Or.inl hsig0) ⟨0, ?_⟩
    rw [hXn, hRn, hZn, hqb, if_neg hc0, hrb, if_neg hc0,
        BitVec.udiv_eq, BitVec.toNat_udiv, BitVec.umod_eq, BitVec.toNat_umod,
        Nat.mul_zero, Nat.add_zero,
        Nat.mul_comm ((Word.toBitVec64 B).toNat / (Word.toBitVec64 C).toNat)
          (Word.toBitVec64 C).toNat]
    exact Nat.div_add_mod _ _

/-- Signed word class core (`divw`/`remw`): the 32-bit signed identity, transported through the
sign extensions. -/
private lemma euclid_limbs_sW_core {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hB : B.isU64) (hC : C.isU64)
    (h45 : f[4] + f[5] = 1) (h67 : f[6] + f[7] = 0) (h02 : f[0] + f[2] = 0)
    (hnotmin : ¬((Word.toBitVec64 B).setWidth 32 = BitVec.intMin 32
        ∧ (Word.toBitVec64 C).setWidth 32 = BitVec.allOnes 32)) :
    EuclidLimbEqs B C f := by
  obtain ⟨hb0v, hb1v, hb2v, hb3v⟩ := Word.lt_cases_of_isU64 hB
  obtain ⟨hc0v, hc1v, hc2v, hc3v⟩ := Word.lt_cases_of_isU64 hC
  have hsig : f[0] + f[2] + f[4] + f[5] = 1 := by linear_combination h02 + h45
  have h4567 : f[4] + f[5] + f[6] + f[7] = 1 := by linear_combination h45 + h67
  have hn67 : ¬f[6] + f[7] = 1 := by rw [h67]; exact zero_ne_one
  -- populate shapes on this class
  have hqb : quotBits B C f
      = if (Word.toBitVec64 C).setWidth 32 = 0 then BitVec.allOnes 64
        else (((Word.toBitVec64 B).setWidth 32).sdiv
            ((Word.toBitVec64 C).setWidth 32)).signExtend 64 := by
    simp only [quotBits]; rw [if_pos h45]
  have hrb : remBits B C f
      = if (Word.toBitVec64 C).setWidth 32 = 0
        then ((Word.toBitVec64 B).setWidth 32).signExtend 64
        else (((Word.toBitVec64 B).setWidth 32).srem
            ((Word.toBitVec64 C).setWidth 32)).signExtend 64 := by
    simp only [remBits]; rw [if_pos h45]
  have hqcb : quotCompBits B C f = quotBits B C f := by
    simp only [quotCompBits]; rw [if_neg hn67]
  have hrcb : remCompBits B C f = remBits B C f := by
    simp only [remCompBits]; rw [if_neg hn67]
  have hbc : bComp B f
      = #v[B[0], B[1], U16MSBOperation.populate_msb B[1] * 65535,
           U16MSBOperation.populate_msb B[1] * 65535] := by
    simp only [bComp]; rw [if_pos h45]
  have hcc : cComp C f
      = #v[C[0], C[1], U16MSBOperation.populate_msb C[1] * 65535,
           U16MSBOperation.populate_msb C[1] * 65535] := by
    simp only [cComp]; rw [if_pos h45]
  have hprod : ctqProd B C f
      = (Word.toBitVec64 (populateQuotComp B C f)).signExtend 128
        * (Word.toBitVec64 (cComp C f)).signExtend 128 := by
    simp only [ctqProd]; rw [if_pos hsig]
  have hqcv : Word.toBitVec64 (populateQuotComp B C f) = quotCompBits B C f :=
    wordOfBits_toBitVec64 _
  -- low-32 values of the raw reads
  have hb32 := setWidth32_toNat hB
  have hc32 := setWidth32_toNat hC
  -- the committed operands are sign extensions of the low-32 reads
  have hbcbv : Word.toBitVec64 (bComp B f)
      = ((Word.toBitVec64 B).setWidth 32).signExtend 64 := by
    rw [hbc]
    refine toBitVec64_signExtend_word _ _ (U16MSBOperation.populate_msb B[1])
      hb0v hb1v ?_ rfl rfl hb32
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    exact populate_msb_eq_ite hb1v
  have hccbv : Word.toBitVec64 (cComp C f)
      = ((Word.toBitVec64 C).setWidth 32).signExtend 64 := by
    rw [hcc]
    refine toBitVec64_signExtend_word _ _ (U16MSBOperation.populate_msb C[1])
      hc0v hc1v ?_ rfl rfl hc32
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    exact populate_msb_eq_ite hc1v
  -- sign cells
  have hbn : populateBNeg B f = if ((Word.toBitVec64 B).setWidth 32).msb then 1 else 0 := by
    rw [populateBNeg_def, hsig, one_mul]
    simp only [bMsbCell]
    rw [if_pos h4567, populate_msb_eq_ite hb1v]
    have hiff : ((Word.toBitVec64 B).setWidth 32).msb = true ↔ 32768 ≤ B[1].val := by
      rw [BitVec.msb_eq_decide, decide_eq_true_eq, hb32]
      omega
    by_cases hge : 32768 ≤ B[1].val
    · rw [if_pos hge, if_pos (hiff.mpr hge)]
    · rw [if_neg hge, if_neg (fun hm => hge (hiff.mp hm))]
  have hrn1 : populateRemNeg B C f
      = if 2 ^ 31 ≤ (remBits B C f).toNat % 2 ^ 32 then 1 else 0 := by
    rw [populateRemNeg_def, hsig, one_mul]
    simp only [remMsbCell, populateRemainder]
    rw [if_pos h4567]
    exact populate_msb_limb1 (remBits B C f)
  have hrn_of : ∀ y : BitVec 32, remBits B C f = y.signExtend 64 →
      populateRemNeg B C f = if y.msb then 1 else 0 := by
    intro y hy
    rw [hrn1, hy, sext64_toNat_mod32]
    have hms := BitVec.msb_eq_decide y
    by_cases hm : y.msb
    · rw [if_pos (show 2 ^ 31 ≤ y.toNat by
          rw [hm] at hms; exact of_decide_eq_true hms.symm), if_pos hm]
    · rw [if_neg (show ¬2 ^ 31 ≤ y.toNat by
          rw [Bool.not_eq_true] at hm; rw [hm] at hms
          exact of_decide_eq_false hms.symm), if_neg hm]
  -- the extended values
  have hZdef : bExtNat B f = (((Word.toBitVec64 B).setWidth 32).signExtend 64).toNat
      + (if ((Word.toBitVec64 B).setWidth 32).msb then 1 else 0) * (2 ^ 128 - 2 ^ 64) := by
    simp only [bExtNat]
    rw [← Word.toBitVec64_toNat (bComp_isU64 hB f), hbcbv, hbn, val_ite01]
  have hRdef_of : ∀ y : BitVec 32, remBits B C f = y.signExtend 64 →
      remExtNat B C f
        = (y.signExtend 64).toNat + (if y.msb then 1 else 0) * (2 ^ 128 - 2 ^ 64) := by
    intro y hy
    rw [remExtNat_eq, hrcb, hy, hrn_of y hy, val_ite01]
  have hZint : (bExtNat B f : ℤ) = ((Word.toBitVec64 B).setWidth 32).toInt
      + (if ((Word.toBitVec64 B).setWidth 32).msb then (2 : ℤ) ^ 128 else 0) := by
    rw [hZdef]
    exact extNat_int32 _ rfl
  by_cases hc320 : (Word.toBitVec64 C).setWidth 32 = 0
  · -- divisor zero (low 32): `X = 0`, `R = Z`, `k = 0`
    have hy : remBits B C f = ((Word.toBitVec64 B).setWidth 32).signExtend 64 := by
      rw [hrb, if_pos hc320]
    have hX0 : (ctqProd B C f).toNat = 0 := by
      rw [hprod, hccbv, hc320]
      have hz1 : (((0 : BitVec 32).signExtend 64).signExtend 128) = 0 := by
        rw [← BitVec.toNat_inj]
        simp
      rw [hz1]
      simp
    refine euclid_limbs_of_agg hB (Or.inr hsig) ⟨0, ?_⟩
    rw [hX0, hRdef_of _ hy, hZdef]
    simp
  · -- low-32 divisor nonzero: the 32-bit signed identity
    have hy : remBits B C f
        = (((Word.toBitVec64 B).setWidth 32).srem
            ((Word.toBitVec64 C).setWidth 32)).signExtend 64 := by
      rw [hrb, if_neg hc320]
    have hq : quotCompBits B C f
        = (((Word.toBitVec64 B).setWidth 32).sdiv
            ((Word.toBitVec64 C).setWidth 32)).signExtend 64 := by
      rw [hqcb, hqb, if_neg hc320]
    have hident := sdiv_srem_toInt_identity (not_and_or.mp hnotmin)
    have hPint : (ctqProd B C f).toInt
        = (((Word.toBitVec64 B).setWidth 32).sdiv ((Word.toBitVec64 C).setWidth 32)).toInt
          * ((Word.toBitVec64 C).setWidth 32).toInt := by
      rw [hprod, hqcv, hq, hccbv, signed_prod_toInt,
        BitVec.toInt_signExtend_of_le (by norm_num),
        BitVec.toInt_signExtend_of_le (by norm_num)]
    have hXint : ((ctqProd B C f).toNat : ℤ)
        = (((Word.toBitVec64 B).setWidth 32).sdiv ((Word.toBitVec64 C).setWidth 32)).toInt
            * ((Word.toBitVec64 C).setWidth 32).toInt
          + (if (ctqProd B C f).msb then (2 : ℤ) ^ 128 else 0) := by
      have h128 := toInt_eq_toNat_sub128' (ctqProd B C f)
      rw [hPint] at h128
      linear_combination -h128
    have hRint : (remExtNat B C f : ℤ)
        = (((Word.toBitVec64 B).setWidth 32).srem ((Word.toBitVec64 C).setWidth 32)).toInt
          + (if (((Word.toBitVec64 B).setWidth 32).srem
                ((Word.toBitVec64 C).setWidth 32)).msb then (2 : ℤ) ^ 128 else 0) := by
      rw [hRdef_of _ hy]
      exact extNat_int32 _ rfl
    have hcomb : ((ctqProd B C f).toNat : ℤ) + (remExtNat B C f : ℤ)
        = (bExtNat B f : ℤ)
          + ((if (ctqProd B C f).msb then (2 : ℤ) ^ 128 else 0)
            + (if (((Word.toBitVec64 B).setWidth 32).srem
                  ((Word.toBitVec64 C).setWidth 32)).msb then (2 : ℤ) ^ 128 else 0)
            - (if ((Word.toBitVec64 B).setWidth 32).msb then (2 : ℤ) ^ 128 else 0)) := by
      rw [hXint, hRint, hZint]
      linear_combination -hident
    exact euclid_limbs_of_agg hB (Or.inr hsig)
      (signed_agg (ctqProd B C f).isLt (remExtNat_lt B C (Or.inr hsig))
        (bExtNat_lt hB (Or.inr hsig)) hcomb)

/-- Unsigned word class core (`divuw`/`remuw`): zero-extended truncations, `k = 0`. -/
private lemma euclid_limbs_uW_core {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hB : B.isU64) (hC : C.isU64)
    (h45 : f[4] + f[5] = 0) (h67 : f[6] + f[7] = 1) (h02 : f[0] + f[2] = 0) :
    EuclidLimbEqs B C f := by
  obtain ⟨hb0v, hb1v, hb2v, hb3v⟩ := Word.lt_cases_of_isU64 hB
  obtain ⟨hc0v, hc1v, hc2v, hc3v⟩ := Word.lt_cases_of_isU64 hC
  have hsig0 : f[0] + f[2] + f[4] + f[5] = 0 := by linear_combination h02 + h45
  have hn45 : ¬f[4] + f[5] = 1 := by rw [h45]; exact zero_ne_one
  have hnsig : ¬f[0] + f[2] + f[4] + f[5] = 1 := by rw [hsig0]; exact zero_ne_one
  have hqb : quotBits B C f
      = if (Word.toBitVec64 C).setWidth 32 = 0 then BitVec.allOnes 64
        else (((Word.toBitVec64 B).setWidth 32).udiv
            ((Word.toBitVec64 C).setWidth 32)).signExtend 64 := by
    simp only [quotBits]; rw [if_neg hn45, if_pos h67]
  have hrb : remBits B C f
      = if (Word.toBitVec64 C).setWidth 32 = 0
        then ((Word.toBitVec64 B).setWidth 32).signExtend 64
        else (((Word.toBitVec64 B).setWidth 32).umod
            ((Word.toBitVec64 C).setWidth 32)).signExtend 64 := by
    simp only [remBits]; rw [if_neg hn45, if_pos h67]
  have hqcb : quotCompBits B C f = ((quotBits B C f).setWidth 32).setWidth 64 := by
    simp only [quotCompBits]; rw [if_pos h67]
  have hrcb : remCompBits B C f = ((remBits B C f).setWidth 32).setWidth 64 := by
    simp only [remCompBits]; rw [if_pos h67]
  have hbc : bComp B f = #v[B[0], B[1], 0, 0] := by
    simp only [bComp]; rw [if_neg hn45, if_pos h67]
  have hcc : cComp C f = #v[C[0], C[1], 0, 0] := by
    simp only [cComp]; rw [if_neg hn45, if_pos h67]
  have hprod : ctqProd B C f
      = (Word.toBitVec64 (populateQuotComp B C f)).setWidth 128
        * (Word.toBitVec64 (cComp C f)).setWidth 128 := by
    simp only [ctqProd]; rw [if_neg hnsig]
  have hbn0 : populateBNeg B f = 0 := by rw [populateBNeg_def, hsig0, zero_mul]
  have hrn0 : populateRemNeg B C f = 0 := by rw [populateRemNeg_def, hsig0, zero_mul]
  have hb32 := setWidth32_toNat hB
  have hc32 := setWidth32_toNat hC
  have hccn : (Word.toBitVec64 (cComp C f)).toNat
      = ((Word.toBitVec64 C).setWidth 32).toNat := by
    rw [Word.toBitVec64_toNat (cComp_isU64 hC f), hcc, Word.toNat_def, hc32]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero]
    omega
  have hZn : bExtNat B f = ((Word.toBitVec64 B).setWidth 32).toNat := by
    simp only [bExtNat]
    rw [hbc, Word.toNat_def, hbn0, hb32]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero]
    omega
  have hRn : remExtNat B C f = (remBits B C f).toNat % 2 ^ 32 := by
    rw [remExtNat_eq, hrcb, BitVec.toNat_setWidth_of_le (by norm_num), BitVec.toNat_setWidth,
        hrn0, ZMod.val_zero]
    omega
  have hqcn : (Word.toBitVec64 (populateQuotComp B C f)).toNat
      = (quotBits B C f).toNat % 2 ^ 32 := by
    have hqcv : Word.toBitVec64 (populateQuotComp B C f) = quotCompBits B C f :=
      wordOfBits_toBitVec64 _
    rw [hqcv, hqcb, BitVec.toNat_setWidth_of_le (by norm_num), BitVec.toNat_setWidth]
  have hXn : (ctqProd B C f).toNat
      = (quotBits B C f).toNat % 2 ^ 32 * ((Word.toBitVec64 C).setWidth 32).toNat := by
    have h1 : (Word.toBitVec64 (populateQuotComp B C f)).toNat < 2 ^ 32 := by
      rw [hqcn]; exact Nat.mod_lt _ (by norm_num)
    have h2 : (Word.toBitVec64 (cComp C f)).toNat < 2 ^ 32 := by
      rw [hccn]; exact BitVec.isLt _
    have hmul : (Word.toBitVec64 (populateQuotComp B C f)).toNat
        * (Word.toBitVec64 (cComp C f)).toNat < 2 ^ 128 := by
      have h := Nat.mul_le_mul
        (show (Word.toBitVec64 (populateQuotComp B C f)).toNat ≤ 2 ^ 32 - 1 by omega)
        (show (Word.toBitVec64 (cComp C f)).toNat ≤ 2 ^ 32 - 1 by omega)
      omega
    rw [hprod, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (show (Word.toBitVec64 (populateQuotComp B C f)).toNat < 2 ^ 128
          by omega),
        Nat.mod_eq_of_lt (show (Word.toBitVec64 (cComp C f)).toNat < 2 ^ 128 by omega),
        Nat.mod_eq_of_lt hmul, hqcn, hccn]
  by_cases hc320 : (Word.toBitVec64 C).setWidth 32 = 0
  · refine euclid_limbs_of_agg hB (Or.inl hsig0) ⟨0, ?_⟩
    have hcz : ((Word.toBitVec64 C).setWidth 32).toNat = 0 := by rw [hc320]; rfl
    rw [hXn, hcz, hRn, hrb, if_pos hc320, sext64_toNat_mod32, hZn]
    omega
  · refine euclid_limbs_of_agg hB (Or.inl hsig0) ⟨0, ?_⟩
    have hquot : (quotBits B C f).toNat % 2 ^ 32
        = ((Word.toBitVec64 B).setWidth 32).toNat
          / ((Word.toBitVec64 C).setWidth 32).toNat := by
      rw [hqb, if_neg hc320, sext64_toNat_mod32, BitVec.udiv_eq, BitVec.toNat_udiv]
    have hrem : remExtNat B C f
        = ((Word.toBitVec64 B).setWidth 32).toNat
          % ((Word.toBitVec64 C).setWidth 32).toNat := by
      rw [hRn, hrb, if_neg hc320, sext64_toNat_mod32, BitVec.umod_eq, BitVec.toNat_umod]
    rw [hXn, hquot, hrem, hZn, Nat.mul_zero, Nat.add_zero,
        Nat.mul_comm (((Word.toBitVec64 B).setWidth 32).toNat
          / ((Word.toBitVec64 C).setWidth 32).toNat)
          ((Word.toBitVec64 C).setWidth 32).toNat]
    exact Nat.div_add_mod _ _

/-! ## §2 The four class-bundle deliverables -/

/-- **Master Euclidean limb identities, signed 64-bit class** (`div`/`rem`, no overflow). The
no-overflow side condition is the primitive divisor/dividend exclusion; the Phase-6 assembler
bridges `is_overflow = 0` to it. -/
theorem euclid_limbs_s64 {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hB : B.isU64)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hcls : f[0] + f[2] = 1)
    (hnotmin : ¬(Word.toBitVec64 B = BitVec.intMin 64
        ∧ Word.toBitVec64 C = BitVec.allOnes 64)) :
    EuclidLimbEqs B C f := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h
  all_goals obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  all_goals first
    | (rw [h0, h2, add_zero] at hcls
       exact absurd hcls (Ne.symm one_ne_zero))
    | (exact euclid_limbs_s64_core hB (by rw [h4, h5, add_zero]) (by rw [h6, h7, add_zero])
        hcls hnotmin)

/-- **Master Euclidean limb identities, unsigned 64-bit class** (`divu`/`remu`). -/
theorem euclid_limbs_u64 {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hB : B.isU64)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hcls : f[1] + f[3] = 1) :
    EuclidLimbEqs B C f := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h
  all_goals obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  all_goals first
    | (rw [h1, h3, add_zero] at hcls
       exact absurd hcls (Ne.symm one_ne_zero))
    | (exact euclid_limbs_u64_core hB (by rw [h4, h5, add_zero]) (by rw [h6, h7, add_zero])
        (by rw [h0, h2, add_zero]))

/-- **Master Euclidean limb identities, signed word class** (`divw`/`remw`, no 32-bit overflow). -/
theorem euclid_limbs_sW {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hB : B.isU64) (hC : C.isU64)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hcls : f[4] + f[5] = 1)
    (hnotmin : ¬((Word.toBitVec64 B).setWidth 32 = BitVec.intMin 32
        ∧ (Word.toBitVec64 C).setWidth 32 = BitVec.allOnes 32)) :
    EuclidLimbEqs B C f := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h
  all_goals obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  all_goals first
    | (rw [h4, h5, add_zero] at hcls
       exact absurd hcls (Ne.symm one_ne_zero))
    | (exact euclid_limbs_sW_core hB hC hcls (by rw [h6, h7, add_zero])
        (by rw [h0, h2, add_zero]) hnotmin)

/-- **Master Euclidean limb identities, unsigned word class** (`divuw`/`remuw`). -/
theorem euclid_limbs_uW {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hB : B.isU64) (hC : C.isU64)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hcls : f[6] + f[7] = 1) :
    EuclidLimbEqs B C f := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h
  all_goals obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  all_goals first
    | (rw [h6, h7, add_zero] at hcls
       exact absurd hcls (Ne.symm one_ne_zero))
    | (exact euclid_limbs_uW_core hB hC (by rw [h4, h5, add_zero]) hcls
        (by rw [h0, h2, add_zero]))

end SP1Clean.DivRemChip
