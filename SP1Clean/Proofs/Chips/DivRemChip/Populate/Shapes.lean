import SP1Clean.Proofs.Chips.DivRemChip.Populate.Bounds
import SP1Clean.Proofs.Chips.DivRemChip.Soundness

/-! # `DivRemChip` populate value bundles — constraint shapes

Value-level forms of the chip's own constraints (`OwnAsserts.lean`) at the honest populate
witnesses: the one-hot flag destructor `flags_cases`, the operand-tie forms E20–E47
(`bComp`/`cComp` limbs against the raw reads), the quotient/remainder ↔ comp links E48–E91
(low limbs agree; high limbs are zero / the `msb`-fill on the word classes), the writeback
placement E184–E219 (`populateA`), and the definitional scal/misc cell forms
(E13/E15/E17/E19/E96/E99/E103). Everything is stated on the populate functions themselves —
no `env`, no `Expression` — so the completeness proof can `rw` these into constraint goals. -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The one-hot flag destructor -/

set_option linter.unusedSectionVars false in
/-- A field element with zero `val` is zero. -/
private lemma eq_zero_of_val {x : ZMod p} (h : x.val = 0) : x = 0 := by
  rw [← ZMod.natCast_zmod_val x, h, Nat.cast_zero]

set_option linter.unusedSectionVars false in
/-- A boolean field element with `val = 1` is one. -/
private lemma eq_one_of_val {x : ZMod p} (hx : x = 0 ∨ x = 1) (h : x.val = 1) : x = 1 := by
  rcases hx with h0 | h1
  · rw [h0, ZMod.val_zero] at h
    simp at h
  · exact h1

/-- **The 8-way one-hot destructor.** Eight boolean flags summing to `1` are exactly one of the
eight one-hot vectors `[div, divu, rem, remu, divw, remw, divuw, remuw]`. Proved by the val route
(`flags_val_sum` + `omega`), not a `2^8` case bash. -/
lemma flags_cases {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    (f[0] = 1 ∧ f[1] = 0 ∧ f[2] = 0 ∧ f[3] = 0 ∧ f[4] = 0 ∧ f[5] = 0 ∧ f[6] = 0 ∧ f[7] = 0) ∨
    (f[0] = 0 ∧ f[1] = 1 ∧ f[2] = 0 ∧ f[3] = 0 ∧ f[4] = 0 ∧ f[5] = 0 ∧ f[6] = 0 ∧ f[7] = 0) ∨
    (f[0] = 0 ∧ f[1] = 0 ∧ f[2] = 1 ∧ f[3] = 0 ∧ f[4] = 0 ∧ f[5] = 0 ∧ f[6] = 0 ∧ f[7] = 0) ∨
    (f[0] = 0 ∧ f[1] = 0 ∧ f[2] = 0 ∧ f[3] = 1 ∧ f[4] = 0 ∧ f[5] = 0 ∧ f[6] = 0 ∧ f[7] = 0) ∨
    (f[0] = 0 ∧ f[1] = 0 ∧ f[2] = 0 ∧ f[3] = 0 ∧ f[4] = 1 ∧ f[5] = 0 ∧ f[6] = 0 ∧ f[7] = 0) ∨
    (f[0] = 0 ∧ f[1] = 0 ∧ f[2] = 0 ∧ f[3] = 0 ∧ f[4] = 0 ∧ f[5] = 1 ∧ f[6] = 0 ∧ f[7] = 0) ∨
    (f[0] = 0 ∧ f[1] = 0 ∧ f[2] = 0 ∧ f[3] = 0 ∧ f[4] = 0 ∧ f[5] = 0 ∧ f[6] = 1 ∧ f[7] = 0) ∨
    (f[0] = 0 ∧ f[1] = 0 ∧ f[2] = 0 ∧ f[3] = 0 ∧ f[4] = 0 ∧ f[5] = 0 ∧ f[6] = 0 ∧ f[7] = 1) := by
  have hval := flags_val_sum hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
  rcases (by omega :
      f[0].val = 1 ∨ f[1].val = 1 ∨ f[2].val = 1 ∨ f[3].val = 1 ∨ f[4].val = 1 ∨
      f[5].val = 1 ∨ f[6].val = 1 ∨ f[7].val = 1) with h | h | h | h | h | h | h | h
  · refine Or.inl ⟨eq_one_of_val hf0 h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact eq_zero_of_val (by omega)
  · refine Or.inr <| Or.inl ⟨?_, eq_one_of_val hf1 h, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact eq_zero_of_val (by omega)
  · refine Or.inr <| Or.inr <| Or.inl ⟨?_, ?_, eq_one_of_val hf2 h, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact eq_zero_of_val (by omega)
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨?_, ?_, ?_, eq_one_of_val hf3 h, ?_, ?_, ?_, ?_⟩ <;> exact eq_zero_of_val (by omega)
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨?_, ?_, ?_, ?_, eq_one_of_val hf4 h, ?_, ?_, ?_⟩ <;> exact eq_zero_of_val (by omega)
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨?_, ?_, ?_, ?_, ?_, eq_one_of_val hf5 h, ?_, ?_⟩ <;> exact eq_zero_of_val (by omega)
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨?_, ?_, ?_, ?_, ?_, ?_, eq_one_of_val hf6 h, ?_⟩ <;> exact eq_zero_of_val (by omega)
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, eq_one_of_val hf7 h⟩ <;> exact eq_zero_of_val (by omega)

/-- The five flag sums consumed throughout the DivRem circuit are boolean under the one-hot flag
contract.  Factoring the one-hot case split here keeps it out of the whole-chip completeness term. -/
lemma flagSums_bool {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    (f[4] + f[5] + f[6] + f[7] = 0 ∨ f[4] + f[5] + f[6] + f[7] = 1) ∧
      (f[0] + f[2] + f[4] + f[5] = 0 ∨ f[0] + f[2] + f[4] + f[5] = 1) ∧
      (f[0] + f[1] + f[2] + f[3] = 0 ∨ f[0] + f[1] + f[2] + f[3] = 1) ∧
      (f[0] + f[2] = 0 ∨ f[0] + f[2] = 1) ∧
      (f[1] + f[3] = 0 ∨ f[1] + f[3] = 1) := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h <;>
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := h <;>
    rw [g0, g1, g2, g3, g4, g5, g6, g7] <;>
    norm_num

/-! ## Operand ties (E20–E47) -/

set_option linter.unusedSectionVars false in
/-- E20's value form: `bComp` limb 0 is the raw read's limb 0 in every branch. -/
lemma bComp_limb0 (B : Word (ZMod p)) (f : Vector (ZMod p) 8) : (bComp B f)[0] = B[0] := by
  unfold bComp; split_ifs <;> rfl

set_option linter.unusedSectionVars false in
/-- E22's value form: `bComp` limb 1 is the raw read's limb 1 in every branch. -/
lemma bComp_limb1 (B : Word (ZMod p)) (f : Vector (ZMod p) 8) : (bComp B f)[1] = B[1] := by
  unfold bComp; split_ifs <;> rfl

set_option linter.unusedSectionVars false in
/-- E21's value form: `cComp` limb 0 is the raw read's limb 0 in every branch. -/
lemma cComp_limb0 (C : Word (ZMod p)) (f : Vector (ZMod p) 8) : (cComp C f)[0] = C[0] := by
  unfold cComp; split_ifs <;> rfl

set_option linter.unusedSectionVars false in
/-- E23's value form: `cComp` limb 1 is the raw read's limb 1 in every branch. -/
lemma cComp_limb1 (C : Word (ZMod p)) (f : Vector (ZMod p) 8) : (cComp C f)[1] = C[1] := by
  unfold cComp; split_ifs <;> rfl

/-- E25–E29's value form: `bComp` limb 2 is the raw limb gated off the word classes plus the
`b_neg` sign fill gated on them. -/
lemma bComp_limb2 (B : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    (bComp B f)[2] = B[2] * (1 - (f[4] + f[5] + f[6] + f[7]))
      + populateBNeg B f * ((f[4] + f[5] + f[6] + f[7]) * 65535) := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h <;>
    simp [bComp, populateBNeg, bMsbCell, h0, h2, h4, h5, h6, h7]

/-- E37–E41's value form: as `bComp_limb2`, for limb 3. -/
lemma bComp_limb3 (B : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    (bComp B f)[3] = B[3] * (1 - (f[4] + f[5] + f[6] + f[7]))
      + populateBNeg B f * ((f[4] + f[5] + f[6] + f[7]) * 65535) := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h <;>
    simp [bComp, populateBNeg, bMsbCell, h0, h2, h4, h5, h6, h7]

/-- E31–E35's value form: as `bComp_limb2`, for the `c` operand. -/
lemma cComp_limb2 (C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    (cComp C f)[2] = C[2] * (1 - (f[4] + f[5] + f[6] + f[7]))
      + populateCNeg C f * ((f[4] + f[5] + f[6] + f[7]) * 65535) := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h <;>
    simp [cComp, populateCNeg, cMsbCell, h0, h2, h4, h5, h6, h7]

/-- E43–E47's value form: as `cComp_limb2`, for limb 3. -/
lemma cComp_limb3 (C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    (cComp C f)[3] = C[3] * (1 - (f[4] + f[5] + f[6] + f[7]))
      + populateCNeg C f * ((f[4] + f[5] + f[6] + f[7]) * 65535) := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h <;>
    simp [cComp, populateCNeg, cMsbCell, h0, h2, h4, h5, h6, h7]

/-! ## Comp links (E48–E91)

The word-class high-limb facts factor through one ℕ-level core: a `wordOfNat` word whose limbs
2/3 satisfy the `msb·65535` fill equations (at the ℕ level) satisfies them at the field level,
with the msb read off limb 1 by `U16MSBOperation.populate_msb`. `signExtend32_limbs` (the sign
extension of any 32-bit value) and `allOnes64_limbs` (the divisor-zero `allOnes` quotient)
instantiate it; `quotBits_shape`/`remBits_shape` show every word-class bit pattern is one of
those two forms. -/

set_option linter.unusedSectionVars false in
/-- Truncation `setWidth 32 |>.setWidth 64` keeps limb 0 (bits 0–15). -/
private lemma wordOfBits_setWidth32_limb0 (x : BitVec 64) :
    (wordOfBits (p := p) ((x.setWidth 32).setWidth 64))[0] = (wordOfBits (p := p) x)[0] := by
  simp only [wordOfBits, wordOfNat, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero]
  congr 1
  rw [BitVec.toNat_setWidth_of_le (by decide : (32 : ℕ) ≤ 64), BitVec.toNat_setWidth]
  omega

set_option linter.unusedSectionVars false in
/-- Truncation `setWidth 32 |>.setWidth 64` keeps limb 1 (bits 16–31). -/
private lemma wordOfBits_setWidth32_limb1 (x : BitVec 64) :
    (wordOfBits (p := p) ((x.setWidth 32).setWidth 64))[1] = (wordOfBits (p := p) x)[1] := by
  simp only [wordOfBits, wordOfNat, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  congr 1
  rw [BitVec.toNat_setWidth_of_le (by decide : (32 : ℕ) ≤ 64), BitVec.toNat_setWidth]
  omega

set_option linter.unusedSectionVars false in
/-- Truncation `setWidth 32 |>.setWidth 64` zeroes limbs 2 and 3 (the value is `< 2^32`). -/
private lemma wordOfBits_setWidth32_hi (x : BitVec 64) :
    (wordOfBits (p := p) ((x.setWidth 32).setWidth 64))[2] = 0 ∧
      (wordOfBits (p := p) ((x.setWidth 32).setWidth 64))[3] = 0 := by
  have ht : ((x.setWidth 32).setWidth 64).toNat = x.toNat % 2 ^ 32 := by
    rw [BitVec.toNat_setWidth_of_le (by decide : (32 : ℕ) ≤ 64), BitVec.toNat_setWidth]
  refine ⟨?_, ?_⟩ <;>
    simp only [wordOfBits, wordOfNat, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ht] <;>
    exact (congrArg Nat.cast (by omega : _ = 0)).trans Nat.cast_zero

set_option linter.unusedSectionVars false in
/-- ℕ-level core of the word-class high-limb fill: if limbs 2/3 of `n` are
`(limb 1's high bit) · 65535` at the ℕ level, the committed word's limbs 2/3 are the
`populate_msb (limb 1) · 65535` fill at the field level. -/
private lemma wordOfNat_limbs23_eq_msb_fill {n : ℕ}
    (h2 : n / 2 ^ 32 % 2 ^ 16 = n / 2 ^ 16 % 2 ^ 16 / 32768 * 65535)
    (h3 : n / 2 ^ 48 % 2 ^ 16 = n / 2 ^ 16 % 2 ^ 16 / 32768 * 65535) :
    (wordOfNat (p := p) n)[2]
        = U16MSBOperation.populate_msb ((wordOfNat (p := p) n)[1]) * 65535 ∧
      (wordOfNat (p := p) n)[3]
        = U16MSBOperation.populate_msb ((wordOfNat (p := p) n)[1]) * 65535 := by
  have hp : 2 ^ 24 < p := Fact.out
  have h1v : ((n / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p).val = n / 2 ^ 16 % 2 ^ 16 :=
    ZMod.val_natCast_of_lt (by omega)
  refine ⟨?_, ?_⟩ <;>
    simp only [wordOfNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, U16MSBOperation.populate_msb, h1v] <;>
    first
      | (rw [h2, Nat.cast_mul]; norm_num)
      | (rw [h3, Nat.cast_mul]; norm_num)

set_option linter.unusedSectionVars false in
/-- **Sign-extension high limbs.** For any 32-bit `x`, limbs 2/3 of the committed
`x.signExtend 64` word are the all-`msb` fill `populate_msb (limb 1) · 65535`
(`BitVec.toNat_signExtend`: the extension adds `2^64 - 2^32` exactly when `x.msb`). -/
private lemma signExtend32_limbs (x : BitVec 32) :
    (wordOfBits (p := p) (x.signExtend 64))[2]
        = U16MSBOperation.populate_msb ((wordOfBits (p := p) (x.signExtend 64))[1]) * 65535 ∧
      (wordOfBits (p := p) (x.signExtend 64))[3]
        = U16MSBOperation.populate_msb ((wordOfBits (p := p) (x.signExtend 64))[1]) * 65535 := by
  have hx : x.toNat < 2 ^ 32 := x.isLt
  have hse : (x.signExtend 64).toNat = x.toNat + if x.msb then 2 ^ 64 - 2 ^ 32 else 0 := by
    rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by decide : (32 : ℕ) ≤ 64)]
  have hmsb : (if x.msb then 2 ^ 64 - 2 ^ 32 else 0)
      = if 2 ^ (32 - 1) ≤ x.toNat then 2 ^ 64 - 2 ^ 32 else 0 := by
    rw [BitVec.msb_eq_decide x]; simp
  refine wordOfNat_limbs23_eq_msb_fill ?_ ?_ <;> rw [hse, hmsb] <;> split <;> omega

set_option linter.unusedSectionVars false in
/-- The divisor-zero quotient `allOnes 64` also carries the msb fill (all limbs `65535`,
`populate_msb 65535 = 1`). -/
private lemma allOnes64_limbs :
    (wordOfBits (p := p) (BitVec.allOnes 64))[2]
        = U16MSBOperation.populate_msb ((wordOfBits (p := p) (BitVec.allOnes 64))[1]) * 65535 ∧
      (wordOfBits (p := p) (BitVec.allOnes 64))[3]
        = U16MSBOperation.populate_msb ((wordOfBits (p := p) (BitVec.allOnes 64))[1]) * 65535 := by
  have hall : (BitVec.allOnes 64).toNat = 2 ^ 64 - 1 := BitVec.toNat_allOnes
  have h2 : (BitVec.allOnes 64).toNat / 2 ^ 32 % 2 ^ 16
      = (BitVec.allOnes 64).toNat / 2 ^ 16 % 2 ^ 16 / 32768 * 65535 := by
    rw [hall]; omega
  have h3 : (BitVec.allOnes 64).toNat / 2 ^ 48 % 2 ^ 16
      = (BitVec.allOnes 64).toNat / 2 ^ 16 % 2 ^ 16 / 32768 * 65535 := by
    rw [hall]; omega
  exact wordOfNat_limbs23_eq_msb_fill h2 h3

set_option linter.unusedSectionVars false in
/-- Any bit pattern that is `allOnes` or a sign-extended 32-bit value commits to a word whose
limbs 2/3 are the `populate_msb (limb 1) · 65535` fill. -/
private lemma wordOfBits_msb_fill {y : BitVec 64}
    (hy : y = BitVec.allOnes 64 ∨ ∃ x : BitVec 32, y = x.signExtend 64) :
    (wordOfBits (p := p) y)[2]
        = U16MSBOperation.populate_msb ((wordOfBits (p := p) y)[1]) * 65535 ∧
      (wordOfBits (p := p) y)[3]
        = U16MSBOperation.populate_msb ((wordOfBits (p := p) y)[1]) * 65535 := by
  rcases hy with rfl | ⟨x, rfl⟩
  · exact allOnes64_limbs
  · exact signExtend32_limbs x

set_option linter.unusedSimpArgs false in
/-- On the word classes the quotient bit pattern is `allOnes` (divisor zero) or a sign-extended
32-bit value (both `sdiv` and `udiv` results are sign-extended — Rust's `as i32 as i64 as u64`). -/
private lemma quotBits_shape {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hW : f[4] + f[5] + f[6] + f[7] = 1) :
    quotBits B C f = BitVec.allOnes 64 ∨
      ∃ x : BitVec 32, quotBits B C f = x.signExtend 64 := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  all_goals first
    | (simp only [h4, h5, h6, h7, add_zero, zero_add] at hW
       exact absurd hW zero_ne_one)
    | (simp only [quotBits, h0, h2, h4, h5, h6, h7, add_zero, zero_add, zero_ne_one,
         eq_self_iff_true, if_true, if_false]
       split
       · exact Or.inl rfl
       · exact Or.inr ⟨_, rfl⟩)

set_option linter.unusedSimpArgs false in
/-- On the word classes the remainder bit pattern is always a sign-extended 32-bit value (the
divisor-zero branch returns the sign-extended low dividend in **both** W-classes). -/
private lemma remBits_shape {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hW : f[4] + f[5] + f[6] + f[7] = 1) :
    remBits B C f = BitVec.allOnes 64 ∨
      ∃ x : BitVec 32, remBits B C f = x.signExtend 64 := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  all_goals first
    | (simp only [h4, h5, h6, h7, add_zero, zero_add] at hW
       exact absurd hW zero_ne_one)
    | (simp only [remBits, h0, h2, h4, h5, h6, h7, add_zero, zero_add, zero_ne_one,
         eq_self_iff_true, if_true, if_false]
       split <;> exact Or.inr ⟨_, rfl⟩)

set_option linter.unusedSimpArgs false in
/-- Under one-hot flags, a signed-word class (`divw`/`remw`) forces the unsigned-word flags to
zero. -/
private lemma flags67_eq_zero_of_sum45 {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hW : f[4] + f[5] = 1) : f[6] = 0 ∧ f[7] = 0 := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  all_goals first
    | exact ⟨h6, h7⟩
    | (simp only [h4, h5, add_zero, zero_add] at hW
       exact absurd hW zero_ne_one)

set_option linter.unusedSimpArgs false in
/-- Under one-hot flags, a 64-bit class forces the unsigned-word flags to zero. -/
private lemma flags67_eq_zero_of_sum0123 {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (h64 : f[0] + f[1] + f[2] + f[3] = 1) : f[6] = 0 ∧ f[7] = 0 := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  all_goals first
    | exact ⟨h6, h7⟩
    | (simp only [h0, h1, h2, h3, add_zero, zero_add] at h64
       exact absurd h64 zero_ne_one)

set_option linter.unusedSectionVars false in
/-- E48's value form: `quotient_comp` limb 0 equals `quotient` limb 0 (the unsigned-word
truncation only touches the high 32 bits). -/
lemma quotComp_limb0 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateQuotComp B C f)[0] = (populateQuotient B C f)[0] := by
  unfold populateQuotComp quotCompBits populateQuotient
  split_ifs
  exacts [wordOfBits_setWidth32_limb0 _, rfl]

set_option linter.unusedSectionVars false in
/-- E49's value form: `quotient_comp` limb 1 equals `quotient` limb 1. -/
lemma quotComp_limb1 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateQuotComp B C f)[1] = (populateQuotient B C f)[1] := by
  unfold populateQuotComp quotCompBits populateQuotient
  split_ifs
  exacts [wordOfBits_setWidth32_limb1 _, rfl]

set_option linter.unusedSectionVars false in
/-- E70's value form: `remainder_comp` limb 0 equals `remainder` limb 0. -/
lemma remComp_limb0 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateRemComp B C f)[0] = (populateRemainder B C f)[0] := by
  unfold populateRemComp remCompBits populateRemainder
  split_ifs
  exacts [wordOfBits_setWidth32_limb0 _, rfl]

set_option linter.unusedSectionVars false in
/-- E71's value form: `remainder_comp` limb 1 equals `remainder` limb 1. -/
lemma remComp_limb1 (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateRemComp B C f)[1] = (populateRemainder B C f)[1] := by
  unfold populateRemComp remCompBits populateRemainder
  split_ifs
  exacts [wordOfBits_setWidth32_limb1 _, rfl]

set_option linter.unusedSectionVars false in
/-- E50–E51/E60–E61's value form: on the unsigned-word class `quotient_comp`'s high limbs are
zero (the computational quotient is the **zero**-extended low 32 bits). -/
lemma quotComp_hi_unsignedW (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hW : f[6] + f[7] = 1) :
    (populateQuotComp B C f)[2] = 0 ∧ (populateQuotComp B C f)[3] = 0 := by
  unfold populateQuotComp quotCompBits; rw [if_pos hW]
  exact wordOfBits_setWidth32_hi _

set_option linter.unusedSectionVars false in
/-- E72–E73/E82–E83's value form: as `quotComp_hi_unsignedW`, for `remainder_comp`. -/
lemma remComp_hi_unsignedW (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hW : f[6] + f[7] = 1) :
    (populateRemComp B C f)[2] = 0 ∧ (populateRemComp B C f)[3] = 0 := by
  unfold populateRemComp remCompBits; rw [if_pos hW]
  exact wordOfBits_setWidth32_hi _

/-- E52–E54/E62–E64's value form: on the signed-word class `quotient_comp`'s high limbs are the
`quot_msb · 65535` sign fill. -/
lemma quotComp_hi_signedW (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hW : f[4] + f[5] = 1) :
    (populateQuotComp B C f)[2] = quotMsbCell B C f * 65535 ∧
      (populateQuotComp B C f)[3] = quotMsbCell B C f * 65535 := by
  obtain ⟨h6, h7⟩ := flags67_eq_zero_of_sum45 hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hW
  have hword : f[4] + f[5] + f[6] + f[7] = 1 := by
    rw [h6, h7, add_zero, add_zero]; exact hW
  have hcomp : quotCompBits B C f = quotBits B C f := by
    simp [quotCompBits, h6, h7]
  have hcell : quotMsbCell B C f
      = U16MSBOperation.populate_msb (populateQuotient B C f)[1] := by
    unfold quotMsbCell; rw [if_pos hword]
  unfold populateQuotComp; rw [hcomp, hcell]
  exact wordOfBits_msb_fill (quotBits_shape hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hword)

/-- E74–E76/E84–E86's value form: as `quotComp_hi_signedW`, for `remainder_comp` with
`rem_msb`. -/
lemma remComp_hi_signedW (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hW : f[4] + f[5] = 1) :
    (populateRemComp B C f)[2] = remMsbCell B C f * 65535 ∧
      (populateRemComp B C f)[3] = remMsbCell B C f * 65535 := by
  obtain ⟨h6, h7⟩ := flags67_eq_zero_of_sum45 hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hW
  have hword : f[4] + f[5] + f[6] + f[7] = 1 := by
    rw [h6, h7, add_zero, add_zero]; exact hW
  have hcomp : remCompBits B C f = remBits B C f := by
    simp [remCompBits, h6, h7]
  have hcell : remMsbCell B C f
      = U16MSBOperation.populate_msb (populateRemainder B C f)[1] := by
    unfold remMsbCell; rw [if_pos hword]
  unfold populateRemComp; rw [hcomp, hcell]
  exact wordOfBits_msb_fill (remBits_shape hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hword)

/-- E55–E57/E65–E67's value form: on **every** word class the writeback `quotient`'s high limbs
are the `quot_msb · 65535` sign fill (`divuw` also sign-extends its 32-bit result; the
divisor-zero `allOnes` quotient fills consistently with `populate_msb 65535 = 1`). -/
lemma quotient_hi_word (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hW : f[4] + f[5] + f[6] + f[7] = 1) :
    (populateQuotient B C f)[2] = quotMsbCell B C f * 65535 ∧
      (populateQuotient B C f)[3] = quotMsbCell B C f * 65535 := by
  have hcell : quotMsbCell B C f
      = U16MSBOperation.populate_msb (populateQuotient B C f)[1] := by
    unfold quotMsbCell; rw [if_pos hW]
  rw [hcell]
  exact wordOfBits_msb_fill (quotBits_shape hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hW)

/-- E77–E79/E87–E89's value form: as `quotient_hi_word`, for the writeback `remainder` with
`rem_msb`. -/
lemma remainder_hi_word (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hW : f[4] + f[5] + f[6] + f[7] = 1) :
    (populateRemainder B C f)[2] = remMsbCell B C f * 65535 ∧
      (populateRemainder B C f)[3] = remMsbCell B C f * 65535 := by
  have hcell : remMsbCell B C f
      = U16MSBOperation.populate_msb (populateRemainder B C f)[1] := by
    unfold remMsbCell; rw [if_pos hW]
  rw [hcell]
  exact wordOfBits_msb_fill (remBits_shape hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hW)

/-- E58–E59/E68–E69's value form: on the 64-bit classes `quotient_comp`'s high limbs equal
`quotient`'s (the truncation gate is off). -/
lemma quotComp_hi_64 (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (h64 : f[0] + f[1] + f[2] + f[3] = 1) :
    (populateQuotComp B C f)[2] = (populateQuotient B C f)[2] ∧
      (populateQuotComp B C f)[3] = (populateQuotient B C f)[3] := by
  obtain ⟨h6, h7⟩ := flags67_eq_zero_of_sum0123 hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h64
  have hcomp : quotCompBits B C f = quotBits B C f := by
    simp [quotCompBits, h6, h7]
  unfold populateQuotComp populateQuotient; rw [hcomp]
  exact ⟨rfl, rfl⟩

/-- E80–E81/E90–E91's value form: as `quotComp_hi_64`, for `remainder_comp`. -/
lemma remComp_hi_64 (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (h64 : f[0] + f[1] + f[2] + f[3] = 1) :
    (populateRemComp B C f)[2] = (populateRemainder B C f)[2] ∧
      (populateRemComp B C f)[3] = (populateRemainder B C f)[3] := by
  obtain ⟨h6, h7⟩ := flags67_eq_zero_of_sum0123 hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h64
  have hcomp : remCompBits B C f = remBits B C f := by
    simp [remCompBits, h6, h7]
  unfold populateRemComp populateRemainder; rw [hcomp]
  exact ⟨rfl, rfl⟩

/-! ## Writeback placement (E184–E219) -/

set_option linter.unusedSectionVars false in
/-- E184…E214's value form (div family): the writeback `a` is the quotient. -/
lemma populateA_div (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hdiv : f[0] + f[1] + f[4] + f[6] = 1) :
    populateA B C f = populateQuotient B C f := by
  unfold populateA; rw [if_pos hdiv]

set_option linter.unusedSimpArgs false in
/-- E189…E219's value form (rem family): the writeback `a` is the remainder (needs one-hot to
rule the div-gate out). -/
lemma populateA_rem (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hrem : f[2] + f[3] + f[5] + f[7] = 1) :
    populateA B C f = populateRemainder B C f := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with h | h | h | h | h | h | h | h <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  all_goals first
    | (simp only [h2, h3, h5, h7, add_zero, zero_add] at hrem
       exact absurd hrem zero_ne_one)
    | (have hdiv : ¬f[0] + f[1] + f[4] + f[6] = 1 := by
         rw [h0, h1, h4, h6]; simp
       unfold populateA; rw [if_neg hdiv, if_pos hrem])

/-! ## Scal/misc cell definitional forms (E13/E15/E17/E19/E96/E99/E103) -/

set_option linter.unusedSectionVars false in
/-- E96's value form: scal slot 0 is `is_overflow`. -/
lemma populateScal_0 (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateScal ir B C f)[0] = populateIsOverflow ir B C f := rfl

set_option linter.unusedSectionVars false in
/-- E15's value form: scal slot 1 is `b_neg`. -/
lemma populateScal_1 (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateScal ir B C f)[1] = populateBNeg B f := rfl

set_option linter.unusedSectionVars false in
/-- E99's value form: scal slot 2 is `b_neg · (1 − is_overflow)`. -/
lemma populateScal_2 (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateScal ir B C f)[2]
      = populateBNeg B f * (1 - populateIsOverflow ir B C f) := rfl

set_option linter.unusedSectionVars false in
/-- E103's value form: scal slot 3 is `(1 − b_neg) · (1 − is_overflow)`. -/
lemma populateScal_3 (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateScal ir B C f)[3]
      = (1 - populateBNeg B f) * (1 - populateIsOverflow ir B C f) := rfl

set_option linter.unusedSectionVars false in
/-- E13's value form: scal slot 4 is `is_real · (1 − is_word)`. -/
lemma populateScal_4 (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateScal ir B C f)[4] = ir * (1 - (f[4] + f[5] + f[6] + f[7])) := rfl

set_option linter.unusedSectionVars false in
/-- E17's value form: scal slot 5 is `rem_neg`. -/
lemma populateScal_5 (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateScal ir B C f)[5] = populateRemNeg B C f := rfl

set_option linter.unusedSectionVars false in
/-- E19's value form: scal slot 6 is `c_neg`. -/
lemma populateScal_6 (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateScal ir B C f)[6] = populateCNeg C f := rfl

set_option linter.unusedSectionVars false in
/-- Misc slot 0 is the `abs_c_alu_event` multiplicity `c_neg · is_real`. -/
lemma populateMisc_0 (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateMisc ir B C f)[0] = populateCNeg C f * ir := rfl

set_option linter.unusedSectionVars false in
/-- Misc slot 1 is the `abs_rem_alu_event` multiplicity `rem_neg · is_real`. -/
lemma populateMisc_1 (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateMisc ir B C f)[1] = populateRemNeg B C f * ir := rfl

set_option linter.unusedSectionVars false in
/-- Misc slot 2 is the `remainder_check_multiplicity` gate. -/
lemma populateMisc_2 (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (populateMisc ir B C f)[2] = ltGate ir C f := rfl

set_option linter.unusedSectionVars false in
/-- E15's defining product: `b_neg = is_signed_type · b_msb`. -/
lemma populateBNeg_def (B : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    populateBNeg B f = (f[0] + f[2] + f[4] + f[5]) * bMsbCell B f := rfl

set_option linter.unusedSectionVars false in
/-- E19's defining product: `c_neg = is_signed_type · c_msb`. -/
lemma populateCNeg_def (C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    populateCNeg C f = (f[0] + f[2] + f[4] + f[5]) * cMsbCell C f := rfl

set_option linter.unusedSectionVars false in
/-- E17's defining product: `rem_neg = is_signed_type · rem_msb`. -/
lemma populateRemNeg_def (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    populateRemNeg B C f = (f[0] + f[2] + f[4] + f[5]) * remMsbCell B C f := rfl

end SP1Clean.DivRemChip
