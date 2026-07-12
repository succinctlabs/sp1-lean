import SP1Clean.Math.Word
import SP1Clean.Extracted.LtOperationSigned
import SP1Clean.Native.Operations.LtOperationUnsigned.RawSpec
import SP1Clean.Native.Operations.U16MSBOperation.RawSpec
import Mathlib.Tactic.LinearCombination

/-! # `LtOperationSigned` — the arithmetic core (`RawSpec` + the sign-bias keystone)

Signed/unsigned word less-than. A selector `is_signed` chooses the mode: when set, the top limbs are
sign-adjusted by flipping the high bit (`b[3] + is_signed·2^15 - 2^16·b_msb`, via two
`U16MSBOperation`s that witness the sign bits `b_msb`, `c_msb`), and the adjusted words are fed to
`LtOperationUnsigned`. When `is_signed = 0` the adjustment is the identity and the sign-bit ranges
are not enforced.

`RawSpec` transcribes the literal constraint meaning at `is_real = 1` with `is_signed` free. The
keystone is the sign-bias identity (`adj_bias`): biasing the top limb by `2^15` is `+2^63 mod 2^64`,
so an unsigned `<` of the biased words is the signed `<` (`toInt`) of the originals
(`toInt_compare_of_bias`). `ltSigned_semantic` is the soundness readout consumed by `Formal.lean`
(`result_semantic`) and the composing chips. -/

namespace SP1Clean.LtOperationSigned

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-! ## Sign-bias arithmetic

The signed compare flips bit 15 of the top limb (bit 63 of the word): the adjusted limb
`e13 = x + 32768 - 65536·msb` biases the value by `2^63 mod 2^64`, so an unsigned compare
of the adjusted words is the signed compare of the originals. -/

/-- The biased top limb `x + 32768 - 65536·msb` (with `msb = [x ≥ 2^15]`) is itself a 16-bit value,
and its `ℕ`-value lifts to the integer bias `x.val + 2^15 - 2^16·msb`. -/
lemma adj_limb {x : ZMod p} (hx : x.val < 2 ^ 16) :
    ((x + 32768 - 65536 * (if 32768 ≤ x.val then (1 : ZMod p) else 0)).val : ℤ)
        = (x.val : ℤ) + 32768 - 65536 * (if 32768 ≤ x.val then 1 else 0)
      ∧ (x + 32768 - 65536 * (if 32768 ≤ x.val then (1 : ZMod p) else 0)).val < 2 ^ 16 := by
  have hp : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  by_cases hsign : 32768 ≤ x.val
  · simp only [if_pos hsign, mul_one]
    have hval : (x + 32768 - 65536 : ZMod p).val = x.val - 32768 := by
      have e : ((x.val - 32768 : ℕ) : ZMod p) = x + 32768 - 65536 := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val]; push_cast; ring
      rw [← e]; exact ZMod.val_natCast_of_lt (show x.val - 32768 < p by omega)
    rw [hval]; refine ⟨by omega, by omega⟩
  · simp only [if_neg hsign, mul_zero, sub_zero]
    have hval : (x + 32768 : ZMod p).val = x.val + 32768 := by
      have e : ((x.val + 32768 : ℕ) : ZMod p) = x + 32768 := by
        push_cast [ZMod.natCast_zmod_val]; ring
      rw [← e]; exact ZMod.val_natCast_of_lt (show x.val + 32768 < p by omega)
    rw [hval]; refine ⟨by push_cast; omega, by omega⟩

/-- **Sign-bias keystone.** For a 64-bit word `b`, the `toNat` of the word with its top limb biased
(bit 15 flipped: `e13 = b[3] + 2^15 - 2^16·[b[3] ≥ 2^15]`) equals `(toBitVec64 b).toInt + 2^63`. Hence
an unsigned `<` of two biased words is a signed `<` of the originals. -/
lemma adj_bias {b : Word (ZMod p)} (hb : b.isU64) :
    ((Word.toNat (#v[b[0], b[1], b[2],
        b[3] + 32768 - 65536 * (if 32768 ≤ b[3].val then (1 : ZMod p) else 0)] : Word (ZMod p))) : ℤ)
      = (Word.toBitVec64 b).toInt + 2 ^ 63 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hval, _⟩ := adj_limb h3
  rw [Word.toNat_def, BitVec.toInt_eq_toNat_cond, Word.toBitVec64_toNat hb, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at hval ⊢
  by_cases hsign : 32768 ≤ b[3].val
  · rw [if_neg (by omega : ¬ 2 * (b[0].val + b[1].val * 2 ^ 16 + b[2].val * 2 ^ 32
        + b[3].val * 2 ^ 48) < 2 ^ 64)]
    simp only [if_pos hsign] at hval ⊢; push_cast at hval ⊢; omega
  · rw [if_pos (by omega : 2 * (b[0].val + b[1].val * 2 ^ 16 + b[2].val * 2 ^ 32
        + b[3].val * 2 ^ 48) < 2 ^ 64)]
    simp only [if_neg hsign] at hval ⊢; push_cast at hval ⊢; omega

/-- Transfer: with the two top limbs biased by their sign bits, the **unsigned** `<` of the biased
words is the **signed** `<` (`toInt`) of the originals. -/
lemma toInt_compare_of_bias {b cc : Word (ZMod p)} (hb : b.isU64) (hcc : cc.isU64)
    {bm cm : ZMod p}
    (hbm : bm = if 32768 ≤ b[3].val then 1 else 0)
    (hcm : cm = if 32768 ≤ cc[3].val then 1 else 0) :
    (Word.toNat (#v[b[0], b[1], b[2], b[3] + 32768 - 65536 * bm] : Word (ZMod p))
        < Word.toNat (#v[cc[0], cc[1], cc[2], cc[3] + 32768 - 65536 * cm] : Word (ZMod p)))
      ↔ (Word.toBitVec64 b).toInt < (Word.toBitVec64 cc).toInt := by
  subst hbm hcm
  have hb' := adj_bias hb
  have hcc' := adj_bias hcc
  omega

omit [Fact (2 ^ 17 < p)] in
/-- For 64-bit words, `toBitVec64` equality is `toNat` equality (it round-trips through `toNat`). Used
to carry the unsigned core's `toNat`-equality up to the signed semantics' `toBitVec64` equality. -/
lemma toBitVec64_eq_iff {b cc : Word (ZMod p)} (hb : b.isU64) (hcc : cc.isU64) :
    (Word.toBitVec64 b = Word.toBitVec64 cc) ↔ (Word.toNat b = Word.toNat cc) := by
  constructor
  · intro h; rw [← Word.toBitVec64_toNat hb, ← Word.toBitVec64_toNat hcc, h]
  · intro h; apply BitVec.eq_of_toNat_eq
    rw [Word.toBitVec64_toNat hb, Word.toBitVec64_toNat hcc, h]

/-- Literal meaning of SP1's `LtOperationSigned` constraint list at `is_real = 1`, with `is_signed`
free: the two `is_signed`-gated MSB sub-lists and the composed unsigned compare on the adjusted
words. -/
def RawSpec (b cc : Word (ZMod p)) (cols : Extracted.LtOperationSigned (ZMod p))
    (is_signed : ZMod p) : Prop :=
  let bm := cols.b_msb.msb; let cm := cols.c_msb.msb
  let e13 := b[3] + is_signed * 32768 - 65536 * bm
  let e17 := cc[3] + is_signed * 32768 - 65536 * cm
  (is_signed = 0 ∨ is_signed = 1) ∧ (bm = 0 ∨ bm = 1) ∧
    (is_signed ≠ 0 → (2 * b[3] - bm * 65536).val < 2 ^ 16) ∧
  (is_signed = 0 ∨ is_signed = 1) ∧ (cm = 0 ∨ cm = 1) ∧
    (is_signed ≠ 0 → (2 * cc[3] - cm * 65536).val < 2 ^ 16) ∧
  LtOperationUnsigned.RawSpec #v[b[0], b[1], b[2], e13] #v[cc[0], cc[1], cc[2], e17] cols.result ∧
  (is_signed = 0 ∨ is_signed = 1) ∧
  ((is_signed - 1) * bm = 0) ∧ ((is_signed - 1) * cm = 0)

set_option maxHeartbeats 800000 in
/-- Soundness readout from `RawSpec` (consumed by `Formal.lean`'s `result_semantic` and the composing
chips): the compare `bit` is the signed (`is_signed = 1`, via `toInt` of the biased words) /
unsigned (`is_signed = 0`) less-than indicator, and on the unsigned branch the flag sum is `0`
exactly when the operands are equal. Loose-variable form (no `Inputs`/`Spec` dependency) so it stays
out of the `Formal` import cycle. -/
theorem ltSigned_semantic {b cc : Word (ZMod p)} {cols : Extracted.LtOperationSigned (ZMod p)}
    {is_signed : ZMod p}
    (hb : Word.isU64 b) (hcc : Word.isU64 cc)
    (h_raw : RawSpec b cc cols is_signed) :
    (cols.result.u16_compare_operation.bit =
      if (if is_signed = 1
          then (Word.toBitVec64 b).toInt < (Word.toBitVec64 cc).toInt
          else Word.toNat b < Word.toNat cc)
        then 1 else 0) ∧
    (is_signed = 0 →
      ((cols.result.u16_flags[0] + cols.result.u16_flags[1] + cols.result.u16_flags[2]
          + cols.result.u16_flags[3] = 0)
        ↔ Word.toBitVec64 b = Word.toBitVec64 cc)) ∧
    (is_signed = 0 →
      (cols.result.u16_flags[0] + cols.result.u16_flags[1] + cols.result.u16_flags[2]
          + cols.result.u16_flags[3] = 0 ∨
       cols.result.u16_flags[0] + cols.result.u16_flags[1] + cols.result.u16_flags[2]
          + cols.result.u16_flags[3] = 1)) := by
  simp only [RawSpec] at h_raw
  obtain ⟨hs1, hbm_b, hrange_b, -, hcm_b, hrange_c, h_uns, -, h_pb, h_pc⟩ := h_raw
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc
  have h01 : (0 : ZMod p) ≠ 1 := by
    intro h; haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have := congrArg ZMod.val h; rw [ZMod.val_zero, ZMod.val_one] at this; exact absurd this (by norm_num)
  rcases hs1 with hs | hs
  · -- `is_signed = 0`: `bm = cm = 0`, the unsigned compare on the unbiased words.
    have hbm0 : cols.b_msb.msb = 0 := by have h := h_pb; rw [hs] at h; linear_combination -h
    have hcm0 : cols.c_msb.msb = 0 := by have h := h_pc; rw [hs] at h; linear_combination -h
    rw [hs, hbm0, hcm0] at h_uns
    simp only [zero_mul, mul_zero, sub_zero, add_zero] at h_uns
    have hbit := LtOperationUnsigned.ltUnsigned_semantic
      #v[b[0], b[1], b[2], b[3]]
      #v[cc[0], cc[1], cc[2], cc[3]]
      (Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
        (by simpa using hb3))
      (Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
        (by simpa using hc3)) h_uns
    refine ⟨?_, fun _ => ?_, fun _ => ?_⟩
    · rw [hbit.1]
      simp [hs, Word.toNat_def, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
    · rw [toBitVec64_eq_iff hb hcc]
      have key := hbit.2
      simp only [Word.toNat_def, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at key ⊢
      exact key
    · -- the unsigned `RawSpec`'s flag-sum-binary conjunct (6th), on the unbiased words.
      exact h_uns.2.2.2.2.2.1
  · -- `is_signed = 1`: `bm`/`cm` are the sign bits, the unsigned compare of the bias-flipped words.
    have hbm : cols.b_msb.msb = if 32768 ≤ b[3].val then 1 else 0 :=
      U16MSBOperation.msb_of_raw hb3
        ⟨hbm_b, by
          have h := hrange_b (by rw [hs]; norm_num)
          simpa using h⟩
    have hcm : cols.c_msb.msb = if 32768 ≤ cc[3].val then 1 else 0 :=
      U16MSBOperation.msb_of_raw hc3
        ⟨hcm_b, by
          have h := hrange_c (by rw [hs]; norm_num)
          simpa using h⟩
    rw [hs] at h_uns
    simp only [one_mul] at h_uns
    have hbU : (b[3] + 32768 - 65536 * cols.b_msb.msb).val < 2 ^ 16 := by
      rw [hbm]; exact (adj_limb hb3).2
    have hcU : (cc[3] + 32768 - 65536 * cols.c_msb.msb).val < 2 ^ 16 := by
      rw [hcm]; exact (adj_limb hc3).2
    have hbit := LtOperationUnsigned.ltUnsigned_semantic
      #v[b[0], b[1], b[2], b[3] + 32768 - 65536 * cols.b_msb.msb]
      #v[cc[0], cc[1], cc[2], cc[3] + 32768 - 65536 * cols.c_msb.msb]
      (Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
        (by simpa using hbU))
      (Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
        (by simpa using hcU)) h_uns
    refine ⟨?_, fun h => absurd (h ▸ hs) h01, fun h => absurd (h ▸ hs) h01⟩
    rw [hbit.1]
    simp only [hs, ↓reduceIte, toInt_compare_of_bias hb hcc hbm hcm]

end SP1Clean.LtOperationSigned
