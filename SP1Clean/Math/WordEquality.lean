import SP1Clean.Math.Word
import Mathlib.Tactic.IntervalCases

/-! # Uniqueness of bounded word encodings

Four bounded base-65536 limbs are determined by their unsigned value. These lemmas let fixed
tables and witness constructors move between field rows and semantic words without duplicating
limb arithmetic in chip proofs.
-/

namespace SP1Clean.Word

variable {p : ℕ} [NeZero p]

/-- Equal unsigned values identify all four bounded limbs. -/
theorem eq_of_toNat_eq {left right : Word (ZMod p)}
    (leftBound : left.isU64) (rightBound : right.isU64) (equal : left.toNat = right.toNat) :
    left = right := by
  obtain ⟨a0, a1, a2, a3⟩ := lt_cases_of_isU64 leftBound
  obtain ⟨b0, b1, b2, b3⟩ := lt_cases_of_isU64 rightBound
  rw [toNat_def, toNat_def] at equal
  apply Vector.ext
  intro index bound
  interval_cases index <;> exact ZMod.val_injective _ (by omega)

/-- Reassembly into a 64-bit word is injective on bounded limb encodings. -/
theorem eq_of_toBitVec64_eq {left right : Word (ZMod p)}
    (leftBound : left.isU64) (rightBound : right.isU64)
    (equal : left.toBitVec64 = right.toBitVec64) : left = right := by
  apply eq_of_toNat_eq leftBound rightBound
  simpa only [toBitVec64_toNat leftBound, toBitVec64_toNat rightBound] using congrArg BitVec.toNat equal

end SP1Clean.Word
