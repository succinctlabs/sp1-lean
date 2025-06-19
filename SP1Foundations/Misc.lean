import mathlib

/-!
# Misc Lemmas Used in Verification

File for random lemmas that don't fit anywhere else (e.g. lemmas about nat).
Would be good to eventually contribute these back to mathlib.
-/

lemma Nat.mod_eq_zero_iff_of_lt (x y : ℕ) (h : x < y) : x % y = 0 ↔ x = 0 := by
  have : x / y = 0 := by aesop
  rw [Nat.mod_def, this, mul_zero, Nat.sub_zero]
