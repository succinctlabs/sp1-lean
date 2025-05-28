import Mathlib

abbrev BabyBearPrime : ℕ := 2013265921

lemma prime_BabyBearPrime : Nat.Prime BabyBearPrime := by
  -- norm_num doesn't work on OSX?
  sorry

abbrev BabyBear : Type := Fin BabyBearPrime

instance : NeZero BabyBearPrime := by constructor; decide

instance : NoZeroDivisors BabyBear := by
  have : IsDomain (ZMod BabyBearPrime) := ZMod.instIsDomain (hp := ⟨prime_BabyBearPrime⟩)
  simp [ZMod] at this
  infer_instance

lemma fin_val_simp {n : ℕ} (Hlt : n < BabyBearPrime) :
  (@Fin.val BabyBearPrime (@OfNat.ofNat.{0} BabyBear n (@Fin.instOfNat BabyBearPrime instNeZeroNatBabyBearPrime n))) = n := by
  simp [BabyBearPrime, OfNat.ofNat] at *; assumption
