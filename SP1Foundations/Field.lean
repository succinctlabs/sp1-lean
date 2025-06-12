import Mathlib

abbrev BabyBearPrime : ℕ := 2013265921
abbrev p : ℕ := 2013265921 -- temp

lemma prime_BabyBearPrime : Nat.Prime BabyBearPrime := by
  -- norm_num doesn't work on OSX?
  sorry

instance : Fact (Nat.Prime BabyBearPrime) := ⟨prime_BabyBearPrime⟩

abbrev BabyBear : Type := Fin BabyBearPrime

instance : NeZero BabyBearPrime := by constructor; decide

instance Fin.noZeroDivisors_of_prime (p : ℕ)
    [hp : Fact (Nat.Prime (p + 1))] : NoZeroDivisors (Fin (p + 1)) := by
  have : IsDomain (ZMod (p + 1)) := ZMod.instIsDomain (hp := ⟨hp.1⟩)
  simp [ZMod] at this
  sorry

lemma fin_val_simp' {n : ℕ} :
    (@Fin.val BabyBearPrime (@OfNat.ofNat.{0} BabyBear n (@Fin.instOfNat BabyBearPrime instNeZeroNatBabyBearPrime n))) = n % BabyBearPrime := rfl

lemma fin_val_simp {n : ℕ} (Hlt : n < BabyBearPrime) :
  (@Fin.val BabyBearPrime (@OfNat.ofNat.{0} BabyBear n (@Fin.instOfNat BabyBearPrime instNeZeroNatBabyBearPrime n))) = n := by
  simp [BabyBearPrime, OfNat.ofNat] at *; assumption

namespace BabyBear

instance : Field BabyBear := ZMod.instField BabyBearPrime

section const_vals

lemma eq_one_iff_val_eq_one (x : BabyBear) : x = 1 ↔ x.val = 1 := by
  rw [← Fin.val_one, Fin.val_inj]

@[simp] lemma val_256 : ((256 : BabyBear) : ℕ) = 256 := rfl

@[simp] lemma val_65536 : ((65536 : BabyBear) : ℕ) = 65536 := rfl

end const_vals

end BabyBear
