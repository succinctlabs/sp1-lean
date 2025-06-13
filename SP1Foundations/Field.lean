import Mathlib

@[simp] abbrev BabyBearPrime : ℕ := 2013265921

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

namespace BabyBear

@[aesop 50% forward]
lemma lt_babyBearPrime (x : BabyBear) : x.val < BabyBearPrime := x.2

instance : Field BabyBear := ZMod.instField BabyBearPrime

section const_vals

lemma eq_one_iff_val_eq_one (x : BabyBear) : x = 1 ↔ x.val = 1 := by aesop

lemma eq_zero_iff_val_eq_zero (x : BabyBear) : x = 0 ↔ x.val = 0 := by aesop

@[simp] lemma val_16 : ((16 : BabyBear) : ℕ) = 16 := rfl
@[simp] lemma val_256 : ((256 : BabyBear) : ℕ) = 256 := rfl
@[simp] lemma val_32768 : ((32768 : BabyBear) : ℕ) = 32768 := rfl
@[simp] lemma val_65536 : ((65536 : BabyBear) : ℕ) = 65536 := rfl

end const_vals

end BabyBear

section base

-- TODO(gzgz): base should be some constant
abbrev base : BabyBear := 65536 -- 2^16
abbrev baseInv : BabyBear := 2013235201 -- 2^-16

@[simp] lemma val_base : (base : ℕ) = 65536 := rfl
@[simp] lemma val_baseInv : (baseInv : ℕ) = 2013235201 := rfl

@[simp] lemma baseInv_mul_base : (baseInv : BabyBear) * (base : BabyBear) = 1 := rfl
@[simp] lemma base_mul_baseInv : (base : BabyBear) * (baseInv : BabyBear) = 1 := rfl

@[simp] lemma base_ne_zero : (base : BabyBear) ≠ 0 := by simp [base]
@[simp] lemma baseInv_ne_zero : (baseInv : BabyBear) ≠ 0 := by simp [baseInv]

lemma baseInv_eq_inv_base : baseInv = base⁻¹ := by
  rw [inv_eq_one_div, eq_div_iff] <;> simp

lemma base_eq_inv_baseInv : base = baseInv⁻¹ := by
  rw [baseInv_eq_inv_base, inv_inv]

@[simp] lemma mul_baseInv_eq_zero_iff (x : BabyBear) : x * baseInv = 1 ↔ x = base := by
  rw [baseInv_eq_inv_base, mul_inv_eq_one₀ base_ne_zero]

@[simp] lemma baseInv_mul_eq_zero_iff (x : BabyBear) : baseInv * x = 1 ↔ x = base := by
  rw [mul_comm, mul_baseInv_eq_zero_iff]

end base
