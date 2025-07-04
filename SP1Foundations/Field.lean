import Mathlib

abbrev BabyBearPrime : ℕ := 2013265921
abbrev BB : ℕ := 2013265921

-- @[simp] lemma BabyBearPrime_eq : BabyBearPrime = 2013265921 := rfl
@[simp] lemma BB_eq : BB = 2013265921 := rfl

-- dt: Need `#eval` strength to make this work on all OS
-- lemma prime_BabyBearPrime : Nat.Prime BabyBearPrime := by native_decide
lemma prime_BabyBearPrime : Nat.Prime BB := by native_decide

instance Fact_BBPrime : Fact (Nat.Prime BB) := ⟨prime_BabyBearPrime⟩

instance : NeZero BB := by constructor; decide
-- instance : NeZero BabyBearPrime := by constructor; decide

instance Fin.noZeroDivisors_of_prime (p : ℕ)
    [hp : Fact (Nat.Prime (p + 1))] : NoZeroDivisors (Fin (p + 1)) := by
  refine IsDomain.to_noZeroDivisors (ZMod (p + 1))

namespace BabyBear

instance : Field (Fin BB) := ZMod.instField BB
instance : NoZeroDivisors (Fin 2013265921) := Fin.noZeroDivisors_of_prime _ (hp := Fact_BBPrime)

section const_vals

@[simp] lemma val_16 : ((16 : Fin BB) : ℕ) = 16 := rfl
@[simp] lemma val_256 : ((256 : Fin BB) : ℕ) = 256 := rfl
@[simp] lemma val_32768 : ((32768 : Fin BB) : ℕ) = 32768 := rfl
@[simp] lemma val_65536 : ((65536 : Fin BB) : ℕ) = 65536 := rfl

@[simp] lemma ne_zero_2 : (2 : Fin BB) ≠ 0 := by simp
@[simp] lemma ne_zero_4 : (4 : Fin BB) ≠ 0 := by simp
@[simp] lemma ne_zero_8 : (8 : Fin BB) ≠ 0 := by simp
@[simp] lemma ne_zero_16 : (16 : Fin BB) ≠ 0 := by simp
@[simp] lemma ne_zero_32 : (32 : Fin BB) ≠ 0 := by simp
@[simp] lemma ne_zero_64 : (64 : Fin BB) ≠ 0 := by simp
@[simp] lemma ne_zero_128 : (128 : Fin BB) ≠ 0 := by simp
@[simp] lemma ne_zero_256 : (256 : Fin BB) ≠ 0 := by simp
@[simp] lemma ne_zero_65536 : (65536 : Fin BB) ≠ 0 := by simp

end const_vals

end BabyBear


-- dt: if we commit to `Fin BB` fully we should have `isTwoPow` class maybe

@[simp] lemma shiftl_1BB_eq_one : (1006632961 : Fin BB) <<< 1 = 1 := rfl
@[simp] lemma shiftl_2BB_eq_one : (1509949441 : Fin BB) <<< 2 = 1 := rfl
@[simp] lemma shiftl_3BB_eq_one : (1761607681 : Fin BB) <<< 3 = 1 := rfl
@[simp] lemma shiftl_8BB_eq_one : (2005401601 : Fin BB) <<< 8 = 1 := rfl
@[simp] lemma shiftl_16BB_eq_one : (2013235201 : Fin BB) <<< 16 = 1 := rfl

lemma inv_1BB_eq : (1006632961 : Fin BB)⁻¹ = 2 := by native_decide
lemma inv_2BB_eq : (1509949441 : Fin BB)⁻¹ = 4 := by native_decide
lemma inv_3BB_eq : (1761607681 : Fin BB)⁻¹ = 8 := by native_decide
lemma inv_8BB_eq : (2005401601 : Fin BB)⁻¹ = 256 := by native_decide
lemma inv_16BB_eq : (2013235201 : Fin BB)⁻¹ = 65536 := by native_decide

lemma inv_1BB_eq' : (1006632961 : Fin BB) = 2⁻¹ := by native_decide
lemma inv_2BB_eq' : (1509949441 : Fin BB) = 4⁻¹ := by native_decide
lemma inv_3BB_eq' : (1761607681 : Fin BB) = 8⁻¹ := by native_decide
lemma inv_8BB_eq' : (2005401601 : Fin BB) = 256⁻¹ := by native_decide
lemma inv_16BB_eq' : (2013235201 : Fin BB) = 65536⁻¹ := by native_decide

@[simp] lemma inv_mul_1BB_eq_one : (1006632961 : Fin BB) * 2 = 1 := by rfl
@[simp] lemma inv_mul_2BB_eq_one : (1509949441 : Fin BB) * 4 = 1 := by rfl
@[simp] lemma inv_mul_3BB_eq_one : (1761607681 : Fin BB) * 8 = 1 := by rfl
@[simp] lemma inv_mul_8BB_eq_one : (2005401601 : Fin BB) * 256 = 1 := by rfl
@[simp] lemma inv_mul_16BB_eq_one : (2013235201 : Fin BB) * 65536 = 1 := by rfl

@[simp] lemma mul_inv_1BB_eq_one : 2 * (1006632961 : Fin BB) = 1 := by rfl
@[simp] lemma mul_inv_2BB_eq_one : 4 * (1509949441 : Fin BB) = 1 := by rfl
@[simp] lemma mul_inv_3BB_eq_one : 8 * (1761607681 : Fin BB) = 1 := by rfl
@[simp] lemma mul_inv_8BB_eq_one : 256 * (2005401601 : Fin BB) = 1 := by rfl
@[simp] lemma mul_inv_16BB_eq_one : 65536 * (2013235201 : Fin BB) = 1 := by rfl

@[simp] lemma inv_mul_1BB_eq_iff : (1006632961 : Fin BB) * x = 1 ↔ x = 2 := by
  rw [inv_1BB_eq', inv_mul_eq_one₀ BabyBear.ne_zero_2, eq_comm]
@[simp] lemma inv_mul_2BB_eq_iff : (1509949441 : Fin BB) * x = 1 ↔ x = 4 := by
  rw [inv_2BB_eq', inv_mul_eq_one₀ BabyBear.ne_zero_4, eq_comm]
@[simp] lemma inv_mul_3BB_eq_iff : (1761607681 : Fin BB) * x = 1 ↔ x = 8 := by
  rw [inv_3BB_eq', inv_mul_eq_one₀ BabyBear.ne_zero_8, eq_comm]
@[simp] lemma inv_mul_8BB_eq_iff : (2005401601 : Fin BB) * x = 1 ↔ x = 256 := by
  rw [inv_8BB_eq', inv_mul_eq_one₀ BabyBear.ne_zero_256, eq_comm]
@[simp] lemma inv_mul_16BB_eq_iff : (2013235201 : Fin BB) * x = 1 ↔ x = 65536 := by
  rw [inv_16BB_eq', inv_mul_eq_one₀ BabyBear.ne_zero_65536, eq_comm]

@[simp] lemma inv_mul_1BB_eq_iff' : x * (1006632961 : Fin BB) = 1 ↔ x = 2 := by
  rw [mul_comm, inv_mul_1BB_eq_iff]
@[simp] lemma inv_mul_2BB_eq_iff' : x * (1509949441 : Fin BB) = 1 ↔ x = 4 := by
  rw [mul_comm, inv_mul_2BB_eq_iff]
@[simp] lemma inv_mul_3BB_eq_iff' : x * (1761607681 : Fin BB) = 1 ↔ x = 8 := by
  rw [mul_comm, inv_mul_3BB_eq_iff]
@[simp] lemma inv_mul_8BB_eq_iff' : x * (2005401601 : Fin BB) = 1 ↔ x = 256 := by
  rw [mul_comm, inv_mul_8BB_eq_iff]
@[simp] lemma inv_mul_16BB_eq_iff' : x * (2013235201 : Fin BB) = 1 ↔ x = 65536 := by
  rw [mul_comm, inv_mul_16BB_eq_iff]

-- dt: things below should be folded into the above

section u3_base

@[simp] lemma u3_base_mul_u3_inv : (8 : Fin BB) * 1761607681 = 1 := rfl
@[simp] lemma u3_inv_mul_u3_base : (1761607681 : Fin BB) * 8 = 1 := rfl

lemma U3BB_inv : (1761607681 : Fin BB)⁻¹ = 8 := by
  have : (8 : Fin BB) ≠ 0 := by simp
  rw [inv_eq_iff_eq_inv, ← mul_left_inj' this, u3_inv_mul_u3_base]
  simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, inv_mul_cancel₀]

lemma U3BB_eq_inv : (1761607681 : Fin BB) = 8⁻¹ := by
  rw [← U3BB_inv, inv_inv]

@[simp] lemma shiftl_U3BB : (1761607681 : Fin BB) <<< 3 = 1 := rfl

end u3_base

section u8_base

@[simp] lemma u8_base_mul_u8_inv : (256 : Fin BB) * 2005401601 = 1 := rfl
@[simp] lemma u8_inv_mul_u8_base : (2005401601 : Fin BB) * 256 = 1 := rfl

lemma U8BB_inv : (2005401601 : Fin BB)⁻¹ = 256 := by
  have : (256 : Fin BB) ≠ 0 := by simp
  rw [inv_eq_iff_eq_inv, ← mul_left_inj' this, u8_inv_mul_u8_base]
  simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, inv_mul_cancel₀]

lemma U8BB_eq_inv : (2005401601 : Fin BB) = 256⁻¹ := by
  rw [← U8BB_inv, inv_inv]

@[simp] lemma shiftl_U8BB : (2005401601 : Fin BB) <<< 8 = 1 := rfl

end u8_base

section u16_base

@[simp] lemma u16_base_mul_u16_inv : (65536 : Fin BB) * 2013235201 = 1 := rfl
@[simp] lemma u16_inv_mul_u16_base : (2013235201 : Fin BB) * 65536 = 1 := rfl

lemma U16BB_inv : (2013235201 : Fin BB)⁻¹ = 65536 := by
  have : (65536 : Fin BB) ≠ 0 := by simp
  rw [inv_eq_iff_eq_inv, ← mul_left_inj' this]
  rw [u16_inv_mul_u16_base]
  simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, inv_mul_cancel₀]

lemma U16BB_eq_inv : (2013235201 : Fin BB) = 65536⁻¹ := by
  rw [← U16BB_inv]
  rw [inv_inv]

@[simp] lemma shiftl_U16BB : (2013235201 : Fin BB) <<< 16 = 1 := rfl

end u16_base
