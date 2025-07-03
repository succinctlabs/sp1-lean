import Mathlib

@[simp] abbrev BabyBearPrime : ℕ := 2013265921

alias BB := BabyBearPrime

-- dt: Need `#eval` strength to make this work on all OS
lemma prime_BabyBearPrime : Nat.Prime BabyBearPrime := by native_decide

instance : Fact (Nat.Prime BabyBearPrime) := ⟨prime_BabyBearPrime⟩

abbrev BabyBear : Type := Fin BabyBearPrime

instance : NeZero BabyBearPrime := by constructor; decide

instance Fin.noZeroDivisors_of_prime (p : ℕ)
    [hp : Fact (Nat.Prime (p + 1))] : NoZeroDivisors (Fin (p + 1)) := by
  refine IsDomain.to_noZeroDivisors (ZMod (p + 1))

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

@[simp] lemma ne_zero_2 : (2 : BabyBear) ≠ 0 := by simp
@[simp] lemma ne_zero_4 : (4 : BabyBear) ≠ 0 := by simp
@[simp] lemma ne_zero_8 : (8 : BabyBear) ≠ 0 := by simp
@[simp] lemma ne_zero_16 : (16 : BabyBear) ≠ 0 := by simp
@[simp] lemma ne_zero_32 : (32 : BabyBear) ≠ 0 := by simp
@[simp] lemma ne_zero_64 : (64 : BabyBear) ≠ 0 := by simp
@[simp] lemma ne_zero_128 : (128 : BabyBear) ≠ 0 := by simp
@[simp] lemma ne_zero_256 : (256 : BabyBear) ≠ 0 := by simp
@[simp] lemma ne_zero_65536 : (65536 : BabyBear) ≠ 0 := by simp

end const_vals

end BabyBear


-- dt: if we commit to `BabyBear` fully we should have `isTwoPow` class maybe

@[simp] lemma shiftl_1BB_eq_one : (1006632961 : BabyBear) <<< 1 = 1 := rfl
@[simp] lemma shiftl_2BB_eq_one : (1509949441 : BabyBear) <<< 2 = 1 := rfl
@[simp] lemma shiftl_3BB_eq_one : (1761607681 : BabyBear) <<< 3 = 1 := rfl
@[simp] lemma shiftl_8BB_eq_one : (2005401601 : BabyBear) <<< 8 = 1 := rfl
@[simp] lemma shiftl_16BB_eq_one : (2013235201 : BabyBear) <<< 16 = 1 := rfl

lemma inv_1BB_eq : (1006632961 : BabyBear)⁻¹ = 2 := by native_decide
lemma inv_2BB_eq : (1509949441 : BabyBear)⁻¹ = 4 := by native_decide
lemma inv_3BB_eq : (1761607681 : BabyBear)⁻¹ = 8 := by native_decide
lemma inv_8BB_eq : (2005401601 : BabyBear)⁻¹ = 256 := by native_decide
lemma inv_16BB_eq : (2013235201 : BabyBear)⁻¹ = 65536 := by native_decide

lemma inv_1BB_eq' : (1006632961 : BabyBear) = 2⁻¹ := by native_decide
lemma inv_2BB_eq' : (1509949441 : BabyBear) = 4⁻¹ := by native_decide
lemma inv_3BB_eq' : (1761607681 : BabyBear) = 8⁻¹ := by native_decide
lemma inv_8BB_eq' : (2005401601 : BabyBear) = 256⁻¹ := by native_decide
lemma inv_16BB_eq' : (2013235201 : BabyBear) = 65536⁻¹ := by native_decide

@[simp] lemma inv_mul_1BB_eq_one : (1006632961 : BabyBear) * 2 = 1 := by rfl
@[simp] lemma inv_mul_2BB_eq_one : (1509949441 : BabyBear) * 4 = 1 := by rfl
@[simp] lemma inv_mul_3BB_eq_one : (1761607681 : BabyBear) * 8 = 1 := by rfl
@[simp] lemma inv_mul_8BB_eq_one : (2005401601 : BabyBear) * 256 = 1 := by rfl
@[simp] lemma inv_mul_16BB_eq_one : (2013235201 : BabyBear) * 65536 = 1 := by rfl

@[simp] lemma mul_inv_1BB_eq_one : 2 * (1006632961 : BabyBear) = 1 := by rfl
@[simp] lemma mul_inv_2BB_eq_one : 4 * (1509949441 : BabyBear) = 1 := by rfl
@[simp] lemma mul_inv_3BB_eq_one : 8 * (1761607681 : BabyBear) = 1 := by rfl
@[simp] lemma mul_inv_8BB_eq_one : 256 * (2005401601 : BabyBear) = 1 := by rfl
@[simp] lemma mul_inv_16BB_eq_one : 65536 * (2013235201 : BabyBear) = 1 := by rfl

@[simp] lemma inv_mul_1BB_eq_iff : (1006632961 : BabyBear) * x = 1 ↔ x = 2 := by
  rw [inv_1BB_eq', inv_mul_eq_one₀ BabyBear.ne_zero_2, eq_comm]
@[simp] lemma inv_mul_2BB_eq_iff : (1509949441 : BabyBear) * x = 1 ↔ x = 4 := by
  rw [inv_2BB_eq', inv_mul_eq_one₀ BabyBear.ne_zero_4, eq_comm]
@[simp] lemma inv_mul_3BB_eq_iff : (1761607681 : BabyBear) * x = 1 ↔ x = 8 := by
  rw [inv_3BB_eq', inv_mul_eq_one₀ BabyBear.ne_zero_8, eq_comm]
@[simp] lemma inv_mul_8BB_eq_iff : (2005401601 : BabyBear) * x = 1 ↔ x = 256 := by
  rw [inv_8BB_eq', inv_mul_eq_one₀ BabyBear.ne_zero_256, eq_comm]
@[simp] lemma inv_mul_16BB_eq_iff : (2013235201 : BabyBear) * x = 1 ↔ x = 65536 := by
  rw [inv_16BB_eq', inv_mul_eq_one₀ BabyBear.ne_zero_65536, eq_comm]

@[simp] lemma inv_mul_1BB_eq_iff' : x * (1006632961 : BabyBear) = 1 ↔ x = 2 := by
  rw [mul_comm, inv_mul_1BB_eq_iff]
@[simp] lemma inv_mul_2BB_eq_iff' : x * (1509949441 : BabyBear) = 1 ↔ x = 4 := by
  rw [mul_comm, inv_mul_2BB_eq_iff]
@[simp] lemma inv_mul_3BB_eq_iff' : x * (1761607681 : BabyBear) = 1 ↔ x = 8 := by
  rw [mul_comm, inv_mul_3BB_eq_iff]
@[simp] lemma inv_mul_8BB_eq_iff' : x * (2005401601 : BabyBear) = 1 ↔ x = 256 := by
  rw [mul_comm, inv_mul_8BB_eq_iff]
@[simp] lemma inv_mul_16BB_eq_iff' : x * (2013235201 : BabyBear) = 1 ↔ x = 65536 := by
  rw [mul_comm, inv_mul_16BB_eq_iff]

-- dt: below should be handled more systematically like above

-- section base

-- -- TODO(gzgz): base should be some constant
-- abbrev base : BabyBear := 65536 -- 2^16
-- abbrev baseInv : BabyBear := 2013235201 -- 2^-16

-- @[simp] lemma val_base : (base : ℕ) = 65536 := rfl
-- @[simp] lemma val_baseInv : (baseInv : ℕ) = 2013235201 := rfl

-- @[simp] lemma baseInv_mul_base : (baseInv : BabyBear) * (base : BabyBear) = 1 := rfl
-- @[simp] lemma base_mul_baseInv : (base : BabyBear) * (baseInv : BabyBear) = 1 := rfl

-- @[simp] lemma base_ne_zero : (base : BabyBear) ≠ 0 := by simp [base]
-- @[simp] lemma baseInv_ne_zero : (baseInv : BabyBear) ≠ 0 := by simp [baseInv]

-- lemma baseInv_eq_inv_base : baseInv = base⁻¹ := by
--   rw [inv_eq_one_div, eq_div_iff] <;> simp

-- lemma base_eq_inv_baseInv : base = baseInv⁻¹ := by
--   rw [baseInv_eq_inv_base, inv_inv]

-- @[simp] lemma mul_baseInv_eq_one_iff (x : BabyBear) : x * baseInv = 1 ↔ x = base := by
--   rw [baseInv_eq_inv_base, mul_inv_eq_one₀ base_ne_zero]

-- @[simp] lemma baseInv_mul_eq_one_iff (x : BabyBear) : baseInv * x = 1 ↔ x = base := by
--   rw [mul_comm, mul_baseInv_eq_one_iff]

-- end base

section u3_base

@[simp] lemma u3_base_mul_u3_inv : (8 : BabyBear) * 1761607681 = 1 := rfl
@[simp] lemma u3_inv_mul_u3_base : (1761607681 : BabyBear) * 8 = 1 := rfl

lemma U3BB_inv : (1761607681 : BabyBear)⁻¹ = 8 := by
  have : (8 : BabyBear) ≠ 0 := by simp
  rw [inv_eq_iff_eq_inv, ← mul_left_inj' this, u3_inv_mul_u3_base]
  simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, inv_mul_cancel₀]

lemma U3BB_eq_inv : (1761607681 : BabyBear) = 8⁻¹ := by
  rw [← U3BB_inv, inv_inv]

@[simp] lemma shiftl_U3BB : (1761607681 : BabyBear) <<< 3 = 1 := rfl

end u3_base

section u8_base

@[simp] lemma u8_base_mul_u8_inv : (256 : BabyBear) * 2005401601 = 1 := rfl
@[simp] lemma u8_inv_mul_u8_base : (2005401601 : BabyBear) * 256 = 1 := rfl

lemma U8BB_inv : (2005401601 : BabyBear)⁻¹ = 256 := by
  have : (256 : BabyBear) ≠ 0 := by simp
  rw [inv_eq_iff_eq_inv, ← mul_left_inj' this, u8_inv_mul_u8_base]
  simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, inv_mul_cancel₀]

lemma U8BB_eq_inv : (2005401601 : BabyBear) = 256⁻¹ := by
  rw [← U8BB_inv, inv_inv]

@[simp] lemma shiftl_U8BB : (2005401601 : BabyBear) <<< 8 = 1 := rfl

end u8_base

section u16_base

@[simp] lemma u16_base_mul_u16_inv : (65536 : BabyBear) * 2013235201 = 1 := rfl
@[simp] lemma u16_inv_mul_u16_base : (2013235201 : BabyBear) * 65536 = 1 := rfl

lemma U16BB_inv : (2013235201 : BabyBear)⁻¹ = 65536 := by
  have : (65536 : BabyBear) ≠ 0 := by simp
  rw [inv_eq_iff_eq_inv, ← mul_left_inj' this]
  rw [u16_inv_mul_u16_base]
  simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, inv_mul_cancel₀]

lemma U16BB_eq_inv : (2013235201 : BabyBear) = 65536⁻¹ := by
  rw [← U16BB_inv]
  rw [inv_inv]

@[simp] lemma shiftl_U16BB : (2013235201 : BabyBear) <<< 16 = 1 := rfl

end u16_base
