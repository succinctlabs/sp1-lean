import SP1Foundations.Misc

notation "BB" => 2013265921
@[simp] lemma BB_eq : BB = 2013265921 := rfl

namespace BabyBear

-- dt: Need `#eval`-level `native_decide` strength to make this work on all OS
lemma prime_BabyBearPrime : Nat.Prime BB := by native_decide

instance Fact_BBPrime : Fact (Nat.Prime BB) := ⟨prime_BabyBearPrime⟩
instance : NeZero BB := by constructor; decide

-- dt: Wouldn't need this if `ZMod` was the fundamental object for us.
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

lemma val_mod4_eq_zero (x : Fin BB) : x.val % 4 = 0 ↔ x % 4 = 0 := by
  rw [← Fin.val_inj]
  simp only [BB_eq, Fin.isValue, Fin.mod_val, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.zero_mod]

end BabyBear

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

-- dt: remaining versions of these
@[simp] lemma mul_inv_16BB_eq_one_iff : x * (65536 : Fin BB)⁻¹ = 1 ↔ x = 65536 := by
  rw [mul_inv_eq_one₀ (by trivial)]

@[simp] lemma inv_16BB_zero_or_one {x : Fin BB} : x * 65536⁻¹ = 0 ∨ x * 65536⁻¹ = 1 ↔ x = 0 ∨ x = 65536
  := by aesop
