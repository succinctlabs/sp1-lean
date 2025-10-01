import SP1Foundations.Misc

notation "KB" => 2130706433
@[simp] lemma BB_eq : KB = 2130706433 := rfl

namespace KoalaBear

-- dt: Need `#eval`-level `native_decide` strength to make this work on all OS
lemma prime_KoalaBearPrime : Nat.Prime KB := by native_decide

instance Fact_BBPrime : Fact (Nat.Prime KB) := ⟨prime_KoalaBearPrime⟩
instance : NeZero KB := by constructor; decide

-- dt: Wouldn't need this if `ZMod` was the fundamental object for us.
instance : Field (Fin KB) := ZMod.instField KB
instance : NoZeroDivisors (Fin 2130706433) := Fin.noZeroDivisors_of_prime _ (hp := Fact_BBPrime)

section const_vals

lemma val_16 : ((16 : Fin KB) : ℕ) = 16 := rfl
lemma val_256 : ((256 : Fin KB) : ℕ) = 256 := rfl
lemma val_32768 : ((32768 : Fin KB) : ℕ) = 32768 := rfl
lemma val_65536 : ((65536 : Fin KB) : ℕ) = 65536 := rfl

lemma ne_zero_2 : (2 : Fin KB) ≠ 0 := by simp
lemma ne_zero_4 : (4 : Fin KB) ≠ 0 := by simp
lemma ne_zero_8 : (8 : Fin KB) ≠ 0 := by simp
lemma ne_zero_16 : (16 : Fin KB) ≠ 0 := by simp
lemma ne_zero_32 : (32 : Fin KB) ≠ 0 := by simp
lemma ne_zero_64 : (64 : Fin KB) ≠ 0 := by simp
lemma ne_zero_128 : (128 : Fin KB) ≠ 0 := by simp
lemma ne_zero_256 : (256 : Fin KB) ≠ 0 := by simp
lemma ne_zero_65536 : (65536 : Fin KB) ≠ 0 := by simp

end const_vals

lemma val_mod4_eq_zero (x : Fin KB) : x.val % 4 = 0 ↔ x % 4 = 0 := by
  rw [← Fin.val_inj]
  simp only [BB_eq, Fin.isValue, Fin.mod_val, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.zero_mod]

@[aesop safe forward]
lemma mul_diff_one_neq {a b c : Fin KB} : a * (b - c) = 1 → b ≠ c := by aesop

@[simp] lemma lt_65536_of_mul_inv_lt (x : Fin KB) (h : (x * 4⁻¹).val < 16384) :
    x.val < 65536 := by
  sorry

end KoalaBear

@[simp] lemma shiftl_1BB_eq_one : (1065353217 : Fin KB) <<< 1 = 1 := rfl
@[simp] lemma shiftl_2BB_eq_one : (1598029825 : Fin KB) <<< 2 = 1 := rfl
@[simp] lemma shiftl_3BB_eq_one : (1864368129 : Fin KB) <<< 3 = 1 := rfl
@[simp] lemma shiftl_8BB_eq_one : (2122383361 : Fin KB) <<< 8 = 1 := rfl
@[simp] lemma shiftl_16BB_eq_one : (2130673921 : Fin KB) <<< 16 = 1 := rfl

lemma inv_1BB_eq : (1065353217 : Fin KB)⁻¹ = 2 := by native_decide
lemma inv_2BB_eq : (1598029825 : Fin KB)⁻¹ = 4 := by native_decide
lemma inv_3BB_eq : (1864368129 : Fin KB)⁻¹ = 8 := by native_decide
lemma inv_8BB_eq : (2122383361 : Fin KB)⁻¹ = 256 := by native_decide
lemma inv_16BB_eq : (2130673921 : Fin KB)⁻¹ = 65536 := by native_decide

lemma inv_1BB_eq' : (1065353217 : Fin KB) = 2⁻¹ := by native_decide
lemma inv_2BB_eq' : (1598029825 : Fin KB) = 4⁻¹ := by native_decide
lemma inv_3BB_eq' : (1864368129 : Fin KB) = 8⁻¹ := by native_decide
lemma inv_8BB_eq' : (2122383361 : Fin KB) = 256⁻¹ := by native_decide
lemma inv_16BB_eq' : (2130673921 : Fin KB) = 65536⁻¹ := by native_decide

@[simp] lemma inv_mul_1BB_eq_one : (1065353217 : Fin KB) * 2 = 1 := by rfl
@[simp] lemma inv_mul_2BB_eq_one : (1598029825 : Fin KB) * 4 = 1 := by rfl
@[simp] lemma inv_mul_3BB_eq_one : (1864368129 : Fin KB) * 8 = 1 := by rfl
@[simp] lemma inv_mul_8BB_eq_one : (2122383361 : Fin KB) * 256 = 1 := by rfl
@[simp] lemma inv_mul_16BB_eq_one : (2130673921 : Fin KB) * 65536 = 1 := by rfl

@[simp] lemma mul_inv_1BB_eq_one : 2 * (1065353217 : Fin KB) = 1 := by rfl
@[simp] lemma mul_inv_2BB_eq_one : 4 * (1598029825 : Fin KB) = 1 := by rfl
@[simp] lemma mul_inv_3BB_eq_one : 8 * (1864368129 : Fin KB) = 1 := by rfl
@[simp] lemma mul_inv_8BB_eq_one : 256 * (2122383361 : Fin KB) = 1 := by rfl
@[simp] lemma mul_inv_16BB_eq_one : 65536 * (2130673921 : Fin KB) = 1 := by rfl

@[simp] lemma inv_mul_1BB_eq_iff : (1065353217 : Fin KB) * x = 1 ↔ x = 2 := by
  rw [inv_1BB_eq', inv_mul_eq_one₀ KoalaBear.ne_zero_2, eq_comm]
@[simp] lemma inv_mul_2BB_eq_iff : (1598029825 : Fin KB) * x = 1 ↔ x = 4 := by
  rw [inv_2BB_eq', inv_mul_eq_one₀ KoalaBear.ne_zero_4, eq_comm]
@[simp] lemma inv_mul_3BB_eq_iff : (1864368129 : Fin KB) * x = 1 ↔ x = 8 := by
  rw [inv_3BB_eq', inv_mul_eq_one₀ KoalaBear.ne_zero_8, eq_comm]
@[simp] lemma inv_mul_8BB_eq_iff : (2122383361 : Fin KB) * x = 1 ↔ x = 256 := by
  rw [inv_8BB_eq', inv_mul_eq_one₀ KoalaBear.ne_zero_256, eq_comm]
@[simp] lemma inv_mul_16BB_eq_iff : (2130673921 : Fin KB) * x = 1 ↔ x = 65536 := by
  rw [inv_16BB_eq', inv_mul_eq_one₀ KoalaBear.ne_zero_65536, eq_comm]

@[simp] lemma inv_mul_1BB_eq_iff' : x * (1065353217 : Fin KB) = 1 ↔ x = 2 := by
  rw [mul_comm, inv_mul_1BB_eq_iff]
@[simp] lemma inv_mul_2BB_eq_iff' : x * (1598029825 : Fin KB) = 1 ↔ x = 4 := by
  rw [mul_comm, inv_mul_2BB_eq_iff]
@[simp] lemma inv_mul_3BB_eq_iff' : x * (1864368129 : Fin KB) = 1 ↔ x = 8 := by
  rw [mul_comm, inv_mul_3BB_eq_iff]
@[simp] lemma inv_mul_8BB_eq_iff' : x * (2122383361 : Fin KB) = 1 ↔ x = 256 := by
  rw [mul_comm, inv_mul_8BB_eq_iff]
@[simp] lemma inv_mul_16BB_eq_iff' : x * (2130673921 : Fin KB) = 1 ↔ x = 65536 := by
  rw [mul_comm, inv_mul_16BB_eq_iff]

-- dt: remaining versions of these
@[simp] lemma mul_inv_16BB_eq_one_iff : x * (65536 : Fin KB)⁻¹ = 1 ↔ x = 65536 := by
  rw [mul_inv_eq_one₀ (by trivial)]

@[simp] lemma inv_16BB_zero_or_one {x : Fin KB} : x * 65536⁻¹ = 0 ∨ x * 65536⁻¹ = 1 ↔ x = 0 ∨ x = 65536
  := by aesop

namespace Int

lemma abs_cases {a : ℤ} : abs a = if 0 ≤ a then a else -a := by
  unfold abs; rw [Int.max_def]; omega

lemma sign_cases (a : ℤ) : a.sign = if a < 0 then -1 else if a = 0 then 0 else 1 := by
  by_cases a = 0
  . simp_all
  . by_cases 0 < a
    . rw [Int.sign_eq_one_of_pos (by omega)]; omega
    . rw [Int.sign_eq_neg_one_of_neg (by omega)]; omega

lemma split_nzp (a : ℤ) (P : Prop) :
  (a < 0 → P) → (a = 0 → P) → (0 < a → P) → P := by
  intro an az ap
  by_cases a = 0
  . apply az (by assumption)
  . by_cases 0 < a
    . apply ap (by omega)
    . apply an (by omega)

end Int
