import SP1Foundations.Misc

notation "KB" => 2130706433
@[simp] lemma BB_eq : KB = 2130706433 := rfl

/-- `Fin n`-level mod equals zero iff the underlying `Nat` mod does. Generic over any
`Fin n`; the only dependence was on `(m : Fin n).val = m.val`. Useful because the
statement naturally arises when bridging between bitvector and modular views. -/
lemma Fin.val_mod_eq_zero_iff {n : ℕ} [NeZero n] (x m : Fin n) :
    x.val % m.val = 0 ↔ x % m = 0 := by
  rw [← Fin.val_inj]; simp [Fin.mod_val]

/-- Literal-compatible variant of `Fin.val_mod_eq_zero_iff`: takes the modulus as a `ℕ`
literal (rather than `m.val` for some `m : Fin n`). The Nat-literal form of `m` on the
LHS is what SP1 chip proofs actually see (e.g. `Main[i].val % 4 = 0`), so this is the
version that fires in `simp` calls. -/
lemma Fin.val_mod_eq_zero_iff_of_lt {n : ℕ} [NeZero n] {x : Fin n} {m : ℕ} (hm : m < n) :
    x.val % m = 0 ↔ x % (Fin.ofNat n m) = 0 := by
  conv_lhs => rw [show m = (Fin.ofNat n m).val from (Nat.mod_eq_of_lt hm).symm]
  exact Fin.val_mod_eq_zero_iff x (Fin.ofNat n m)

namespace KoalaBear

-- dt: Need `#eval`-level `native_decide` strength to make this work on all OS
lemma prime_KoalaBearPrime : Nat.Prime KB := by native_decide

instance Fact_BBPrime : Fact (Nat.Prime KB) := ⟨prime_KoalaBearPrime⟩
instance : NeZero KB := by constructor; decide

-- dt: Wouldn't need this if `ZMod` was the fundamental object for us.
instance : Field (Fin KB) := ZMod.instField KB
instance : NoZeroDivisors (Fin 2130706433) := Fin.noZeroDivisors_of_prime _ (hp := Fact_BBPrime)

lemma val_mod4_eq_zero (x : Fin KB) : x.val % 4 = 0 ↔ x % 4 = 0 :=
  Fin.val_mod_eq_zero_iff x 4

end KoalaBear

@[aesop safe forward]
lemma mul_diff_one_neq {α : Type*} [Field α] {a b c : α} :
    a * (b - c) = 1 → b ≠ c := by aesop

/-- `Fin (n + 1)` is a field whenever `n + 1` is prime — via `ZMod.instField`, noting
that `ZMod (n + 1)` is definitionally `Fin (n + 1)`. Avoids having to restate a
`Field (Fin p)` instance for each specific prime `p` (e.g. `Field (Fin KB)` above
reduces to an application of this instance). -/
instance Fin.instField {n : ℕ} [Fact (Nat.Prime (n + 1))] : Field (Fin (n + 1)) :=
  ZMod.instField (n + 1)

@[simp] lemma shiftl_1BB_eq_one : (1065353217 : Fin KB) <<< 1 = 1 := rfl
@[simp] lemma shiftl_2BB_eq_one : (1598029825 : Fin KB) <<< 2 = 1 := rfl
@[simp] lemma shiftl_3BB_eq_one : (1864368129 : Fin KB) <<< 3 = 1 := rfl
@[simp] lemma shiftl_8BB_eq_one : (2122383361 : Fin KB) <<< 8 = 1 := rfl
@[simp] lemma shiftl_16BB_eq_one : (2130673921 : Fin KB) <<< 16 = 1 := rfl

lemma inv_1BB_eq : (1065353217 : Fin KB)⁻¹ = 2 := inv_eq_of_mul_eq_one_right (by rfl)
lemma inv_2BB_eq : (1598029825 : Fin KB)⁻¹ = 4 := inv_eq_of_mul_eq_one_right (by rfl)
lemma inv_3BB_eq : (1864368129 : Fin KB)⁻¹ = 8 := inv_eq_of_mul_eq_one_right (by rfl)
lemma inv_8BB_eq : (2122383361 : Fin KB)⁻¹ = 256 := inv_eq_of_mul_eq_one_right (by rfl)
lemma inv_16BB_eq : (2130673921 : Fin KB)⁻¹ = 65536 := inv_eq_of_mul_eq_one_right (by rfl)

lemma inv_1BB_eq' : (1065353217 : Fin KB) = 2⁻¹ := eq_inv_of_mul_eq_one_left (by rfl)
lemma inv_2BB_eq' : (1598029825 : Fin KB) = 4⁻¹ := eq_inv_of_mul_eq_one_left (by rfl)
lemma inv_3BB_eq' : (1864368129 : Fin KB) = 8⁻¹ := eq_inv_of_mul_eq_one_left (by rfl)
lemma inv_8BB_eq' : (2122383361 : Fin KB) = 256⁻¹ := eq_inv_of_mul_eq_one_left (by rfl)
lemma inv_16BB_eq' : (2130673921 : Fin KB) = 65536⁻¹ := eq_inv_of_mul_eq_one_left (by rfl)

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
  rw [inv_1BB_eq', inv_mul_eq_one₀ (by decide), eq_comm]
@[simp] lemma inv_mul_2BB_eq_iff : (1598029825 : Fin KB) * x = 1 ↔ x = 4 := by
  rw [inv_2BB_eq', inv_mul_eq_one₀ (by decide), eq_comm]
@[simp] lemma inv_mul_3BB_eq_iff : (1864368129 : Fin KB) * x = 1 ↔ x = 8 := by
  rw [inv_3BB_eq', inv_mul_eq_one₀ (by decide), eq_comm]
@[simp] lemma inv_mul_8BB_eq_iff : (2122383361 : Fin KB) * x = 1 ↔ x = 256 := by
  rw [inv_8BB_eq', inv_mul_eq_one₀ (by decide), eq_comm]
@[simp] lemma inv_mul_16BB_eq_iff : (2130673921 : Fin KB) * x = 1 ↔ x = 65536 := by
  rw [inv_16BB_eq', inv_mul_eq_one₀ (by decide), eq_comm]

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

lemma mul_256_inv_KB (x : Fin KB)
    (hx : x.val % 256 = 0) : x * (256 : Fin KB)⁻¹ = x >>> 8 := by
  rw [mul_inv_eq_iff_eq_mul₀ (by omega), ← Fin.val_inj]
  simp [Fin.val_mul, Nat.shiftRight_eq_div_pow, Nat.div_mul_self_eq_mod_sub_self]
  omega

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
