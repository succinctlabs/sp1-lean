import SP1Foundations.Field

section base

-- TODO(gzgz): base should be some constant like U16.base
abbrev base : BabyBear := 65536 -- 2^16
abbrev baseInv : BabyBear := 2013235201

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

section U16

structure U16 extends BabyBear where
  in_u16_range : val < base.val

def U16.ofNat (x : Nat) : U16 := ⟨x % base, by simp; exact Nat.mod_lt (x := x % BabyBearPrime) ((by decide) : 65536 > 0)⟩

@[reducible]
def U16.zero : U16 := { (0 : BabyBear) with in_u16_range := by simp [base] }
@[reducible]
def U16.one : U16 := { (1 : BabyBear) with in_u16_range := by simp [base] }

instance : Coe U16 BabyBear where
  coe x := x.toFin

end U16

section U8

structure U8 extends U16 where
  in_u8_range : val < 256

@[reducible]
def U8.zero : U8 := { U16.zero with in_u8_range := by simp }
@[reducible]
def U8.one : U8 := { U16.one with in_u8_range := by simp }

instance : Coe U8 BabyBear where
  coe x := x.toFin

end U8

section U1

-- U1 type for bits
structure U1 extends U8 where
  in_u1_range : val = 0 ∨ val = 1

@[reducible]
def U1.one : U1 := { U8.one with in_u1_range := by simp }
@[reducible]
def U1.zero : U1 := { U8.zero with in_u1_range := by simp }

instance : Coe U1 BabyBear where
  coe x := x.toFin

end U1
