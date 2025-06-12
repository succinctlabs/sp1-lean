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

/-- General definition that can be used to define `U1`, `U8`, and `U16`.
Allows writing unified lemmas for all three definitions. -/
structure BoundedBabyBear (bound : ℕ) extends BabyBear where
  in_range : val < bound

namespace BoundedBabyBear

def ofNat (bound_dec x : ℕ) : BoundedBabyBear bound_dec.succ where
  val := (x % bound_dec.succ) % BabyBearPrime
  isLt := Nat.mod_lt _ Nat.succ_pos'
  in_range := Nat.mod_lt_of_lt (Nat.mod_lt _ Nat.succ_pos')

/-- If the bound is at least `1` then `boundedBabyBear` has a natural `0`. -/
def boundedBabyBear.zero (bound_dec : ℕ) : BoundedBabyBear bound_dec.succ where
  in_range := by simp
  __ := (0 : BabyBear)

/-- If the bound is at least `2` then `boundedBabyBear` has a natural `1`. -/
def boundedBabyBear.one (bound_dec_dec : ℕ) : BoundedBabyBear (bound_dec_dec.succ.succ) where
  in_range := by simp
  __ := (1 : BabyBear)

instance (bound_dec : ℕ) : Zero (BoundedBabyBear bound_dec.succ) := ⟨boundedBabyBear.zero _⟩
instance (bound_dec_dec : ℕ) : One (BoundedBabyBear bound_dec_dec.succ.succ) := ⟨boundedBabyBear.one _⟩

/-- Should only make an actual instance for special cases. -/
def coe_of_le {bound bound' : ℕ} (h : bound ≤ bound') :
    Coe (BoundedBabyBear bound) (BoundedBabyBear bound') where
  coe x := { in_range := lt_of_lt_of_le x.in_range h, __ := x }

variable {bound : ℕ}

def toBabyBear (x : BoundedBabyBear bound) : BabyBear where __ := x

@[simp] lemma toBabyBear_zero : (0 : BoundedBabyBear bound.succ).toBabyBear = 0 := rfl
@[simp] lemma toBabyBear_one : (1 : BoundedBabyBear bound.succ.succ).toBabyBear = 1 := rfl

@[simp] lemma toFin_zero : (0 : BoundedBabyBear bound.succ).toFin = 0 := rfl
@[simp] lemma toFin_one : (1 : BoundedBabyBear bound.succ.succ).toFin = 1 := rfl

lemma toFin_inj (x y : BoundedBabyBear bound) : x.toFin = y.toFin ↔ x = y := sorry

lemma toFin_eq_iff (x : BoundedBabyBear bound) (y : Fin BabyBearPrime) : x.toFin = y ↔ x.val = y.val := by
  erw [Fin.ext_iff]

@[simp] lemma eq_zero_iff (x : BoundedBabyBear bound.succ) : x = 0 ↔ x.val = 0 := by
  rw [Fin.val_eq_zero_iff, ← toFin_zero, toFin_inj]

@[simp] lemma eq_one_iff (x : BoundedBabyBear bound.succ.succ) : x = 1 ↔ x.val = 1 := by
  sorry

@[simp] lemma val_toBabyBear (x : BoundedBabyBear bound) : (x.toBabyBear : ℕ) = x.val := rfl

end BoundedBabyBear

abbrev U16 := BoundedBabyBear 65536
abbrev U8 := BoundedBabyBear 256
abbrev U1 := BoundedBabyBear 2

instance : Coe U16 BabyBear where coe := BoundedBabyBear.toBabyBear
instance : Coe U8 BabyBear where coe := BoundedBabyBear.toBabyBear
instance : Coe U1 BabyBear where coe := BoundedBabyBear.toBabyBear

instance : Coe U1 U8 := BoundedBabyBear.coe_of_le <| by omega
instance : Coe U8 U16 := BoundedBabyBear.coe_of_le <| by omega

def U1.in_range' (x : U1) : x.val = 0 ∨ x.val = 1 := by
  have := x.in_range; omega
