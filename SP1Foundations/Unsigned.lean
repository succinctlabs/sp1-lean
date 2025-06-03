import SP1Foundations.Field

section base

abbrev base : BabyBear := 65536 -- 2^16
abbrev baseInv : BabyBear := 2013235201

@[simp] lemma val_base : (base : ℕ) = 65536 := rfl
@[simp] lemma val_baseInv : (baseInv : ℕ) = 2013235201 := rfl

@[simp] lemma baseInv_mul_base : (baseInv : BabyBear) * (base : BabyBear) = 1 := rfl
@[simp] lemma base_mul_baseInv : (base : BabyBear) * (baseInv : BabyBear) = 1 := rfl

@[simp] lemma base_ne_zero : (base : BabyBear) ≠ 0 := by simp [base]
@[simp] lemma baseInv_ne_zero : (baseInv : BabyBear) ≠ 0 := by simp [baseInv]

@[simp] lemma mul_baseInv_eq_zero_iff (x : BabyBear) : x * baseInv = 1 ↔ x = base := by
  refine ⟨fun h => by simpa [mul_assoc] using congr_arg (· * base) h,
    fun h => by simp only [h, base_mul_baseInv, Fin.isValue]⟩

@[simp] lemma baseInv_mul_eq_zero_iff (x : BabyBear) : baseInv * x = 1 ↔ x = base := by
  rw [mul_comm, mul_baseInv_eq_zero_iff]

end base

section U16

structure U16 where
  val : BabyBear
  in_range : val < base

-- Extensionality for U2
@[ext] theorem U16.ext {a b : U16} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp at h; simp [h]

instance : Coe U16 BabyBear where
  coe u := u.val

-- Safe constructors for 0 and 1
def U16.zero : U16 := ⟨0, by simp [base]⟩
def U16.one : U16 := ⟨1, by simp [base]⟩

-- Allow writing 0 : U16 and 1 : U16 directly
instance : Zero U16 := ⟨U16.zero⟩
instance : One U16 := ⟨U16.one⟩

@[simp]
lemma U16_eq_zero_iff (x : U16) : x = 0 ↔ x.val = 0 := by
  refine ⟨congr_arg U16.val, fun h => U16.ext h⟩

@[simp]
lemma U16_eq_one_iff (x : U16) : x = 1 ↔ x.val = 1 := by
  refine ⟨congr_arg U16.val, fun h => U16.ext h⟩

-- For converting BabyBear to U16, we can define a function that returns Option
def BabyBear.toU16? (b : BabyBear) : Option U16 :=
  if h : b < base then some ⟨b, h⟩ else none

instance (b : BabyBear) (h : b < base) : CoeDep BabyBear b U16 where
  coe := ⟨b, h⟩

instance : CoeOut U16 ℕ where
  coe u := u.val.val  -- U16 -> BabyBear -> ℕ

end U16

section U2

-- U2 type for bits
structure U2 where
  val : BabyBear
  in_range : val = 0 ∨ val = 1

-- Extensionality for U2
@[ext] theorem U2.ext {a b : U2} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp at h; simp [h]

instance : Coe U2 BabyBear where
  coe u := u.val

instance : CoeOut U2 ℕ where
  coe u := u.val.val

-- Conversion from BabyBear to U2
def BabyBear.toU2? (b : BabyBear) : Option U2 :=
  if h : b = 0 ∨ b = 1 then some ⟨b, h⟩ else none

-- Safe constructors for 0 and 1
def U2.zero : U2 := ⟨0, Or.inl rfl⟩
def U2.one : U2 := ⟨1, Or.inr rfl⟩

-- Allow writing 0 : U2 and 1 : U2 directly
instance : Zero U2 := ⟨U2.zero⟩
instance : One U2 := ⟨U2.one⟩

@[simp]
lemma U2.eq_zero_iff (x : U2) : x = 0 ↔ x.val = 0 := by
  refine ⟨congr_arg U2.val, fun h => U2.ext h⟩

@[simp]
lemma U2.eq_one_iff (x : U2) : x = 1 ↔ x.val = 1 := by
  refine ⟨congr_arg U2.val, fun h => U2.ext h⟩

end U2
