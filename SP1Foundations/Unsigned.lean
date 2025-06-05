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

structure U16 where
  val : BabyBear
  in_range : val < base

-- Extensionality for U1
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

@[simp]
lemma U16_eq_zero_iff' (x : U16) : x = U16.zero ↔ x.val = 0 := by
  refine ⟨congr_arg U16.val, fun h => U16.ext h⟩

@[simp]
lemma U16_eq_one_iff' (x : U16) : x = U16.one ↔ x.val = 1 := by
  refine ⟨congr_arg U16.val, fun h => U16.ext h⟩

-- For converting BabyBear to U16, we can define a function that returns Option
def BabyBear.toU16? (b : BabyBear) : Option U16 :=
  if h : b < base then some ⟨b, h⟩ else none

instance (b : BabyBear) (h : b < base) : CoeDep BabyBear b U16 where
  coe := ⟨b, h⟩

instance : CoeOut U16 ℕ where
  coe u := u.val.val  -- U16 -> BabyBear -> ℕ

end U16

section U8

structure U8 where
  val : BabyBear
  in_range : val < 256 -- TODO(gzgz): 256 should be some constant like U8.base

-- Extensionality for U1
@[ext] theorem U8.ext {a b : U8} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp at h; simp [h]

instance : Coe U8 BabyBear where
  coe u := u.val

-- Safe constructors for 0 and 1
def U8.zero : U8 := ⟨0, by simp [base]⟩
def U8.one : U8 := ⟨1, by simp [base]⟩

-- Allow writing 0 : U8 and 1 : U8 directly
instance : Zero U8 := ⟨U8.zero⟩
instance : One U8 := ⟨U8.one⟩

@[simp]
lemma U8_eq_zero_iff (x : U8) : x = 0 ↔ x.val = 0 := by
  refine ⟨congr_arg U8.val, fun h => U8.ext h⟩

@[simp]
lemma U8_eq_one_iff (x : U8) : x = 1 ↔ x.val = 1 := by
  refine ⟨congr_arg U8.val, fun h => U8.ext h⟩

@[simp]
lemma U8_eq_zero_iff' (x : U8) : x = U8.zero ↔ x.val = 0 := by
  refine ⟨congr_arg U8.val, fun h => U8.ext h⟩

@[simp]
lemma U8_eq_one_iff' (x : U8) : x = U8.one ↔ x.val = 1 := by
  refine ⟨congr_arg U8.val, fun h => U8.ext h⟩

-- For converting BabyBear to U8, we can define a function that returns Option
def BabyBear.toU8? (b : BabyBear) : Option U8 :=
  if h : b < 256 then some ⟨b, h⟩ else none

instance (b : BabyBear) (h : b < 256) : CoeDep BabyBear b U8 where
  coe := ⟨b, h⟩

instance : CoeOut U8 ℕ where
  coe u := u.val.val  -- U8 -> BabyBear -> ℕ

end U8

section U1

-- U1 type for bits
structure U1 where
  val : BabyBear
  in_range : val = 0 ∨ val = 1

-- Extensionality for U1
@[ext] theorem U1.ext {a b : U1} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp at h; simp [h]

instance : Coe U1 BabyBear where
  coe u := u.val

instance : CoeOut U1 ℕ where
  coe u := u.val.val

-- Conversion from BabyBear to U1
def BabyBear.toU1? (b : BabyBear) : Option U1 :=
  if h : b = 0 ∨ b = 1 then some ⟨b, h⟩ else none

-- Safe constructors for 0 and 1
def U1.zero : U1 := ⟨0, Or.inl rfl⟩
def U1.one : U1 := ⟨1, Or.inr rfl⟩

-- Allow writing 0 : U1 and 1 : U1 directly
instance : Zero U1 := ⟨U1.zero⟩
instance : One U1 := ⟨U1.one⟩

@[simp]
lemma U1.eq_zero_iff (x : U1) : x = 0 ↔ x.val = 0 := by
  refine ⟨congr_arg U1.val, fun h => U1.ext h⟩

@[simp]
lemma U1.eq_one_iff (x : U1) : x = 1 ↔ x.val = 1 := by
  refine ⟨congr_arg U1.val, fun h => U1.ext h⟩

@[simp]
lemma U1.eq_zero_iff' (x : U1) : x = U1.zero ↔ x.val = 0 := by
  refine ⟨congr_arg U1.val, fun h => U1.ext h⟩

@[simp]
lemma U1.eq_one_iff' (x : U1) : x = U1.one ↔ x.val = 1 := by
  refine ⟨congr_arg U1.val, fun h => U1.ext h⟩

end U1
