import Mathlib

-- random math fact
instance {p : ℕ} [Fact (Nat.Prime p)] : NoZeroDivisors (Fin p) := by
  sorry

macro "WORD_SIZE" : term => `(2)
abbrev p := 2013265921

@[reducible] def Word (T : Type) := Vector T WORD_SIZE
@[reducible] def AddOperation (T : Type) := Word T

section eliminators

@[elab_as_elim]
def Word.inductionOn {α : Type} {C : Word α → Prop}
    (mk : ∀ x1 x2 : α, C #v[x1, x2]) (w : Word α) : C w := by
  refine match w with
  | (Vector.mk (Array.mk as) h) => by {
    simp at h
    sorry
  }

@[elab_as_elim]
def AddOperation.inductionOn {α : Type} {C : AddOperation α → Prop}
    (mk : ∀ x1 x2 : α, C #v[x1, x2])
    (op : AddOperation α) : C op := sorry

end eliminators

section base

abbrev base : Fin p := 2 ^ 16
abbrev baseInv : Fin p := 2013235201

@[simp] lemma val_base : base.val = 65536 := rfl
@[simp] lemma val_baseInv : baseInv.val = 2013235201 := rfl

@[simp] lemma baseInv_mul_base : baseInv * base = 1 := rfl
@[simp] lemma base_mul_baseInv : base * baseInv = 1 := rfl

@[simp] lemma base_ne_zero : base ≠ 0 := by simp [base]; trivial
@[simp] lemma baseInv_ne_zero : baseInv ≠ 0 := by simp [baseInv]

@[simp] lemma mul_baseInv_eq_zero_iff (x : Fin p) :
    x * baseInv = 1 ↔ x = base := by
  refine ⟨fun h => by simpa [mul_assoc] using congr_arg (· * base) h,
    fun h => by simp only [h, base_mul_baseInv, Fin.isValue]⟩

end base

section isUInt32

-- A word represents a u32 value if both entries are u16 values
def Word.isUInt32 (w : Word (Fin p)) : Prop :=
  ∀ x ∈ w, x.val < base

end isUInt32

section toNat

-- Convert a word to a natural number in the natural way
def Word.toNat (w : Word (Fin p)) : ℕ :=
  w[0].val + base * w[1].val

lemma toNat_add_toNat (a b : Word (Fin p)) :
    a.toNat + b.toNat = (a[0] + b[0]) + base * (a[1] + b[1]) := by
  simp [Word.toNat]; omega

end toNat

/-- `AddOperation` should either give the direct sum of the two input values,
or the value plus `2^32` on overflow-/
def AddOperation.spec (cols : AddOperation (Fin p))
    (a : Word (Fin p)) (b : Word (Fin p)) : Prop :=
  a.isUInt32 → b.isUInt32 →
    a.toNat + b.toNat = if a.toNat + b.toNat < 2^32
      then cols.toNat else cols.toNat + 2^32

/-- Basic representation of the extracted constraints. A bit pre-processed more than will be in practice.
Also note we ignore the `is_real` part of the constraints, but should be easy to add that later.  -/
def AddOperation.constraints
    (cols : AddOperation (Fin p))
    (a : Word (Fin p))
    (b : Word (Fin p)) : Prop :=
  let carry0 := 0
  let carry1 := (a[0] + b[0] - cols[0] + carry0) * baseInv
  let carry2 := (a[1] + b[1] - cols[1] + carry1) * baseInv
  carry1 * (carry1 - 1) = 0 ∧ -- isBool check
  carry2 * (carry2 - 1) = 0 ∧ -- isBool check
  cols.isUInt32 -- slice range checks

/-- The constraints on `AddOperation` imply the expected spec. -/
theorem AddOperation.correct [Fact (Nat.Prime p)]
    (cols : AddOperation (Fin p))
    (a : Word (Fin p)) (b : Word (Fin p)) :
    cols.constraints a b → cols.spec a b := by
  induction a using Word.inductionOn with | mk a1 a2 =>
  induction b using Word.inductionOn with | mk b1 b2 =>
  induction cols using AddOperation.inductionOn with | mk v1 v2 =>

  unfold constraints spec

  simp [toNat_add_toNat, Word.isUInt32, mul_eq_zero]
  intros h1 h2 h3 h4 h5 h6 h7 h8

  cases a1 with | mk a1 ha1 =>
  cases a2 with | mk a2 ha2 =>
  cases b1 with | mk b1 hb1 =>
  cases b2 with | mk b2 hb2 =>
  cases v1 with | mk v1 hv1 =>
  cases v2 with | mk v2 hv2 =>

  have hinv : (2013235201 : Fin p).val = 2013235201 := rfl
  have hbase : (65536 : Fin p).val = 65536 := rfl
  have hpow : (2 ^ 16 : Fin p).val = 2 ^ 16 := rfl

  simp only [Fin.val, hpow] at h3 h4 h5 h6 h7 h8
  simp only [Fin.isValue, sub_eq_zero, mul_baseInv_eq_zero_iff] at h1 h2

  by_cases h_overflow : a1 + b1 + 65536 * (a2 + b2) < 4294967296
  ·
    simp only [h_overflow, if_true, Word.toNat]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, val_base,
      List.getElem_cons_succ]

    cases h1 with
    | inl h1 => cases h2 with
      | inl h2 => {
        simp [p, Fin.val, base] at *
        rw [h1, sub_self, zero_mul, add_zero, sub_eq_zero] at h2
        rw [Fin.add_def, Fin.ext_iff] at h1 h2
        simp at h1 h2

        rw [← h1, ← h2]
        omega
      }
      | inr h2 => {
        simp [p, Fin.val, base] at *
        rw [h1, sub_self, zero_mul, add_zero] at h2
        rw [sub_eq_iff_eq_add] at h2
        rw [← sub_eq_iff_eq_add'] at h2
        rw [Fin.add_def, Fin.ext_iff] at h1 h2
        simp at h1
        simp [Fin.sub_def] at h2

        rw [← h1, ← h2]

        omega
      }
    | inr h1 => cases h2 with
      | inl h2 => {
        simp [p] at *
        rw [h1] at h2
        simp at h2
        rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h1

        rw [← eq_sub_iff_add_eq, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h2
        simp at h2

        simp only [Fin.add_def, Fin.sub_def, Fin.ext_iff] at h1 h2

        rw [val_base] at h1

        omega
      }
      | inr h2 => {

        rw [h1, base_mul_baseInv] at h2

        rw [← eq_sub_iff_add_eq, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h2
        rw [sub_eq_add_neg, neg_sub] at h2
        rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h1


        simp only [Fin.add_def, Fin.sub_def, Fin.ext_iff] at h1 h2

        rw [← h1, ← h2]
        simp
        simp_rw [mul_add, ← add_assoc]
        simp [p] at *
        omega
      }
  · simp only [h_overflow, if_true, Word.toNat]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, val_base,
      List.getElem_cons_succ]

    cases h1 with
    | inl h1 => cases h2 with
      | inl h2 => {
        simp [p, Fin.val, base] at *
        rw [h1, sub_self, zero_mul, add_zero, sub_eq_zero] at h2
        rw [Fin.add_def, Fin.ext_iff] at h1 h2
        simp at h1 h2

        rw [← h1, ← h2]
        omega
      }
      | inr h2 => {
        simp [p, Fin.val, base] at *
        rw [h1, sub_self, zero_mul, add_zero] at h2
        rw [sub_eq_iff_eq_add] at h2
        rw [← sub_eq_iff_eq_add'] at h2
        rw [Fin.add_def, Fin.ext_iff] at h1 h2
        simp at h1
        simp [Fin.sub_def] at h2

        rw [← h1, ← h2]

        omega
      }
    | inr h1 => cases h2 with
      | inl h2 => {
        simp [p] at *
        rw [h1] at h2
        simp at h2
        rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h1

        rw [← eq_sub_iff_add_eq, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h2
        simp at h2

        simp only [Fin.add_def, Fin.sub_def, Fin.ext_iff] at h1 h2

        rw [val_base] at h1

        omega
      }
      | inr h2 => {

        rw [h1, base_mul_baseInv] at h2
        rw [← eq_sub_iff_add_eq, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h2
        rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h1
        simp only [Fin.add_def, Fin.sub_def, Fin.ext_iff] at h1 h2
        rw [← h1, ← h2]
        simp [p] at *
        omega
      }
