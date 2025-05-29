import Mathlib

macro "WORD_SIZE" : term => `(2)
-- macro "BASE" : term => `(65536)


@[reducible]
def Word (T : Type) := Vector T WORD_SIZE

abbrev p := 2013265921

abbrev base : Fin p := 65536
abbrev baseInv : Fin p := 2013235201

@[simp] lemma val_base : base.val = 65536 := rfl
@[simp] lemma val_baseInv : baseInv.val = 2013235201 := rfl

@[simp] lemma baseInv_test : baseInv * base = 1 := rfl

@[simp] lemma base_mul_baseInv : base * baseInv = 1 := rfl

@[simp] lemma baseInv_ne_zero : baseInv ≠ 0 := by simp [baseInv]

instance : NeZero (baseInv) := sorry

variable [Fact (Nat.Prime p)] [NeZero p] [(NoZeroDivisors (Fin p))]


@[simp] lemma mul_baseInv_eq_zero_iff (x : Fin p) :
    x * baseInv = 1 ↔ x = base := by

  sorry

-- example : Field (Fin p) := by infer_instance

def Word.is_u32 (w : Word (Fin p)) : Prop :=
  ∀ x ∈ w, x.val < base

def Word.toNat (w : Word (Fin p)) : ℕ :=
  w[0].val + base * w[1].val

structure AddOperation (T : Type) where
  value : Word T

@[elab_as_elim]
def Word.inductionOn {α : Type} {C : Word α → Prop}
    (mk : ∀ x1 x2 : α, C #v[x1, x2]) (w : Word α) : C w := sorry

@[elab_as_elim]
def AddOperation.inductionOn {α : Type} {C : AddOperation α → Prop}
    (mk : ∀ x1 x2 : α, C ⟨#v[x1, x2]⟩)
    (op : AddOperation α) : C op := sorry

def AddOperation.spec
    (cols : AddOperation (Fin p))
    (a : Word (Fin p))
    (b : Word (Fin p)) : Prop :=
  let a32 := a.toNat
  let b32 := b.toNat
  let c32 := cols.value.toNat
  a.is_u32 → b.is_u32 →
    (a32 + b32) % 2^32 = c32

def AddOperation.spec'
    (cols : AddOperation (Fin p))
    (a : Word (Fin p)) (b : Word (Fin p)) : Prop :=
  let a32 := a.toNat
  let b32 := b.toNat
  let c32 := cols.value.toNat
  a.is_u32 → b.is_u32 →
    a32 + b32 = if a32 + b32 < 2^32 then c32 else c32 + 2^32

lemma helper (a b : Word (Fin p)) :
    a.toNat + b.toNat = (a[0] + b[0]) + base * (a[1] + b[1]) := by
  rw [Word.toNat, Word.toNat]
  simp
  omega

def AddOperation.constraints
    (cols : AddOperation (Fin p))
    (a : Word (Fin p))
    (b : Word (Fin p)) : Prop :=
  let carry0 := 0
  let carry1 := (a[0] + b[0] - cols.value[0] + carry0) * baseInv
  let carry2 := (a[1] + b[1] - cols.value[1] + carry1) * baseInv
  -- actual constraints
  carry1 * (carry1 - 1) = 0 ∧
  carry2 * (carry2 - 1) = 0 ∧
  cols.value.is_u32 -- slice range checks

example {F : Type} [Field F] (x y : F) (h : x * y = 1) :
  x = y⁻¹ := by
  exact eq_inv_of_mul_eq_one_left h

theorem AddOperation.correct [NeZero p] (cols : AddOperation (Fin p))
    (a : Word (Fin p)) (b : Word (Fin p)) :
    cols.constraints a b → cols.spec a b := by
  induction a using Word.inductionOn with | mk a1 a2 =>
  induction b using Word.inductionOn with | mk b1 b2 =>
  induction cols using AddOperation.inductionOn with | mk v1 v2 =>
  unfold constraints spec
  simp_rw [helper]

  simp [Word.is_u32, Word.toNat, mul_eq_zero]
  intros h1 h2 h3 h4 h5 h6 h7 h8

  cases a1 with | mk a1 ha1 =>
  cases a2 with | mk a2 ha2 =>
  cases b1 with | mk b1 hb1 =>
  cases b2 with | mk b2 hb2 =>
  cases v1 with | mk v1 hv1 =>
  cases v2 with | mk v2 hv2 =>
  simp only

  have hinv : (2013235201 : Fin p).val = 2013235201 := rfl
  have hbase : (65536 : Fin p).val = 65536 := rfl
  have hpow : (2 ^ 16 : Fin p).val = 2 ^ 16 := rfl

  simp only [Fin.val, hpow] at h3 h4 h5 h6 h7 h8
  simp [two_ne_zero, sub_eq_zero] at h1 h2


  cases h1 with
  | inl h1 => cases h2 with
    | inl h2 => {
      simp [p, Fin.val, base] at *
      rw [h1, sub_self, zero_mul, add_zero, sub_eq_zero] at h2
      rw [Fin.add_def, Fin.ext_iff] at h1 h2
      simp at h1 h2

      omega
    }
    | inr h2 => {
      -- simp [p] at *
      rw [h1, sub_self, zero_mul, add_zero] at h2

      rw [eq_comm] at h1
      rw [sub_eq_iff_eq_add, eq_comm, add_comm base] at h2
      rw [← eq_sub_iff_add_eq] at h2

      rw [Fin.ext_iff] at h1 h2


      simp[Fin.add_def, Fin.sub_def] at h1 h2

      rw [← Nat.sub_add_comm (by omega)] at h2


      rw [h1, h2]




      sorry
    }
  | inr h1 => cases h2 with
    | inl h2 => {
      simp [p] at *
      rw [h1] at h2
      simp at h2
      rw [add_eq_zero_iff_neg_eq, neg_sub] at h2
      rw [sub_eq_iff_eq_add] at h2

      rw [sub_eq_iff_eq_add, eq_comm] at h1

      rw [add_comm base] at h1

      rw [← eq_sub_iff_add_eq] at h1

      rw [Fin.ext_iff] at h1 h2


      simp[Fin.add_def, Fin.sub_def] at h1 h2

      rw [h1, h2]

      omega
    }
    | inr h2 => {
      simp [p] at *
      rw [h1] at h2
      simp at h2

      rw [sub_eq_iff_eq_add] at h1
      rw [← eq_sub_iff_add_eq, sub_eq_iff_eq_add] at h2

      rw [Fin.ext_iff] at h1 h2

      simp [Fin.add_def, Fin.sub_def] at h1 h2
      have hab1 : a1 + b1 < p := sorry
      have hab2 : a2 + b2 < p := sorry

      rw [Nat.mod_eq_of_lt hab1] at h1
      rw [Nat.mod_eq_of_lt hab2] at h2

      rw [h1, h2]



      sorry
    }


theorem AddOperation.correct' [NeZero p] (cols : AddOperation (Fin p))
    (a : Word (Fin p)) (b : Word (Fin p)) :
    cols.constraints a b → cols.spec' a b := by
  induction a using Word.inductionOn with | mk a1 a2 =>
  induction b using Word.inductionOn with | mk b1 b2 =>
  induction cols using AddOperation.inductionOn with | mk v1 v2 =>
  unfold constraints spec'
  simp_rw [helper]

  simp [Word.is_u32, mul_eq_zero]
  intros h1 h2 h3 h4 h5 h6 h7 h8

  cases a1 with | mk a1 ha1 =>
  cases a2 with | mk a2 ha2 =>
  cases b1 with | mk b1 hb1 =>
  cases b2 with | mk b2 hb2 =>
  cases v1 with | mk v1 hv1 =>
  cases v2 with | mk v2 hv2 =>
  simp only

  have hinv : (2013235201 : Fin p).val = 2013235201 := rfl
  have hbase : (65536 : Fin p).val = 65536 := rfl
  have hpow : (2 ^ 16 : Fin p).val = 2 ^ 16 := rfl

  simp only [Fin.val, hpow] at h3 h4 h5 h6 h7 h8
  simp [two_ne_zero, sub_eq_zero] at h1 h2

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
        rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h1
        simp only [Fin.add_def, Fin.sub_def, Fin.ext_iff] at h1 h2
        rw [← h1, ← h2]
        simp

        sorry
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
        simp

        sorry
      }
