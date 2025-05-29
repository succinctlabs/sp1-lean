import Mathlib

/-!
This file contains an optimized/golfed proof of add operation correctness.
Need more work to check how this scales to e.g. add4 or add5
-/

-- random math fact
instance {p : ℕ} [hp : Fact (Nat.Prime (p + 1))] : NoZeroDivisors (Fin (p + 1)) := by
  have : IsDomain (ZMod (p + 1)) := ZMod.instIsDomain (hp := ⟨hp.1⟩)
  simp [ZMod] at this
  infer_instance

abbrev WORD_SIZE := 2
abbrev p := 2013265921

@[reducible] def Word (T : Type) := Vector T WORD_SIZE
@[reducible] def AddOperation (T : Type) := Word T

@[elab_as_elim] -- induction rule for words
def Word.inductionOn {α : Type} {C : Word α → Prop}
    (mk : ∀ x1 x2 : α, C #v[x1, x2]) (w : Word α) : C w := sorry

section base

abbrev base : Fin p := 65536
abbrev baseInv : Fin p := 2013235201

@[simp] lemma val_base : base.val = 65536 := rfl
@[simp] lemma val_baseInv : baseInv.val = 2013235201 := rfl

@[simp] lemma baseInv_mul_base : baseInv * base = 1 := rfl
@[simp] lemma base_mul_baseInv : base * baseInv = 1 := rfl

@[simp] lemma base_ne_zero : base ≠ 0 := by simp [base]
@[simp] lemma baseInv_ne_zero : baseInv ≠ 0 := by simp [baseInv]

@[simp] lemma mul_baseInv_eq_zero_iff (x : Fin p) :
    x * baseInv = 1 ↔ x = base := by
  refine ⟨fun h => by simpa [mul_assoc] using congr_arg (· * base) h,
    fun h => by simp only [h, base_mul_baseInv, Fin.isValue]⟩

end base

-- A word represents a u32 value if both entries are u16 values
def Word.isUInt32 (w : Word (Fin p)) : Prop :=
  w[0].val < base ∧ w[1].val < base

-- Convert a word to a natural number in the natural way
@[reducible] def Word.toNat (w : Word (Fin p)) : ℕ :=
  w[0].val + base * w[1].val

lemma toNat_add_toNat (a b : Word (Fin p)) :
    a.toNat + b.toNat = (a[0] + b[0]) + base * (a[1] + b[1]) := by
  simp [Word.toNat]; omega

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

lemma test_constraints_equiv (cols : AddOperation (Fin p))
    (a : Word (Fin p)) (b : Word (Fin p)) :
  cols.constraints a b ↔ (((((a[0] + b[0]) - cols[0]) + (0 : Fin p)) *
    (2013235201 : Fin p)) * (((((a[0] + b[0]) - cols[0]) + 0) * 2013235201) - 1)) = 0 ∧
    (((((a[1] + b[1]) - cols[1]) + ((((a[0] + b[0]) - cols[0]) + (0 : Fin p)) *
    (2013235201 : Fin p))) * (2013235201 : Fin p)) * (((((a[1] + b[1]) - cols[1]) +
    ((((a[0] + b[0]) - cols[0]) + 0) * 2013235201)) * 2013235201) - 1)) = 0 ∧
    cols.isUInt32 := by
  simp [AddOperation.constraints]

/-- The constraints on `AddOperation` imply the expected spec. -/
theorem AddOperation.correct [Fact (Nat.Prime p)]
    (cols : AddOperation (Fin p))
    (a : Word (Fin p)) (b : Word (Fin p)) :
    cols.constraints a b → cols.spec a b := by
  simp [constraints, spec, toNat_add_toNat, Word.isUInt32, sub_eq_zero]
  intros h1 h2; intros
  split_ifs with h_overflow
    <;> simp [h_overflow, Word.toNat]
    <;> cases h1 with | inl h1 => ?_ | inr h1 => ?_
    <;> · rw [h1] at h2
          simp [Fin.add_def, Fin.sub_def, Fin.ext_iff, sub_eq_zero, p] at *
          omega
