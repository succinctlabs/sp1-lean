import SP1Foundations

structure SubOperation where
  value : Word U16

namespace SubOperation

/-- `SubOperation` should result in wrapping addition of the outputs.
Note that we ignore `is_real` for now. -/
def spec (cols : SubOperation) (a b : Word U16) (is_real : U1) : Prop :=
  is_real = 1 → a.toFin32_U16 - b.toFin32_U16 = cols.value.toFin32_U16

/-- Constraints on `SubOperation` as extracted from the source code:
Asserting expr 3: `(is_real * (is_real - 1))`
Asserting expr 17: `(is_real * (((((((a[0] + 65536) - 1) - b[0]) - cols.value[0]) + 1) * 2013235201) * (((((((a[0] + 65536) - 1) - b[0]) - cols.value[0]) + 1) * 2013235201) - 1)))`
Asserting expr 29: `(is_real * (((((((a[1] + 65536) - 1) - b[1]) - cols.value[1]) + ((((((a[0] + 65536) - 1) - b[0]) - cols.value[0]) + 1) * 2013235201)) * 2013235201) * (((((((a[1] + 65536) - 1) - b[1]) - cols.value[1]) + ((((((a[0] + 65536) - 1) - b[0]) - cols.value[0]) + 1) * 2013235201)) * 2013235201) - 1)))` -/
def extractedConstraints (cols : SubOperation)
    (a b : Word U16) (is_real : U1) : Finset SP1Constraint :=
  {
  .assertZero (is_real.val * (((((((a[0] + (65536 : BabyBear)) - (1 : BabyBear)) - b[0]) - cols.value[0]) + 1) * (2013235201 : BabyBear)) * (((((((a[0] + (65536 : BabyBear)) - (1 : BabyBear)) - b[0]) - cols.value[0]) + 1) * (2013235201 : BabyBear)) - (1 : BabyBear)))),
  .assertZero (is_real.val * (((((((a[1] + (65536 : BabyBear)) - (1 : BabyBear)) - b[1]) - cols.value[1]) + ((((((a[0] + (65536 : BabyBear)) - (1 : BabyBear)) - b[0]) - cols.value[0]) + 1) * (2013235201 : BabyBear))) * (2013235201 : BabyBear)) * (((((((a[1] + (65536 : BabyBear)) - (1 : BabyBear)) - b[1]) - cols.value[1]) + ((((((a[0] + (65536 : BabyBear)) - (1 : BabyBear)) - b[0]) - cols.value[0]) + 1) * (2013235201 : BabyBear))) * (2013235201 : BabyBear)) - (1 : BabyBear))))
  }

/-- Cleaned up representation of the `SubOperation` constraints. -/
def idealizedConstraints (cols : SubOperation)
    (a b : Word U16) (is_real : U1) : Prop :=
  let carry0 : BabyBear := 1
  let carry1 : BabyBear := (a[0] + base - (1 : BabyBear) - b[0] - cols.value[0] + carry0) * baseInv
  let carry2 : BabyBear := (a[1] + base - (1 : BabyBear) - b[1] - cols.value[1] + carry1) * baseInv
  (is_real.val * carry1 * (carry1 - 1)) = 0 ∧ -- isBool check
  (is_real.val * carry2 * (carry2 - 1)) = 0 -- isBool check

/-- The idealized constraints are logically equivalent to the extracted ones when `is_real := 1` -/
lemma extractedConstraints_iff_idealizedConstraints
    (cols : SubOperation) (a b : Word U16) (is_real : U1) :
    constraintSet_toProp (cols.extractedConstraints a b is_real) ↔ cols.idealizedConstraints a b is_real := by

  simp only [extractedConstraints, WORD_SIZE, Fin.isValue, Nat.cast_one,
    constraintSet_toProp_insert, SP1Constraint.toProp_assertZero, mul_eq_zero, baseInv_ne_zero,
    or_false, constraintSet_toProp_singleton, idealizedConstraints, base, baseInv,
    - Fin.val_eq_zero_iff]
  rw [Fin.add_def]

  simp only [Fin.cast_val_eq_self, Fin.isValue, Fin.val_one, Fin.mk_eq_zero, Fin.val_eq_zero_iff,
    mul_eq_zero, baseInv_ne_zero, or_false]
  simp [sub_eq_zero, Fin.sub_def, Fin.add_def]

  sorry
  -- aesop

/-- The extracted constraints on `SubOperation` imply the spec. -/
theorem correct [Fact (Nat.Prime p)] (cols : SubOperation)
    (a b : Word U16) (is_real : U1) :
    cols.idealizedConstraints a b is_real → cols.spec a b is_real := by
  -- Unfold the definitions of constraints and spec
  simp [idealizedConstraints, spec, sub_eq_zero, mul_eq_zero, Fin.val_mul]
  -- Introduce all of the hypothesis from the constraints
  intros h1 h2
  -- Eliminate `is_real`
  intro h_is_real
  simp [h_is_real, sub_eq_zero] at *
  -- have is_real_val_eq_one : is_real.val = 1 := by aesop

  -- rw [is_real_val_eq_one] at h1 h2
  -- simp at h1 h2

  simp [Word.toFin32_U16]

  -- Extract the range constraint in U16
  let _ : a[0].val < 65536 := a[0].in_range
  let _ : b[0].val < 65536 := b[0].in_range
  let _ : a[1].val < 65536 := a[1].in_range
  let _ : b[1].val < 65536 := b[1].in_range
  let _ : cols.value[0].val < 65536 := cols.value[0].in_range
  let _ : cols.value[1].val < 65536 := cols.value[1].in_range

  -- Split on whether the lower limb addition causes a carry
  cases h1 with | inl h1 => ?_ | inr h1 => ?_

  all_goals -- In both cases can now reduce down to the `omega` linear constraint solver
  · rw [h1] at h2
    simp only [Fin.add_def, Fin.sub_def, Fin.ext_iff, p, Word.toNat, Word.isUInt32] at *
    simp [BabyBearPrime] at *
    omega

end SubOperation
