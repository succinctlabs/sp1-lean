import SP1Foundations

@[reducible] def SubOperation (T : Type) := Word T

namespace SubOperation

/-- `SubOperation` should result in wrapping addition of the outputs.
Note that we ignore `is_real` for now. -/
def spec (cols : SubOperation BabyBear) (a b : Word BabyBear) : Prop :=
  a.isUInt32 → b.isUInt32 →
    a.toNat = (cols.toNat + b.toNat) % 2^32

/-- Constraints on `SubOperation` as extracted from the source code:
Asserting expr 3: `(is_real * (is_real - 1))`
Asserting expr 17: `(is_real * (((((((a[0] + 65536) - 1) - b[0]) - cols.value[0]) + 1) * 2013235201) * (((((((a[0] + 65536) - 1) - b[0]) - cols.value[0]) + 1) * 2013235201) - 1)))`
Asserting expr 29: `(is_real * (((((((a[1] + 65536) - 1) - b[1]) - cols.value[1]) + ((((((a[0] + 65536) - 1) - b[0]) - cols.value[0]) + 1) * 2013235201)) * 2013235201) * (((((((a[1] + 65536) - 1) - b[1]) - cols.value[1]) + ((((((a[0] + 65536) - 1) - b[0]) - cols.value[0]) + 1) * 2013235201)) * 2013235201) - 1)))` -/
def extractedConstraints (cols : SubOperation BabyBear)
    (a b : Word BabyBear) (is_real : BabyBear) : List SP1Constraint :=
  [
  .assertZero (is_real * (is_real - 1)),
  .assertZero (is_real * (((((((a[0] + 65536) - 1) - b[0]) - cols[0]) + 1) * 2013235201) * (((((((a[0] + 65536) - 1) - b[0]) - cols[0]) + 1) * 2013235201) - 1))),
  .assertZero (is_real * (((((((a[1] + 65536) - 1) - b[1]) - cols[1]) + ((((((a[0] + 65536) - 1) - b[0]) - cols[0]) + 1) * 2013235201)) * 2013235201) * (((((((a[1] + 65536) - 1) - b[1]) - cols[1]) + ((((((a[0] + 65536) - 1) - b[0]) - cols[0]) + 1) * 2013235201)) * 2013235201) - 1))),
  ]

/-- Cleaned up representation of the `SubOperation` constraints. -/
def idealizedConstraints (cols : SubOperation BabyBear)
    (a b : Word BabyBear) : Prop :=
  let carry0 : BabyBear := 1
  let carry1 : BabyBear := (a[0] + base - 1 - b[0] - cols[0] + carry0) * baseInv
  let carry2 : BabyBear := (a[1] + base - 1 - b[1] - cols[1] + carry1) * baseInv
  carry1 * (carry1 - 1) = 0 ∧ -- isBool check
  carry2 * (carry2 - 1) = 0 -- isBool check

/-- The idealized constraints are logically equivalent to the extracted ones when `is_real := 1` -/
lemma extractedConstraints_iff_idealizedConstraints
    (cols : SubOperation BabyBear) (a b : Word BabyBear) :
    constraintList_toProp (cols.extractedConstraints a b 1) ↔ cols.idealizedConstraints a b := by
  simp [extractedConstraints, idealizedConstraints]

/-- The extracted constraints on `SubOperation` imply the spec. -/
theorem correct [Fact (Nat.Prime p)] (cols : SubOperation BabyBear)
    (a b : Word BabyBear) (hcols : cols.isUInt32) :
    cols.idealizedConstraints a b → cols.spec a b := by
  -- Unfold the definitions of constraints and spec
  simp [idealizedConstraints, spec, sub_eq_zero, mul_eq_zero]
  -- Introduce all of the hypothesis from the constraints
  intros h1 h2 ha_u32 hb_u32
  -- Split on whether the lower limb addition causes a carry
  cases h1 with | inl h1 => ?_ | inr h1 => ?_
  all_goals -- In both cases can now reduce down to the `omega` linear constraint solver
  · rw [h1] at h2
    simp only [Fin.add_def, Fin.sub_def, Fin.ext_iff, p, Word.toNat, Word.isUInt32] at *
    simp [BabyBearPrime] at *
    omega

end SubOperation
