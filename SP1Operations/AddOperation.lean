import SP1Foundations

@[reducible] def AddOperation2 (T : Type) := Word T

namespace AddOperation2

/-- `AddOperation` should result in wrapping addition of the outputs.
Note that we ignore `is_real` for now. -/
def spec (cols : AddOperation2 (Fin p)) (a b : Word (Fin p)) : Prop :=
  a.isUInt32 → b.isUInt32 →
    (a.toNat + b.toNat) % 2^32 = cols.toNat

/-- Constraints on `AddOperation` as extracted from the source code:
Asserting expr 3: `(is_real * (is_real - 1))`
Asserting expr 15: `(is_real * (((((a[0] + b[0]) - cols[0]) + 0) * 2013235201) * (((((a[0] + b[0]) - cols[0]) + 0) * 2013235201) - 1)))`
Asserting expr 25: `(is_real * (((((a[1] + b[1]) - cols[1]) + ((((a[0] + b[0]) - cols[0]) + 0) * 2013235201)) * 2013235201) * (((((a[1] + b[1]) - cols[1]) + ((((a[0] + b[0]) - cols[0]) + 0) * 2013235201)) * 2013235201) - 1)))` -/
def extractedConstraints (cols : AddOperation2 (Fin p))
    (a b : Word (Fin p)) (is_real : Fin p) : Prop :=
  is_real * (is_real - 1) = 0 ∧
  is_real * (((((a[0] + b[0]) - cols[0]) + 0) * 2013235201) * (((((a[0] + b[0]) - cols[0]) + 0) * 2013235201) - 1)) = 0 ∧
  is_real * (((((a[1] + b[1]) - cols[1]) + ((((a[0] + b[0]) - cols[0]) + 0) * 2013235201)) * 2013235201) *
    (((((a[1] + b[1]) - cols[1]) + ((((a[0] + b[0]) - cols[0]) + 0) * 2013235201)) * 2013235201) - 1)) = 0

/-- Cleaned up representation of the `AddOperation` constraints. Assumes that `is_real == 1` -/
def idealizedConstraints (cols : AddOperation2 (Fin p))
    (a b : Word (Fin p)) : Prop :=
  let carry0 := 0
  let carry1 := (a[0] + b[0] - cols[0] + carry0) * baseInv
  let carry2 := (a[1] + b[1] - cols[1] + carry1) * baseInv
  carry1 * (carry1 - 1) = 0 ∧ -- isBool check
  carry2 * (carry2 - 1) = 0 -- isBool check

/-- The idealized constraints are logically equivalent to the extracted ones given `is_real := 1`. -/
lemma extractedConstraints_iff_idealizedConstraints
    (cols : AddOperation2 (Fin p)) (a b : Word (Fin p)) :
    cols.extractedConstraints a b 1 ↔ cols.idealizedConstraints a b := by
  simp [extractedConstraints, idealizedConstraints, Word.isUInt32]

/-- The extracted constraints on `AddOperation` imply the spec. -/
theorem correct [Fact (Nat.Prime p)] (cols : AddOperation2 (Fin p))
    (a b : Word (Fin p)) (hcols : cols.isUInt32) :
    cols.idealizedConstraints a b → cols.spec a b := by
  -- Unfold the definitions of constraints and spec
  simp [idealizedConstraints, spec, sub_eq_zero, mul_eq_zero]
  -- Introduce all of the hypothesis from the constraints
  intros h1 h2 ha_u32 hb_u32
  -- Split on whether the lower limb addition causes a carry
  cases h1 with | inl h1 => ?_ | inr h1 => ?_
  all_goals -- In both cases can now reduce down to the `omega` linear constraint solver
  · rw [h1] at h2
    simp [Fin.add_def, Fin.sub_def, Fin.ext_iff, p, Word.toNat, Word.isUInt32] at *
    sorry
    -- omega

end AddOperation2
