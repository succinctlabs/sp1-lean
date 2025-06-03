import SP1Foundations

structure IsZeroOperation2 (T : Type) where
  inverse : T
  result : T

namespace IsZeroOperation2

/-- `IsZeroOperation` should result in wrapping addition of the outputs. -/
def spec (cols : IsZeroOperation2 (Fin p)) (a : Fin p) (is_real : Fin p) : Prop :=
  is_real = 0 ∨ (a = 0 ↔ cols.result = 1)

/-- Constraints on `IsZeroOperation` as extracted from the source code:
Asserting expr 8: `(is_real * ((1 - (cols.inverse * a)) - cols.result))`
Asserting expr 11: `(is_real * (cols.result * (cols.result - 1)))`
Asserting expr 13: `(is_real * (cols.result * a))` -/
def extractedConstraints (cols : IsZeroOperation2 (Fin p))
    (a : Fin p) (is_real : Fin p) : Prop :=
  (is_real * ((1 - (cols.inverse * a)) - cols.result)) = 0 ∧
  (is_real * (cols.result * (cols.result - 1))) = 0 ∧
  (is_real * (cols.result * a)) = 0

/-- Cleaned up representation of the `IsZeroOperation` constraints. -/
def idealizedConstraints (cols : IsZeroOperation2 (Fin p))
    (a : Fin p) (is_real : Fin p) : Prop :=
  is_real ≠ 0 → (
    1 - (cols.inverse * a) = cols.result ∧
    (cols.result = 0 ∨ cols.result = 1) ∧
    (cols.result = 0 ∨ a = 0)
  )

variable (cols : IsZeroOperation2 (Fin p)) (a : Fin p) (is_real : Fin p)

/-- The idealized constraints are logically equivalent to the extracted ones. -/
lemma extractedConstraints_iff_idealizedConstraints [Fact (Nat.Prime p)] :
    cols.extractedConstraints a is_real ↔ cols.idealizedConstraints a is_real := by
  by_cases hreal : is_real = 0
  · simp [extractedConstraints, idealizedConstraints, hreal]
  · simp [extractedConstraints, idealizedConstraints, hreal, sub_eq_zero]

/-- The extracted constraints on `IsZeroOperation` imply the spec. -/
theorem correct [Fact (Nat.Prime p)] :
    cols.extractedConstraints a is_real → cols.spec a is_real := by
  simp [extractedConstraints_iff_idealizedConstraints, idealizedConstraints, spec]
  by_cases hreal : is_real = 0
  · aesop
  · aesop

end IsZeroOperation2
