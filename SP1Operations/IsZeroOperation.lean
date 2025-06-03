import SP1Foundations

import SP1Foundations

structure IsZeroOperation where
  /-- The inverse of the input. -/
  inverse : U16
  /--
  Result indicating whether the input is 0. This equals `inverse * input ==
  \ 0`.
  -/
  result  : U2

namespace IsZeroOperation

def spec
  (cols : IsZeroOperation)
  (a : U16)
  (is_real : U2) : Prop :=
    is_real = U2.one →
    (a = U16.zero ↔ cols.result = U2.one)

def constraints
  (cols : IsZeroOperation)
  (a : U16)
  (is_real : U2) : Prop :=
    (is_real.val * ((1 - (cols.inverse.val * a.val)) - cols.result.val)) = (0 : BabyBear)
    ∧ (is_real.val * (cols.result.val * (cols.result.val - (1 : BabyBear)))) = (0 : BabyBear)
    ∧ (is_real.val * (cols.result.val * (cols.result.val - (1 : BabyBear)))) = (0 : BabyBear)
    ∧ (is_real.val * (cols.result.val * a.val)) = (0 : BabyBear)

theorem correct (cols : IsZeroOperation)
  (a : U16)
  (is_real : U2)
  : cols.constraints a is_real → cols.spec a is_real :=
  by
    intro ⟨h1, h2, h3, h4⟩
    intro h_is_real

    -- Since is_real = 1, substitute and apply 1 * x = x to get original constraints
    have is_real_val_eq_one : is_real.val = 1 := by aesop
    rw [is_real_val_eq_one] at h1 h2 h3 h4
    simp at h1 h2 h3 h4

    -- From constraint h2: cols.result.val * (cols.result.val - 1) = 0
    -- This means cols.result.val = 0 or cols.result.val = 1
    simp [mul_eq_zero, sub_eq_zero] at h2

    -- Show the spec: a = U16.zero ↔ cols.result = U2.one
    constructor

    -- Direction 1: a = U16.zero → cols.result = U2.one
    · intro h_a_zero
      have a_val_zero : a.val = 0 := by simp [h_a_zero, U16.zero]
      rw [a_val_zero] at h1
      simp at h1
      -- h1: 1 - cols.result.val = 0, so cols.result.val = 1
      apply U2.ext
      simp [U2.one]
      rw [sub_eq_zero] at h1
      exact h1.symm

    -- Direction 2: cols.result = U2.one → a = U16.zero
    · intro h_result_one
      have result_val_one : cols.result.val = 1 := by simp [h_result_one, U2.one]
      rw [result_val_one] at h4
      simp at h4
      -- h4: a.val = 0
      cases a with | mk val_a in_range_a =>
      simp [U16.zero]
      exact h4

end IsZeroOperation

-- structure IsZeroOperation2 (T : Type) where
--   inverse : T
--   result : T

-- namespace IsZeroOperation2

-- /-- `IsZeroOperation` should result in wrapping addition of the outputs. -/
-- def spec (cols : IsZeroOperation2 (Fin p)) (a : Fin p) (is_real : Fin p) : Prop :=
--   is_real = 0 ∨ (a = 0 ↔ cols.result = 1)

-- /-- Constraints on `IsZeroOperation` as extracted from the source code:
-- Asserting expr 8: `(is_real * ((1 - (cols.inverse * a)) - cols.result))`
-- Asserting expr 11: `(is_real * (cols.result * (cols.result - 1)))`
-- Asserting expr 13: `(is_real * (cols.result * a))` -/
-- def extractedConstraints (cols : IsZeroOperation2 (Fin p))
--     (a : Fin p) (is_real : Fin p) : Prop :=
--   (is_real * ((1 - (cols.inverse * a)) - cols.result)) = 0 ∧
--   (is_real * (cols.result * (cols.result - 1))) = 0 ∧
--   (is_real * (cols.result * a)) = 0

-- /-- Cleaned up representation of the `IsZeroOperation` constraints. -/
-- def idealizedConstraints (cols : IsZeroOperation2 (Fin p))
--     (a : Fin p) (is_real : Fin p) : Prop :=
--   is_real ≠ 0 → (
--     1 - (cols.inverse * a) = cols.result ∧
--     (cols.result = 0 ∨ cols.result = 1) ∧
--     (cols.result = 0 ∨ a = 0)
--   )

-- variable (cols : IsZeroOperation2 (Fin p)) (a : Fin p) (is_real : Fin p)

-- /-- The idealized constraints are logically equivalent to the extracted ones. -/
-- lemma extractedConstraints_iff_idealizedConstraints [Fact (Nat.Prime p)] :
--     cols.extractedConstraints a is_real ↔ cols.idealizedConstraints a is_real := by
--   by_cases hreal : is_real = 0
--   · simp [extractedConstraints, idealizedConstraints, hreal]
--   · simp [extractedConstraints, idealizedConstraints, hreal, sub_eq_zero]

-- /-- The extracted constraints on `IsZeroOperation` imply the spec. -/
-- theorem correct [Fact (Nat.Prime p)] :
--     cols.extractedConstraints a is_real → cols.spec a is_real := by
--   simp [extractedConstraints_iff_idealizedConstraints, idealizedConstraints, spec]
--   by_cases hreal : is_real = 0
--   · aesop
--   · aesop

-- end IsZeroOperation2
