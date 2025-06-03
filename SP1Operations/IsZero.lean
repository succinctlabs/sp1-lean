import SP1Foundations

structure IsZeroOperation where
  /-- The inverse of the input. -/
  inverse : U16
  /--
  Result indicating whether the input is 0. This equals `inverse * input ==
  \ 0`.
  -/
  result  : U2

def IsZeroOperation.spec
  (cols : IsZeroOperation)
  (a : U16)
  (is_real : U2) : Prop :=
    is_real = U2.one →
    (a = U16.zero ↔ cols.result = U2.one)

def IsZeroOperation.constraints
  (cols : IsZeroOperation)
  (a : U16)
  (is_real : U2) : Prop :=
    (is_real.val * ((1 - (cols.inverse.val * a.val)) - cols.result.val)) = (0 : BabyBear)
    ∧ (is_real.val * (cols.result.val * (cols.result.val - (1 : BabyBear)))) = (0 : BabyBear)
    ∧ (is_real.val * (cols.result.val * (cols.result.val - (1 : BabyBear)))) = (0 : BabyBear)
    ∧ (is_real.val * (cols.result.val * a.val)) = (0 : BabyBear)

theorem IsZeroOperation.correct (cols : IsZeroOperation)
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
