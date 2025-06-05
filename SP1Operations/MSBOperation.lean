import SP1Foundations

structure U16MSBOperation where
  msb : U1

def U16MSBOperation.spec
  (cols : U16MSBOperation)
  (a : U16)
  (is_real : U1) : Prop :=
    is_real = U1.one →
    -- MSB is 1 if a >= 2^15, otherwise 0
    (a.val.val < 32768 ∧ cols.msb = 0) ∨
    (a.val.val ≥ 32768 ∧ cols.msb = 1)

def U16MSBOperation.constraints
  (cols : U16MSBOperation)
  (a : U16)
  (is_real : U1) : Prop :=
    is_real = U1.one →
    -- (2 * a) - (cols.msb * 65536) must be within U16 range
    -- This effectively checks: 2*a - msb*2^16 < 2^16
    -- When msb=0: 2*a < 2^16 (true for a < 2^15)
    -- When msb=1: 2*a - 2^16 < 2^16, i.e., 2*a < 2^17 (true for a < 2^16)
    ((2 : BabyBear) * a.val) - (cols.msb.val * (65536 : BabyBear)) < (base : BabyBear)

theorem U16MSBOperation.correct (cols : U16MSBOperation)
  (a : U16)
  (is_real : U1)
  : cols.constraints a is_real → cols.spec a is_real :=
  by
    intro h_constraint
    intro h_is_real
    -- Since is_real = U1.one, extract the original constraint
    have orig_constraint : ((2 : BabyBear) * a.val) - (cols.msb.val * (65536 : BabyBear)) < (base : BabyBear) := h_constraint h_is_real
    -- Show the spec holds
    show (a.val.val < 32768 ∧ cols.msb = 0) ∨ (a.val.val ≥ 32768 ∧ cols.msb = 1)
    -- Get the ranges we need
    have a_in_range := a.in_range

    -- Case split on cols.msb value
    cases h_msb : cols.msb.in_range with
    | inl h_zero =>
      -- Case: cols.msb.val = 0
      left
      have h_msb_val : cols.msb.val = 0 := h_zero
      rw [h_msb_val] at orig_constraint
      constructor
      · -- Show a.val.val < 32768
        -- orig_constraint : 2 * a.val - 0 * 65536 < 65536
        -- Note: 0 : BabyBear is actually Fin.mk 0, so we need to handle this carefully
        have h_simplify : (2 : BabyBear) * a.val - (0 : BabyBear) * (65536 : BabyBear) = (2 : BabyBear) * a.val := by
          ring
        rw [h_simplify] at orig_constraint
        -- Convert to natural numbers
        have h_constraint_nat : (2 * a.val).val < 65536 := by
          simp only [Fin.lt_iff_val_lt_val] at orig_constraint
          exact orig_constraint
        -- Show that 2 * a.val doesn't wrap
        have h_no_wrap : (2 * a.val).val = 2 * a.val.val := by
          simp only [Fin.val_mul]
          apply Nat.mod_eq_of_lt
          have : a.val.val < base := a_in_range
          simp [BabyBearPrime, base] at *
          omega
        rw [h_no_wrap] at h_constraint_nat
        -- From 2 * a.val.val < 65536, deduce a.val.val < 32768
        omega

      · -- Show cols.msb = 0
        -- Since cols.msb.val = 0 and cols.msb has type U1, it must equal U1.zero
        have : cols.msb = U1.zero := by
          ext
          simp [U1.zero]
          exact h_zero
        rw [this]
        rfl

    | inr h_one =>
      -- Case: cols.msb.val = 1
      right
      have h_msb_val : cols.msb.val = 1 := h_one
      rw [h_msb_val] at orig_constraint
      constructor
      · -- Show a.val.val ≥ 32768
        -- By contradiction: assume a.val.val < 32768
        by_contra h_not_ge
        push_neg at h_not_ge

        -- orig_constraint : 2 * a.val - 1 * 65536 < 65536
        -- Simplify 1 * 65536 = 65536
        have h_one_mul : (1 : BabyBear) * (65536 : BabyBear) = 65536 := by simp
        rw [h_one_mul] at orig_constraint

        -- Convert to natural numbers
        have h_constraint_nat : ((2 : BabyBear) * a.val - (65536 : BabyBear)).val < 65536 := by
          simp only [Fin.lt_iff_val_lt_val] at orig_constraint
          exact orig_constraint

        -- When a.val.val < 32768, we have 2 * a.val.val < 65536
        have h_2a_small : 2 * a.val.val < 65536 := by
          omega

        -- So (2 * a.val) as BabyBear has value 2 * a.val.val (no wrap)
        have h_2a_val : ((2 : BabyBear) * a.val).val = 2 * a.val.val := by
          simp only [Fin.val_mul]
          apply Nat.mod_eq_of_lt
          have : a.val.val < base := a_in_range
          simp [BabyBearPrime, base] at *
          omega

        -- Since 2 * a.val.val < 65536, the subtraction wraps around
        -- In modular arithmetic, when x < y, x - y ≡ x + p - y (mod p)
        have h_sub_wrap : ((2 : BabyBear) * a.val - (65536 : BabyBear)).val =
                          2 * a.val.val + BabyBearPrime - 65536 := by
          simp only [Fin.sub_def]
          rw [h_2a_val]
          -- We have 2 * a.val.val < 65536 < BabyBearPrime
          -- So (BabyBearPrime - 65536 + 2 * a.val.val) % BabyBearPrime = BabyBearPrime - 65536 + 2 * a.val.val
          have h1 : (65536 : BabyBear).val = 65536 := rfl
          simp only [h1]
          -- Since 2 * a.val.val < 65536, we have BabyBearPrime - 65536 + 2 * a.val.val < BabyBearPrime
          have h_lt : BabyBearPrime - 65536 + 2 * a.val.val < BabyBearPrime := by
            simp [BabyBearPrime]
            omega
          rw [Nat.mod_eq_of_lt h_lt]
          -- Now we need to show BabyBearPrime - 65536 + 2 * a.val.val = 2 * a.val.val + BabyBearPrime - 65536
          simp [BabyBearPrime]
          ring

        -- The wrapped value doesn't need modulo
        have h_no_mod : (2 * a.val.val + BabyBearPrime - 65536) % BabyBearPrime =
                        2 * a.val.val + BabyBearPrime - 65536 := by
          apply Nat.mod_eq_of_lt
          simp [BabyBearPrime]
          omega

        rw [h_sub_wrap] at h_constraint_nat
        -- Now h_constraint_nat says: 2 * a.val.val + BabyBearPrime - 65536 < 65536
        -- This means BabyBearPrime < 131072 - 2 * a.val.val ≤ 131072
        have : BabyBearPrime < 131072 := by
          omega
        -- But BabyBearPrime = 2013265921 > 131072, contradiction
        norm_num [BabyBearPrime] at this

      · -- Show cols.msb = 1
        -- Since cols.msb.val = 1 and cols.msb has type U1, it must equal U1.one
        have : cols.msb = U1.one := by
          ext
          simp only [U1.one]
          simp [h_one]
        rw [this]
        rfl

-- Example demonstrating U1 usage with numeric literals
example : U16MSBOperation := {
  msb := 1  -- Can write 1 directly instead of U1.one
}

example : U16MSBOperation := {
  msb := 0  -- Can write 0 directly instead of U1.zero
}

-- Example showing the spec works with numeric literals
example (a : U16) (h : a.val.val = 40000) :
  U16MSBOperation.spec ⟨1⟩ a U1.one := by
  intro h_is_real
  right
  constructor
  · -- Show a.val.val ≥ 32768
    rw [h]
    norm_num
  · -- Show msb = 1
    rfl
