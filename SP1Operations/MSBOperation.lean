import SP1Foundations

structure U16MSBOperation where
  msb : U1

def U16MSBOperation.spec
  (cols : U16MSBOperation)
  (a : U16)
  (is_real : U1) : Prop :=
    is_real = 1 →
    -- MSB is 1 if a >= 2^15, otherwise 0
    (a.val < 32768 ∧ cols.msb = 0) ∨
    (a.val ≥ 32768 ∧ cols.msb = 1)

def U16MSBOperation.constraints
  (cols : U16MSBOperation)
  (a : U16)
  (is_real : U1) : Prop :=
    is_real = 1 →
    -- (2 * a) - (cols.msb * 65536) must be within U16 range
    -- This effectively checks: 2*a - msb*2^16 < 2^16
    -- When msb=0: 2*a < 2^16 (true for a < 2^15)
    -- When msb=1: 2*a - 2^16 < 2^16, i.e., 2*a < 2^17 (true for a < 2^16)
    ((2 : BabyBear) * a) - (cols.msb * (65536 : BabyBear)) < (base : BabyBear)

theorem U16MSBOperation.correct (cols : U16MSBOperation)
  (a : U16)
  (is_real : U1)
  : cols.constraints a is_real → cols.spec a is_real :=
  by
    intro h_constraint
    intro h_is_real
    -- Since is_real = 1, extract the original constraint
    have orig_constraint : ((2 : BabyBear) * a) - (cols.msb * (65536 : BabyBear)) < (base : BabyBear) := h_constraint h_is_real
    -- Show the spec holds
    show (a.val < 32768 ∧ cols.msb = 0) ∨ (a.val ≥ 32768 ∧ cols.msb = 1)
    -- Get the ranges we need
    have a_in_range := a.in_range

    -- Case split on cols.msb value
    cases h_msb : cols.msb.in_range'' with
    | inl h_zero =>
      -- Case: cols.msb.val = 0
      left
      have h_msb_val : cols.msb = 0 := h_zero
      simp [h_msb_val] at orig_constraint
      simp [h_msb_val, base] at *

      rw [Fin.lt_iff_val_lt_val] at orig_constraint
      simp [BabyBearPrime] at *
      rw [Fin.val_mul] at orig_constraint
      rw [Nat.mod_eq_of_lt] at orig_constraint

      · omega
      · omega

    | inr h_one =>
      -- Case: cols.msb.val = 1
      right
      have h_msb_val : cols.msb = 1 := h_one
      simp [h_msb_val] at orig_constraint
      simp [h_msb_val, base] at *

      rw [Fin.lt_iff_val_lt_val] at orig_constraint
      simp [BabyBearPrime] at *
      rw [Fin.sub_def] at orig_constraint
      rw [Fin.val_mul] at orig_constraint
      simp [BabyBearPrime] at *
      -- wrong :(
      rw [Nat.mod_eq_of_lt] at orig_constraint

      · omega
      ·

        sorry

-- Example demonstrating U1 usage with numeric literals
example : U16MSBOperation := {
  msb := 1  -- Can write 1 directly instead of 1
}

example : U16MSBOperation := {
  msb := 0  -- Can write 0 directly instead of 0
}

-- Example showing the spec works with numeric literals
example (a : U16) (h : a.val = 40000) :
  U16MSBOperation.spec ⟨1⟩ a 1 := by
  intro h_is_real
  right
  constructor
  · -- Show a.val ≥ 32768
    rw [h]
    norm_num
  · -- Show msb = 1
    rfl
