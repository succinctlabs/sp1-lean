-- import SP1Foundations

-- structure IsZeroOperation where
--   /-- The inverse of the input. -/
--   inverse : U16
--   /-- Result indicating whether the input is 0. This equals `inverse * input == \ 0`. -/
--   result  : U1

-- namespace IsZeroOperation

-- def spec (cols : IsZeroOperation)
--     (a : U16) (is_real : U1) : Prop :=
--   is_real = 1 → (a = 0 ↔ cols.result = 1)

-- def constraints (cols : IsZeroOperation)
--     (a : U16) (is_real : U1) : SP1ConstraintList :=
--   [
--     .assertZero (is_real.val * ((1 - (cols.inverse.val * a.val)) - cols.result.val)),
--     .assertZero (is_real.val * (cols.result.val * (cols.result.val - 1))),
--     .assertZero (is_real.val * (cols.result.val * (cols.result.val - 1))),
--     .assertZero (is_real.val * (cols.result.val * a.val))
--   ]

-- theorem correct (cols : IsZeroOperation)
--     (a : U16) (is_real : U1) :
--     (cols.constraints a is_real).allHold → cols.spec a is_real := by
--   simp [constraints, spec, sub_eq_zero]
--   aesop

-- end IsZeroOperation
