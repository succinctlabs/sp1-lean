import SP1Foundations

import SP1Foundations

structure IsZeroOperation where
  /-- The inverse of the input. -/
  inverse : U16
  /-- Result indicating whether the input is 0. This equals `inverse * input == \ 0`. -/
  result  : U2

namespace IsZeroOperation

def spec (cols : IsZeroOperation)
    (a : U16) (is_real : U2) : Prop :=
  is_real = 1 → (a = 0 ↔ cols.result = 1)

def constraints (cols : IsZeroOperation)
    (a : U16) (is_real : U2) : Prop :=
  (is_real.val * ((1 - (cols.inverse.val * a.val)) - cols.result.val)) = 0
  ∧ (is_real.val * (cols.result.val * (cols.result.val - 1))) = 0
  ∧ (is_real.val * (cols.result.val * (cols.result.val - 1))) = 0
  ∧ (is_real.val * (cols.result.val * a.val)) = 0

theorem correct (cols : IsZeroOperation)
    (a : U16) (is_real : U2) :
    cols.constraints a is_real → cols.spec a is_real := by
  intro ⟨h1, h2, h3, h4⟩ h_is_real
  simp [sub_eq_zero] at *
  aesop

end IsZeroOperation
