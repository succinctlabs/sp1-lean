import SP1Foundations
import SP1Operations.Compare.IsZeroOperation.Operation
import SP1Operations.Compare.IsZeroOperation.Constraints

namespace IsZeroOperation

lemma allHold_constraints_iff
  (a : Fin BB)
  (cols : IsZeroOperation)
  (is_real) :
  (constraints a cols is_real).allHold ↔
    (is_real = 0 ∨ cols.result = 1 - cols.inverse * a) ∧
    (is_real = 0 ∨ cols.result = 0 ∨ cols.result = 1) ∧
    (is_real = 0 ∨ cols.result = 0 ∨ a = 0)
  := by
    simp [constraints, sub_eq_zero, @eq_comm _ (_ - _ * _)]

lemma spec
  (a : Fin BB)
  (cols : IsZeroOperation)
  (is_real) :
  (constraints a cols is_real).allHold →
    (is_real ≠ 0 → cols.result = if (a = 0) then 1 else 0)
  := by
    rw [allHold_constraints_iff]
    aesop

end IsZeroOperation
