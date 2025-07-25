import SP1Operations.Compare.U16CompareOperation.Operation
import SP1Operations.Compare.U16CompareOperation.Constraints

namespace U16CompareOperation

lemma allHold_constraints_iff
  (a b : Fin BB)
  (cols : U16CompareOperation)
  (is_real : Fin BB) :
  (constraints a b cols is_real).allHold ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (cols.bit = 0 ∨ cols.bit = 1) ∧
    (¬is_real = 0 → a - b + cols.bit * 65536 < 65536)
  := by
    simp [constraints, sub_eq_zero, Fin.lt_iff_val_lt_val]

lemma spec
  (a b : Fin BB)
  (cols : U16CompareOperation)
  (is_real : Fin BB)
  (h_a_isU16 : (a : ℕ) < 65536)
  (h_b_isU16 : (b : ℕ) < 65536) :
  (constraints a b cols is_real).allHold →
    is_real ≠ 0 → (cols.bit = if (a : ℕ) < b then 1 else 0)
  := by
    simp [constraints, sub_eq_zero]
    split_ifs <;> omega

end U16CompareOperation
