import SP1Operations.Compare.IsZeroWordOperation.Operation
import SP1Operations.Compare.IsZeroWordOperation.Constraints

namespace IsZeroWordOperation

lemma allHold_constraints_iff
  (a : Word (Fin BB))
  (cols : IsZeroWordOperation)
  (is_real) :
  (constraints a cols is_real).allHold ↔
    (IsZeroOperation.constraints a[0] { inverse := cols.is_zero_limb[0].inverse, result := cols.is_zero_limb[0].result } is_real).allHold ∧
    (IsZeroOperation.constraints a[1] { inverse := cols.is_zero_limb[1].inverse, result := cols.is_zero_limb[1].result } is_real).allHold ∧
    (IsZeroOperation.constraints a[2] { inverse := cols.is_zero_limb[2].inverse, result := cols.is_zero_limb[2].result } is_real).allHold ∧
    (IsZeroOperation.constraints a[3] { inverse := cols.is_zero_limb[3].inverse, result := cols.is_zero_limb[3].result } is_real).allHold ∧
    ((is_real = 0 ∨ is_real = 1) ∧
    (cols.result = 0 ∨ cols.result = 1) ∧
    cols.is_zero_first_half = cols.is_zero_limb[0].result * cols.is_zero_limb[1].result ∧
    cols.is_zero_second_half = cols.is_zero_limb[2].result * cols.is_zero_limb[3].result ∧
    (is_real = 0 ∨ cols.result = cols.is_zero_first_half * cols.is_zero_second_half))
  := by simp [and_assoc, sub_eq_zero, constraints]

lemma spec
  (a : Word (Fin BB))
  (cols : IsZeroWordOperation)
  (is_real) :
  (constraints a cols is_real).allHold →
    (is_real ≠ 0 →
      cols.result = if a = #v[(0 : Fin BB), (0 : Fin BB), (0 : Fin BB), (0 : Fin BB)] then 1 else 0)
  := by
  rw [allHold_constraints_iff]
  intro ⟨ zero_op_0, zero_op_1, zero_op_2, zero_op_3, cstrs ⟩ h_is_real
  apply IsZeroOperation.spec at zero_op_0
  apply IsZeroOperation.spec at zero_op_1
  apply IsZeroOperation.spec at zero_op_2
  apply IsZeroOperation.spec at zero_op_3
  simp_all [-Vector.eq_mk]
  split_ifs <;> rw [← Word.eq_pointwise] at * <;> simp_all

end IsZeroWordOperation
