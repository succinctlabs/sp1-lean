import SP1Operations.Compare.IsEqualWordOperation.Operation
import SP1Operations.Compare.IsEqualWordOperation.Constraints

namespace IsEqualWordOperation

lemma allHold_constraints_iff
  (a b : Word (Fin BB))
  (cols : IsEqualWordOperation)
  (is_real : Fin BB) :
  (constraints a b cols is_real).allHold ↔
    (IsZeroWordOperation.constraints
      #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]
      { is_zero_limb :=
          #v[{ inverse := cols.is_diff_zero.is_zero_limb[0].inverse, result := cols.is_diff_zero.is_zero_limb[0].result },
             { inverse := cols.is_diff_zero.is_zero_limb[1].inverse, result := cols.is_diff_zero.is_zero_limb[1].result },
             { inverse := cols.is_diff_zero.is_zero_limb[2].inverse, result := cols.is_diff_zero.is_zero_limb[2].result },
             { inverse := cols.is_diff_zero.is_zero_limb[3].inverse, result := cols.is_diff_zero.is_zero_limb[3].result } ],
        is_zero_first_half := cols.is_diff_zero.is_zero_first_half,
        is_zero_second_half := cols.is_diff_zero.is_zero_second_half,
        result := cols.is_diff_zero.result }
      is_real).allHold ∧
    (is_real = 0 ∨ is_real = 1)
  := by simp [and_assoc, sub_eq_zero, constraints]

lemma spec
  (a b : Word (Fin BB))
  (cols : IsEqualWordOperation)
  (is_real : Fin BB) :
  (constraints a b cols is_real).allHold →
    (is_real ≠ 0 →
      cols.is_diff_zero.result = if a = b then 1 else 0)
  := by
  rw [allHold_constraints_iff]
  intro ⟨ cstrs, h_is_real_bool ⟩ h_is_real
  apply IsZeroWordOperation.spec at cstrs
  simp [sub_eq_zero] at *
  split_ifs <;> rw [← Word.eq_pointwise] at * <;> simp_all

end IsEqualWordOperation
