import SP1Foundations
import SP1Operations.Operation.U16MSBOperation.Operation
import SP1Operations.Operation.U16MSBOperation.Constraints

namespace U16MSBOperation

lemma allHold_constraints_iff
  (a : Fin BB)
  (cols : U16MSBOperation)
  (is_real : Fin BB) :
  (constraints a cols is_real).allHold ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (cols.msb = 0 ∨ cols.msb = 1) ∧
    (¬is_real = 0 → 2 * a - cols.msb * 65536 < 65536)
  := by
    simp [constraints, sub_eq_zero, Fin.lt_iff_val_lt_val]

lemma is_bool_cols_msb
  (a : Fin BB)
  (cols : U16MSBOperation)
  (is_real : Fin BB)
  (h_cstrs : (constraints a cols is_real).allHold) :
    cols.msb = 0 ∨ cols.msb = 1 := by
    simp [constraints, sub_eq_zero] at h_cstrs; tauto

lemma spec
  (a : Fin BB)
  (cols : U16MSBOperation)
  (is_real : Fin BB)
  (h_a_isU16 : a < 65536) :
  List.Forall SP1Constraint.toProp (constraints a cols is_real) →
    (is_real ≠ 0 →
      (cols.msb = if a >= 32768 then 1 else 0)
    )
  := by
    simp [constraints, sub_eq_zero]
    intro _ h_cols_msb h_msb _
    simp [Fin.mul_def, Fin.sub_def] at h_msb
    rcases h_cols_msb <;> simp_all <;>
    [ skip; by_contra! h_a_lt ] <;>
    rw [Nat.mod_eq_of_lt (by omega)] at h_msb <;>
    omega

lemma spec.U64
  (w : Word (Fin BB))
  (cols : U16MSBOperation)
  (is_real : Fin BB)
  (h_w_isU64 : w.isU64) :
  List.Forall SP1Constraint.toProp (constraints w[3] cols is_real) →
    (is_real ≠ 0 → (cols.msb = if w.isNegative then 1 else 0))
  := by
    simp [constraints, sub_eq_zero, Word.isNegative]
    intro _ h_cols_msb h_msb _
    apply Word.lt_cases_of_isU64 at h_w_isU64
    simp [Fin.mul_def, Fin.sub_def] at h_msb
    rcases h_cols_msb <;> simp_all <;>
    [ skip; by_contra! h_a_lt ] <;>
    rw [Nat.mod_eq_of_lt (by omega)] at h_msb <;>
    omega

end U16MSBOperation
