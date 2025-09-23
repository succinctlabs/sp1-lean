import SP1Foundations
import SP1Operations.Operation.AddOperation.Operation
import SP1Operations.Operation.AddOperation.Constraints

namespace AddOperation

/-- Equivalent formulation of constraints given that `is_real = 1`. -/
lemma allHold_constraints_iff (a b : Word (Fin KB)) (cols : AddOperation) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
      let carry0 : Fin KB := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : Fin KB := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      let carry2 : Fin KB := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
      let carry3 : Fin KB := (a[3] + b[3] - cols.value[3] + carry2) * 65536⁻¹
      (carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (carry2 = 0 ∨ carry2 = 1) ∧
      (carry3 = 0 ∨ carry3 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536) ∧
      (cols.value[2].val < 65536) ∧
      (cols.value[3].val < 65536) := by
  simp [constraints, sub_eq_zero, inv_16BB_eq']

set_option maxHeartbeats 1000000 in
theorem spec
  {a b : Word (Fin KB)}
  {cols : AddOperation}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    cols.value.isU64 ∧ cols.value.toBitVec64 = execute_RTYPE_pure_w a b .ADD := by
  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨h0, h1, h2, h3, hbds⟩ := cstrs
  apply Word.lt_cases_of_isU64 at h_isU64_a
  apply Word.lt_cases_of_isU64 at h_isU64_b

  constructor
  · clear *- hbds; aesop

  . simp [BitVec.eq_sub_iff_add_eq]
    simp [Word.toBitVec64, Word.toNat]
    rw [← BitVec.toNat_inj, BitVec.toNat_add]
    rcases h0 <;> rcases h1 <;> rcases h2 <;> rcases h3 <;>
    simp_all <;> omega

section gen

theorem spec.gen
  {a b : Word (Fin KB)}
  {cols : AddOperation}
  {is_real : Fin KB}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  List.Forall SP1Constraint.toProp (constraints a b cols is_real) →
    is_real = 1 →
      cols.value.isU64 ∧ cols.value.toBitVec64 = execute_RTYPE_pure_w a b .ADD := by
  intro cstrs is_real; simp_all
  exact spec h_isU64_a h_isU64_b cstrs

end gen

end AddOperation
