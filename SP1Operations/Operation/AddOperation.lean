import SP1Foundations
import SP1Operations.Operation.AddOperation.Operation
import SP1Operations.Operation.AddOperation.Constraints

namespace AddOperation

/-- Equivalent formulation of constraints given that `is_real = 1`. -/
lemma allHold_constraints_iff (a b : Word (Fin BB)) (cols : AddOperation) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
      let carry0 : Fin BB := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : Fin BB := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      let carry2 : Fin BB := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
      let carry3 : Fin BB := (a[3] + b[3] - cols.value[3] + carry2) * 65536⁻¹
      (carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (carry2 = 0 ∨ carry2 = 1) ∧
      (carry3 = 0 ∨ carry3 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536) ∧
      (cols.value[2].val < 65536) ∧
      (cols.value[3].val < 65536) := by
  simp [constraints, sub_eq_zero, inv_16BB_eq']

def spec (a b : Word (Fin BB)) (cols : AddOperation) : Prop :=
  a.isU64 → b.isU64 → cols.value.isU64 ∧ cols.value.toBitVec64 = a.toBitVec64 + b.toBitVec64

set_option maxHeartbeats 1000000 in
/-- If the operation is real and the input words have correctly bounded limbs,
then the constraints imply the spec. -/
theorem correct (a b : Word (Fin BB)) (cols : AddOperation) (is_real : Fin BB)
    (h_is_real : is_real = 1)
    (h_cstrs : (constraints a b cols is_real).allHold) :
    spec a b cols := by
  cases h_is_real
  simp [allHold_constraints_iff] at h_cstrs
  obtain ⟨h0, h1, h2, h3, hbds⟩ := h_cstrs
  intro ha hb
  have ha' := Word.lt_cases_of_isU64 ha
  have hb' := Word.lt_cases_of_isU64 hb

  constructor
  · clear *- hbds
    aesop

  . rw [Word.toBitVec64_add_toBitVec64, Word.toBitVec64_eq_add]
    simp [← inv_16BB_eq'] at *
    simp [← BitVec.ofNat_add, ← BitVec.ofNat_mul]
    simp [BitVec.ofNat, Fin.ext_iff, Fin.add_def, Fin.sub_def]
    rcases h0 <;> rcases h1 <;> rcases h2 <;> rcases h3 <;>
    simp_all <;> omega

end AddOperation
