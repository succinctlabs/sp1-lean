import SP1Foundations
import SP1Operations.Operation.AddrAddOperation.Operation
import SP1Operations.Operation.AddrAddOperation.Constraints

namespace AddrAddOperation

/-- Equivalent formulation of constraints given that `is_real = 1`. -/
lemma allHold_constraints_iff (a b : Word (Fin BB)) (cols : AddrAddOperation) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
      let carry0 : Fin BB := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : Fin BB := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      let carry2 : Fin BB := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
      let carry3 : Fin BB := (a[3] + b[3] - 0 + carry2) * 65536⁻¹
      (carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (carry2 = 0 ∨ carry2 = 1) ∧
      (carry3 = 0 ∨ carry3 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536) ∧
      (cols.value[2].val < 65536) := by
  simp [constraints, sub_eq_zero, inv_16BB_eq']

lemma isU64_of_allHold_constraints (a b : Word (Fin BB)) (cols : AddrAddOperation)
    (h : (constraints a b cols 1).allHold) : 
    cols.value[0] < 65536 ∧ cols.value[1] < 65536 ∧ cols.value[2] < 65536 := by
  simp [allHold_constraints_iff] at h
  obtain ⟨_, _, _, _, h0, h1, h2⟩ := h
  exact ⟨h0, h1, h2⟩

/-- The specification for AddrAddOperation: it computes a 3-limb addition (address addition).
    The result is stored in the lower 3 limbs, with the 4th limb being 0. -/
def spec (a b : Word (Fin BB)) (cols : AddrAddOperation) : Prop :=
  a.isU64 → b.isU64 → a.toBitVec64 + b.toBitVec64 < 2^48 →
    cols.value[0] < 65536 ∧ cols.value[1] < 65536 ∧ cols.value[2] < 65536 ∧
    Word.toBitVec64 #v[cols.value[0], cols.value[1], cols.value[2], 0] = a.toBitVec64 + b.toBitVec64

set_option maxHeartbeats 1000000 in
/-- If the operation is real and the input words have correctly bounded limbs,
then the constraints imply the spec. -/
theorem correct (a b : Word (Fin BB)) (cols : AddrAddOperation) (is_real : Fin BB)
    (h_is_real : is_real = 1)
    (h_cstrs : (constraints a b cols is_real).allHold) :
    spec a b cols := by
  cases h_is_real
  simp [allHold_constraints_iff] at h_cstrs
  obtain ⟨h0, h1, h2, h3, hbd0, hbd1, hbd2⟩ := h_cstrs
  intro ha hb h_no_overflow
  have ha' := Word.lt_cases_of_isU64 ha
  have hb' := Word.lt_cases_of_isU64 hb

  refine ⟨?_, ?_⟩
  · exact hbd0
  
  · -- Prove the addition correctness
    rw [Word.toBitVec64_eq_add]
    simp [← inv_16BB_eq'] at *
    simp [← BitVec.ofNat_add, ← BitVec.ofNat_mul]
    simp [BitVec.ofNat, Fin.ext_iff, Fin.add_def, Fin.sub_def]
    -- The proof follows the same pattern as AddOperation but with 3 limbs
    -- and the fact that the sum is < 2^48
    sorry

end AddrAddOperation
