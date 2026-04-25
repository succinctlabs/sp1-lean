import SP1Foundations
import SP1Operations.Operation.SubOperation.Operation
import SP1Operations.Operation.SubOperation.Constraints

namespace SubOperation

-- iff-characterization of constraints
lemma allHold_constraints_iff (a b : Word (Fin KB)) (cols : SubOperation) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
    let carry0 : Fin KB := (b[0] + cols.value[0] - a[0]) * 65536⁻¹
    let carry1 : Fin KB := (b[1] + cols.value[1] - a[1] + carry0) * 65536⁻¹
    let carry2 : Fin KB := (b[2] + cols.value[2] - a[2] + carry1) * 65536⁻¹
    let carry3 : Fin KB := (b[3] + cols.value[3] - a[3] + carry2) * 65536⁻¹
    (carry0 = 0 ∨ carry0 = 1) ∧
    (carry1 = 0 ∨ carry1 = 1) ∧
    (carry2 = 0 ∨ carry2 = 1) ∧
    (carry3 = 0 ∨ carry3 = 1) ∧
    (cols.value[0].val < 65536) ∧
    (cols.value[1].val < 65536) ∧
    (cols.value[2].val < 65536) ∧
    (cols.value[3].val < 65536) := by
  simp [constraints, ← inv_16BB_eq', sub_eq_zero]
  constructor <;> intro ⟨h0, h1, h2, h3, r0, r1, r2, r3⟩ <;> split_ands <;>
  [ clear *- h0; clear *- h1; clear *- h2; clear *- h3; exact r0; exact r1; exact r2; exact r3;
    clear *- h0; clear *- h1; clear *- h2; clear *- h3; exact r0; exact r1; exact r2; exact r3 ] <;>
  omega

set_option maxHeartbeats 1000000 in

-- arithmetic spec proof over Word/BitVec
theorem spec
  {a b : Word (Fin KB)}
  {cols : SubOperation}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    cols.value.isU64 ∧ cols.value.toBitVec64 = execute_RTYPE_pure_w a b .SUB := by
  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨h0, h1, h2, h3, hbds⟩ := cstrs
  apply Word.lt_cases_of_isU64 at h_isU64_a
  apply Word.lt_cases_of_isU64 at h_isU64_b
  constructor
  · clear *- hbds; aesop
  · simp [BitVec.eq_sub_iff_add_eq]
    simp [Word.toBitVec64, Word.toNat]
    rw [← BitVec.toNat_inj, BitVec.toNat_add]
    rcases h0 <;> rcases h1 <;> rcases h2 <;> rcases h3 <;>
    simp_all <;> omega

end SubOperation
