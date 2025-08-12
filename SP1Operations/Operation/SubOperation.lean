import SP1Foundations
import SP1Operations.Operation.SubOperation.Operation
import SP1Operations.Operation.SubOperation.Constraints

namespace SubOperation

set_option maxHeartbeats 2000000 in
/-- Equivalent formulation of constraints given that `is_real = 1`. -/
lemma allHold_constraints_iff (a b : Word (Fin BB)) (cols : SubOperation) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
    let carry0 : Fin BB := (b[0] + cols.value[0] - a[0]) * 65536⁻¹
    let carry1 : Fin BB := (b[1] + cols.value[1] - a[1] + carry0) * 65536⁻¹
    let carry2 : Fin BB := (b[2] + cols.value[2] - a[2] + carry1) * 65536⁻¹
    let carry3 : Fin BB := (b[3] + cols.value[3] - a[3] + carry2) * 65536⁻¹
    (carry0 = 0 ∨ carry0 = 1) ∧
    (carry1 = 0 ∨ carry1 = 1) ∧
    (carry2 = 0 ∨ carry2 = 1) ∧
    (carry3 = 0 ∨ carry3 = 1) ∧
    (cols.value[0].val < 65536) ∧
    (cols.value[1].val < 65536) ∧
    (cols.value[2].val < 65536) ∧
    (cols.value[3].val < 65536) := by
  simp [constraints, ← inv_16BB_eq', sub_eq_zero]
  constructor <;> intro ⟨ h0, h1, h2, h3, r0, r1, r2, r3 ⟩
  . split_ands <;>
    [ omega; omega; omega; omega; exact r0; exact r1; exact r2; exact r3]
  . split_ands <;> [ clear *- h0; clear *- h1; clear *- h2; clear *- h3; exact r0; exact r1; exact r2; exact r3]
    . omega
    . omega
    . rcases h2 <;> [ right; left ] <;> omega
    . rcases h3 <;> [ right; left ] <;> omega

def spec (a b : Word (Fin BB)) (cols : SubOperation) : Prop :=
  a.isU64 → b.isU64 → cols.value.isU64 ∧ cols.value.toBitVec64 = execute_RTYPE_pure_w a b .SUB

set_option maxHeartbeats 1000000 in
/-- If the operation is real and the input words have correctly bounded limbs,
then the constraints imply the spec. -/
theorem correct (a b : Word (Fin BB)) (cols : SubOperation) (is_real : Fin BB)
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

  . simp [BitVec.eq_sub_iff_add_eq]
    simp [Word.toBitVec64, Word.toNat]
    rw [← BitVec.toNat_inj, BitVec.toNat_add]
    rcases h0 <;> rcases h1 <;> rcases h2 <;> rcases h3 <;>
    simp_all <;> omega

end SubOperation
