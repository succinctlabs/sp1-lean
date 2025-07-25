import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Operation.AddwOperation.Operation
import SP1Operations.Operation.AddwOperation.Constraints

namespace AddwOperation

/-- Equivalent formulation of constraints given that `is_real = 1`. -/
lemma allHold_constraints_iff (a b : Word (Fin BB)) (cols : AddwOperation) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
      let carry0 : Fin BB := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : Fin BB := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      (U16MSBOperation.constraints cols.value[1] cols.msb 1).allHold ∧
      ((carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (cols.value[0] < 65536) ∧
      (cols.value[1] < 65536)) := by
  simp [constraints, U16MSBOperation.constraints, sub_eq_zero, inv_16BB_eq']
  tauto

def spec (a b : Word (Fin BB)) (cols : AddwOperation) : Prop :=
  a.isU64 → b.isU64 →
    HalfWord.isU32 (cols.value) ∧
    HalfWord.toBitVec32 (cols.value) = a.low32.toBitVec32 + b.low32.toBitVec32 ∧
    cols.msb.msb = if (HalfWord.toBitVec32 cols.value).msb then 1 else 0

set_option maxHeartbeats 1000000 in
/-- If the operation is real and the input words have correctly bounded limbs,
then the constraints imply the spec. -/
theorem correct (a b : Word (Fin BB)) (cols : AddwOperation) (is_real : Fin BB)
    (h_is_real : is_real = 1)
    (h_cstrs : (constraints a b cols is_real).allHold) :
    spec a b cols := by
  cases h_is_real
  simp [allHold_constraints_iff] at h_cstrs
  obtain ⟨hmsb, h0, h1, hbds⟩ := h_cstrs
  intro ha hb
  have ha' := Word.lt_cases_of_isU64 ha
  have hb' := Word.lt_cases_of_isU64 hb

  constructor
  · clear *- hbds
    aesop

  . constructor
    . rw [HalfWord.toBitVec32_add_toBitVec32, HalfWord.toBitVec32_eq_add]
      simp [← inv_16BB_eq'] at *
      simp [Word.low32, ← BitVec.ofNat_add, ← BitVec.ofNat_mul]
      simp [BitVec.ofNat, Fin.ext_iff, Fin.add_def, Fin.sub_def]
      rcases h0 <;> rcases h1 <;>
      simp_all <;> omega
    . simp [Fin.lt_iff_val_lt_val] at hbds
      apply (U16MSBOperation.spec cols.value[1] cols.msb 1 (by omega)) at hmsb
      simp [HalfWord.toBitVec32, HalfWord.toNat, BitVec.msb_eq_toNat]
      simp at hmsb; split_ifs at * <;> omega

end AddwOperation
