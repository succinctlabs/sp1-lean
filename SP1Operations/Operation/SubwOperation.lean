import SP1Foundations
import SP1Operations.Operation.SubwOperation.Operation
import SP1Operations.Operation.SubwOperation.Constraints

set_option linter.style.setOption false
set_option maxHeartbeats 10000000

namespace SubwOperation

lemma allHold_constraints_iff (a b : Word (Fin KB)) (cols : SubwOperation) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
      let carry0 : Fin KB := (b[0] + cols.value[0] - a[0]) * 65536⁻¹
      let carry1 : Fin KB := (b[1] + cols.value[1] - a[1] + carry0) * 65536⁻¹
      List.Forall SP1Constraint.toProp (U16MSBOperation.constraints cols.value[1] cols.msb 1) ∧
      ((carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (cols.value[0] < 65536) ∧
      (cols.value[1] < 65536)) := by
  simp [constraints, ← inv_16BB_eq', sub_eq_zero]
  omega

theorem spec
  {a b : Word (Fin KB)}
  {cols : SubwOperation}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    HWord.isU32 (cols.value) ∧
    HWord.toBitVec32 (cols.value) = execute_RTYPEW_pure_32_w a b .SUBW ∧
    cols.msb.msb = if (HWord.toBitVec32 cols.value).msb then 1 else 0
  := by
    intro cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨hmsb, h0, h1, hbds⟩ := cstrs
    apply Word.lt_cases_of_isU64 at h_isU64_a
    apply Word.lt_cases_of_isU64 at h_isU64_b
    split_ands
    . clear *- hbds; aesop
    . simp [BitVec.eq_sub_iff_add_eq]
      simp [HWord.toBitVec32, Word.low, HWord.toNat]
      rw [← BitVec.toNat_inj, BitVec.toNat_add]
      aesop (add safe (by omega))
    . simp [Fin.lt_def] at hbds
      apply U16MSBOperation.spec (by omega) at hmsb
      simp [HWord.toBitVec32, HWord.toNat, BitVec.msb_eq_toNat]
      simp at hmsb; split_ifs at * <;> omega

end SubwOperation
