import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Operation.AddwOperation.Operation
import SP1Operations.Operation.AddwOperation.Constraints

namespace AddwOperation

/-- Equivalent formulation of constraints given that `is_real = 1`. -/
lemma allHold_constraints_iff (a b : Word (Fin KB)) (cols : AddwOperation (Fin KB)) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
      let carry0 : Fin KB := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : Fin KB := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      (U16MSBOperation.constraints cols.value[1] cols.msb 1).allHold ∧
      ((carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (cols.value[0] < 65536) ∧
      (cols.value[1] < 65536)) := by
  simp [constraints, U16MSBOperation.constraints, sub_eq_zero]
  tauto

/-- Polymorphic companion of `allHold_constraints_iff` over `ZMod p`. The
auto-gen carries match the iff RHS's natural form (Add-style, no
sign-flip), so bare `simp + tauto` closes — same recipe as
`AddOperation.allHold_constraints_iff_poly`. -/
lemma allHold_constraints_iff_poly
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (a b : Word (ZMod p)) (cols : AddwOperation (ZMod p)) :
    SP1ConstraintList.allHold_poly (constraints a b cols 1) ↔
      let carry0 : ZMod p := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : ZMod p := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      List.Forall SP1Constraint.toProp_poly (U16MSBOperation.constraints cols.value[1] cols.msb 1) ∧
      ((carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536)) := by
  simp [constraints, U16MSBOperation.constraints,
        sub_eq_zero, SP1Constraint.toProp_poly]
  tauto

theorem spec
  {a b : Word (Fin KB)}
  {cols : AddwOperation (Fin KB)}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    HWord.isU32 (cols.value) ∧
    HWord.toBitVec32 (cols.value) = execute_RTYPEW_pure_32_w a b .ADDW ∧
    cols.msb.msb = if (HWord.toBitVec32 cols.value).msb then 1 else 0
  := by
    intro cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨hmsb, h0, h1, hbds⟩ := cstrs
    apply Word.lt_cases_of_isU64 at h_isU64_a
    apply Word.lt_cases_of_isU64 at h_isU64_b
    split_ands
    · clear *- hbds; aesop
    · simp [BitVec.eq_sub_iff_add_eq]
      simp [HWord.toBitVec32, Word.low, HWord.toNat]
      rw [← BitVec.toNat_inj, BitVec.toNat_add]
      aesop (add safe (by omega))
    · simp [Fin.lt_def] at hbds
      apply U16MSBOperation.spec (by omega) at hmsb
      simp [HWord.toBitVec32, HWord.toNat, BitVec.msb_eq_toNat]
      simp at hmsb; split_ifs at * <;> omega

end AddwOperation
