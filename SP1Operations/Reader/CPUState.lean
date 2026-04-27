import SP1Operations.Reader.CPUState.Operation
import SP1Operations.Reader.CPUState.Constraints

namespace CPUState

lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints cols next_pc clk_increment is_real) ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (¬is_real = 0 →
      ((cols.clk_0_16 - 1) * (8 : Fin KB)⁻¹) < 8192 ∧
      cols.clk_16_24 < 256)
   := by
    simp [constraints, sub_eq_zero, SP1Constraint.toProp]
    tauto

lemma allHold_constraints_iff_is_real (h : is_real = 1) :
  List.Forall SP1Constraint.toProp (constraints cols next_pc clk_increment is_real) ↔
      ((cols.clk_0_16 - 1) * (8 : Fin KB)⁻¹) < 8192 ∧
      cols.clk_16_24 < 256
    := by simp_all [allHold_constraints_iff]

end CPUState
