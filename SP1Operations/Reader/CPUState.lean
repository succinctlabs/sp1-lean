import SP1Operations.Reader.CPUState.Operation
import SP1Operations.Reader.CPUState.Constraints

namespace CPUState

lemma is_real_is_bool_of_constraints
    (h : (constraints cols next_pc clk_increment is_real).allHold) :
    is_real = 0 ∨ is_real = 1 := by
  simp [constraints, sub_eq_zero] at h
  tauto

end CPUState
