import SP1Clean.Proofs.Chips.LoadByteChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # LoadByte — physical routing contract

This file exposes the one structural fact the whole-machine decoder needs from LoadByte's
complete native assertion system: ordinary LB/LBU rows are routed away from `x0`.  The proof
projects the literal `op_a_0 === 0` assertion from the folded `main`; it does not obtain routing
from the semantic `Spec` or from a trace-generator convention.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

set_option maxHeartbeats 1000000 in
/-- Project LoadByte's physical non-`x0` route while its circuit input stays folded. -/
theorem LoadByteChip.eval_inputOpA0_eq_zero_of_mainConstraints
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env
      ((LoadByteChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 := by
  have routeConstraint : Expression.eval env (input.adapter.op_a_0 - 0) = 0 := by
    apply constraints.1
    simp only [LoadByteChip.main, circuit_norm]
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 0 _
  rw [eval_sub] at routeConstraint
  simpa only [Expression.eval] using sub_eq_zero.mp routeConstraint

end SP1Clean.Soundness
