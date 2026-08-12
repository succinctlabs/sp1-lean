import SP1Clean.Proofs.Chips.LoadWordChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # LoadWord — physical routing contract -/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

-- Runs at the plain default: the former 1000000 ceiling was ~25x over; measured floor <= 40000.
/-- Project LoadWord's literal `op_a_0 === 0` assertion from the folded native `main`. -/
theorem LoadWordChip.eval_inputOpA0_eq_zero_of_mainConstraints
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env
      ((LoadWordChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 := by
  have routeConstraint : Expression.eval env (input.adapter.op_a_0 - 0) = 0 := by
    apply constraints.1
    simp only [LoadWordChip.main, circuit_norm]
    right; right; right; right; right; right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 0 _
  rw [eval_sub] at routeConstraint
  simpa only [Expression.eval] using sub_eq_zero.mp routeConstraint

end SP1Clean.Soundness
