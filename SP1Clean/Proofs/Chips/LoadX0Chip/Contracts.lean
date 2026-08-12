import SP1Clean.Proofs.Chips.LoadX0Chip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # LoadX0 — physical routing contract

This file exposes the one structural fact the whole-machine decoder needs from LoadX0's complete
native assertion system: every active row is routed to `x0`. The proof projects the literal
`is_real * (op_a_0 - 1) === 0` assertion from the folded `main`; it does not obtain routing from
the semantic `Spec` or a trace-generator convention.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

-- General expression/membership helpers: none of them needs a magnitude fact, so it is
-- introduced further down, over exactly the two declarations that carry it.
variable {p : ℕ} [Fact p.Prime]

private theorem expression_eval_sub (env : Environment (ZMod p))
    (a b : Expression (ZMod p)) :
    Expression.eval env (a - b) = Expression.eval env a - Expression.eval env b :=
  eval_sub env a b

private theorem expression_eval_mul (env : Environment (ZMod p))
    (a b : Expression (ZMod p)) :
    Expression.eval env (a * b) = Expression.eval env a * Expression.eval env b :=
  eval_mul env a b

private theorem expression_eval_add (env : Environment (ZMod p))
    (a b : Expression (ZMod p)) :
    Expression.eval env (a + b) = Expression.eval env a + Expression.eval env b :=
  eval_add env a b

private theorem evalSelectorSum (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) :
    Expression.eval env
        (input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
          input.is_lw + input.is_lwu + input.is_ld) =
      Expression.eval env input.is_lb + Expression.eval env input.is_lbu +
        Expression.eval env input.is_lh + Expression.eval env input.is_lhu +
          Expression.eval env input.is_lw + Expression.eval env input.is_lwu +
            Expression.eval env input.is_ld := by
  simp only [expression_eval_add]

private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

section RouteProjection
variable [Fact (2 ^ 17 < p)]

private theorem loadX0RouteConstraint_mem
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    (input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
      input.is_lw + input.is_lwu + input.is_ld) *
        (input.adapter.op_a_0 - 1) - 0 ∈
      ((LoadX0Chip.main input).operations offset).constraints := by
  simp only [LoadX0Chip.main, circuit_norm]
  iterate 15 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem
      ((input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
        input.is_lw + input.is_lwu + input.is_ld) *
          (input.adapter.op_a_0 - 1)) 0 _

-- Runs at the plain default: the former 1000000 ceiling was ~25x over; measured floor <= 40000.
/-- Project LoadX0's active `x0` route while its completed circuit stays folded. -/
theorem LoadX0Chip.eval_inputOpA0_eq_one_of_mainConstraints
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env
      ((LoadX0Chip.main input).operations offset))
    (real : Expression.eval env input.is_lb + Expression.eval env input.is_lbu +
      Expression.eval env input.is_lh + Expression.eval env input.is_lhu +
        Expression.eval env input.is_lw + Expression.eval env input.is_lwu +
          Expression.eval env input.is_ld = 1) :
    Expression.eval env input.adapter.op_a_0 = 1 := by
  have route : Expression.eval env
      (((input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
        input.is_lw + input.is_lwu + input.is_ld) *
          (input.adapter.op_a_0 - 1)) - 0) = 0 :=
    constraints.1 _ (loadX0RouteConstraint_mem input offset)
  rw [expression_eval_sub, expression_eval_mul, evalSelectorSum, real,
    expression_eval_sub] at route
  simp only [Expression.eval, one_mul, sub_zero] at route
  exact sub_eq_zero.mp route

end RouteProjection

end SP1Clean.Soundness
