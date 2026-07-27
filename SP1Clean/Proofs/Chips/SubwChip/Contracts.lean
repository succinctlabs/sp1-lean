import SP1Clean.Proofs.Chips.SubwChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # Subw — circuit-grounding contracts

Structural facts crossing the completed SUBW circuit boundary: adapter passthrough and the physical
non-`x0` routing assertion.  Arithmetic meaning remains in `SubwChip.Spec`.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

/-- Project SUBW's `op_a_0 = 0` assertion while its circuit input remains folded. -/
private theorem subwInputOpA0_eq_zero_of_mainConstraints
    (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env ((SubwChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 := by
  have flagConstraint : Expression.eval env (input.adapter.op_a_0 - 0) = 0 := by
    apply constraints.1
    simp only [SubwChip.main, circuit_norm]
    right
    right
    right
    right
    left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 0 _
  rw [eval_sub] at flagConstraint
  have flagEq := sub_eq_zero.mp flagConstraint
  simpa only [Expression.eval] using flagEq

/-- SUBW passes its independent R-type adapter input through to the committed output row. -/
theorem SubwChip.inputOutputAdapter (env : Environment (ZMod p)) :
    ((⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  have inputEq : Eval.eval env (varFromOffset SubwChip.Inputs 0) =
      ((⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset SubwChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((SubwChip.circuit (p := p)).output (varFromOffset SubwChip.Inputs 0)
        (size SubwChip.Inputs)) =
      ((⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  simp only [SubwChip.circuit, circuit_norm]

/-- SUBW's complete physical assertions force the canonical zero-register indicator onto the
non-`x0` routing branch. -/
theorem SubwChip.inputOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    ((⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter.op_a_0 = 0 := by
  let input : Var SubwChip.Inputs (ZMod p) := varFromOffset SubwChip.Inputs 0
  let offset := size SubwChip.Inputs
  have rowConstraints : Operations.ConstraintsHold env ((SubwChip.main input).operations offset) :=
    (Component.constraintsHold_iff env).mp constraints
  have flagConstraint :=
    subwInputOpA0_eq_zero_of_mainConstraints input offset env rowConstraints
  have inputEq : Eval.eval env input =
      (⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset SubwChip.Inputs 0 env
  rw [← inputEq, SubwChip.eval_inputs, Readers.RTypeReader.eval_opA0]
  exact flagConstraint

/-- Row-view form of SUBW's physical routing constraint. -/
theorem SubwChip.rowViewOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    (SubwChip.rowView
      ((⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
      ((⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)).adapter.op_a_0 = 0 := by
  change ((⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_a_0 = 0
  rw [← SubwChip.inputOutputAdapter env]
  exact SubwChip.inputOpA0_eq_zero_of_constraints env constraints

end SP1Clean.Soundness
