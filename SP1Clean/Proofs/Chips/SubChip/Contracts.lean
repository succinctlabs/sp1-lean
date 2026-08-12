import SP1Clean.Proofs.Chips.SubChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # Sub — circuit-grounding contracts

Small structural facts that cross Sub's completed Clean circuit boundary.  Arithmetic meaning stays
in `SubChip.Spec`; these lemmas expose only the input/output adapter passthrough and the physical
non-`x0` routing assertion used by the whole-machine grounding layer.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

/-- Project Sub's routing assertion while its circuit input remains opaque. -/
private theorem subInputOpA0_eq_zero_of_mainConstraints
    (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env ((SubChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 := by
  have flagConstraint : Expression.eval env (input.adapter.op_a_0 - 0) = 0 := by
    apply constraints.1
    simp only [SubChip.main, circuit_norm]
    right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 0 _
  rw [eval_sub] at flagConstraint
  simpa only [Expression.eval] using sub_eq_zero.mp flagConstraint

/-- The native Sub circuit passes its independent R-type adapter input through to its output. -/
theorem SubChip.inputOutputAdapter (env : Environment (ZMod p)) :
    ((⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  have inputEq : Eval.eval env (varFromOffset SubChip.Inputs 0) =
      ((⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset SubChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((SubChip.circuit (p := p)).output (varFromOffset SubChip.Inputs 0)
        (size SubChip.Inputs)) =
      ((⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  simp only [SubChip.circuit, circuit_norm]

/-- Sub's complete physical assertion system forces the canonical zero-register indicator onto its
non-`x0` routing branch. -/
theorem SubChip.inputOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints : (⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    ((⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter.op_a_0 = 0 := by
  let input : Var SubChip.Inputs (ZMod p) := varFromOffset SubChip.Inputs 0
  let offset := size SubChip.Inputs
  have rowConstraints : Operations.ConstraintsHold env ((SubChip.main input).operations offset) :=
    (Component.constraintsHold_iff env).mp constraints
  have flagConstraint := subInputOpA0_eq_zero_of_mainConstraints input offset env rowConstraints
  have inputEq : Eval.eval env input =
      (⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset SubChip.Inputs 0 env
  rw [← inputEq, SubChip.eval_inputs, Readers.RTypeReader.eval_opA0]
  exact flagConstraint

/-- Row-view form of Sub's physical routing constraint. -/
theorem SubChip.rowViewOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints : (⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    (SubChip.rowView
      ((⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
      ((⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)).adapter.op_a_0 = 0 := by
  change ((⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_a_0 = 0
  rw [← SubChip.inputOutputAdapter env]
  exact SubChip.inputOpA0_eq_zero_of_constraints env constraints

end SP1Clean.Soundness
