import SP1Clean.Proofs.Chips.AddiChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # Addi — circuit-grounding contracts

Small structural facts crossing Addi's completed Clean circuit boundary.  Arithmetic meaning stays
in `AddiChip.Spec`; these lemmas expose only state/adapter passthrough and the physical non-`x0`
routing assertion used by whole-machine grounding.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

/-- The folded `main` constraint list contains Addi's `op_a_0 = 0` routing assertion. -/
theorem AddiChip.eval_inputOpA0_eq_zero_of_mainConstraints
    (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env ((AddiChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 := by
  have flagConstraint : Expression.eval env (input.adapter.op_a_0 - 0) = 0 := by
    apply constraints.1
    simp only [AddiChip.main, circuit_norm]
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

/-- Addi passes its independent state input through to the completed row. -/
theorem AddiChip.inputOutputState (env : Environment (ZMod p)) :
    ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state =
      ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).state := by
  let input : Var AddiChip.Inputs (ZMod p) := varFromOffset AddiChip.Inputs 0
  let offset := size AddiChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset AddiChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((AddiChip.circuit (p := p)).output input offset) =
      ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).state =
    (Eval.eval env ((AddiChip.elaborated (p := p)).output input offset)).state
  rw [AddiChip.directOutput_eq, AddiChip.eval_inputs, AddiChip.eval_columns]

/-- Addi passes its independent I-type adapter input through to the completed row. -/
theorem AddiChip.inputOutputAdapter (env : Environment (ZMod p)) :
    ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  let input : Var AddiChip.Inputs (ZMod p) := varFromOffset AddiChip.Inputs 0
  let offset := size AddiChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset AddiChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((AddiChip.circuit (p := p)).output input offset) =
      ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).adapter =
    (Eval.eval env ((AddiChip.elaborated (p := p)).output input offset)).adapter
  rw [AddiChip.directOutput_eq, AddiChip.eval_inputs, AddiChip.eval_columns]

end SP1Clean.Soundness
