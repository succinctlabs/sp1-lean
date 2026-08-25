import SP1Clean.Proofs.Chips.MulChip.Bridge
import SP1Clean.Proofs.Chips.MulChip.Structural
import SP1Clean.Soundness.TypedMemory

/-! # MUL — circuit-grounding contracts

Small structural facts crossing the completed MUL circuit boundary.  They expose adapter
passthrough and the chip-owned selector/routing constraints; multiplication arithmetic remains in
`MulChip.Spec` and its Sail bridge. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The five selector cells at the folded `main` boundary. -/
private def selectorVars (offset : ℕ) : Vector (Expression (ZMod p)) 5 :=
  Vector.mapRange 5 fun i => var { index := offset + i }

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Precisely the seven chip-owned control assertions needed by grounding.  The multiplication
result ties, sum-boolean gate, and final row gate remain outside this deliberately narrow list. -/
private def controlExpressions (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ) :
    List (Expression (ZMod p)) :=
  let flags := selectorVars (p := p) offset
  [ flags[0] * (flags[0] - 1), flags[1] * (flags[1] - 1),
    flags[2] * (flags[2] - 1), flags[3] * (flags[3] - 1),
    flags[4] * (flags[4] - 1), input.adapter.op_a_0,
    input.is_real - (flags[0] + flags[1] + flags[2] + flags[3] + flags[4]) ]

/-- Each grounding control expression is a top-level assertion of the physical MUL circuit.  This
membership statement is the only place the sequential `main` syntax is normalized. -/
private theorem controlExpressions_subset_shallowConstraints
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ) :
    ∀ e ∈ controlExpressions (p := p) input offset,
      e ∈ ((MulChip.main input).operations offset).shallowConstraints := by
  intro e he
  simp only [controlExpressions, selectorVars, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [MulChip.main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorIR, Witnessable.witness, witnessIR,
      subcircuitWithAssertion, assertion, assertZero,
      Operations.localLength, Operations.shallowConstraints, List.mem_cons, List.not_mem_nil,
      or_false, circuit_norm]

/-- The physical constraints of `MulChip.main`, kept at the folded typed-input boundary, imply its
five selector booleans, selector-sum link, and `op_a_0 = 0` routing assertion. -/
private theorem controlFacts_of_mainConstraints
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (shallow : ConstraintsHold.Shallow env ((MulChip.main input).operations offset)) :
    let flags := selectorVars (p := p) offset
    (Expression.eval env flags[0] = 0 ∨ Expression.eval env flags[0] = 1) ∧
    (Expression.eval env flags[1] = 0 ∨ Expression.eval env flags[1] = 1) ∧
    (Expression.eval env flags[2] = 0 ∨ Expression.eval env flags[2] = 1) ∧
    (Expression.eval env flags[3] = 0 ∨ Expression.eval env flags[3] = 1) ∧
    (Expression.eval env flags[4] = 0 ∨ Expression.eval env flags[4] = 1) ∧
    Expression.eval env input.is_real =
      Expression.eval env flags[0] + Expression.eval env flags[1] +
        Expression.eval env flags[2] + Expression.eval env flags[3] +
          Expression.eval env flags[4] ∧
    Expression.eval env input.adapter.op_a_0 = 0 := by
  let flags := selectorVars (p := p) offset
  have allConstraints := (constraintsHold_shallow_iff_forall_mem.mp shallow).1
  have controlConstraint (e : Expression (ZMod p))
      (he : e ∈ controlExpressions (p := p) input offset) : Expression.eval env e = 0 :=
    allConstraints e (controlExpressions_subset_shallowConstraints input offset e he)
  have g0 := controlConstraint (flags[0] * (flags[0] - 1)) (by
    simp [controlExpressions, flags])
  have g1 := controlConstraint (flags[1] * (flags[1] - 1)) (by
    simp [controlExpressions, flags])
  have g2 := controlConstraint (flags[2] * (flags[2] - 1)) (by
    simp [controlExpressions, flags])
  have g3 := controlConstraint (flags[3] * (flags[3] - 1)) (by
    simp [controlExpressions, flags])
  have g4 := controlConstraint (flags[4] * (flags[4] - 1)) (by
    simp [controlExpressions, flags])
  have hopa0 := controlConstraint input.adapter.op_a_0 (by
    simp [controlExpressions])
  have hlink := controlConstraint
    (input.is_real - (flags[0] + flags[1] + flags[2] + flags[3] + flags[4])) (by
      simp [controlExpressions, flags])
  simp only [eval_sub, Expression.eval] at g0 g1 g2 g3 g4 hopa0 hlink
  refine ⟨bool_of_mul_pred g0, bool_of_mul_pred g1, bool_of_mul_pred g2,
    bool_of_mul_pred g3, bool_of_mul_pred g4, ?_, hopa0⟩
  exact sub_eq_zero.mp hlink

/-- MUL's output layout passes the independent R-type adapter through unchanged.  This stays at the
typed circuit boundary; generic component transport is performed only by the grounding consumer. -/
theorem MulChip.eval_output_adapter (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) :
    (Eval.eval env input).adapter =
      (Eval.eval env ((MulChip.circuit (p := p)).output input offset)).adapter := by
  change (Eval.eval env input).adapter =
    (Eval.eval env ((MulChip.elaborated (p := p)).output input offset)).adapter
  rw [MulChip.directOutput_eq, ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval]
  rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Evaluation of MUL's input selector, exposed without decomposing the reader blocks. -/
theorem MulChip.eval_isReal {F : Type} [FiniteField F] (env : Environment F)
    (input : MulChip.Inputs (Expression F)) :
    (Eval.eval env input).is_real = Expression.eval env input.is_real := by
  simpa only [CircuitType.eval_expr] using
    congrArg (fun value : MulChip.Inputs F => value.is_real) (MulChip.eval_inputs env input)

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Evaluation commutes with the small selector projection.  The source row remains abstract, so
this generic transport never normalizes MUL's arithmetic columns. -/
theorem MulChip.eval_selectors {F : Type} [FiniteField F] (env : Environment F)
    (cols : MulChip.Columns (Expression F)) :
    Eval.eval env (MulChip.selectors cols) = MulChip.selectors (Eval.eval env cols) := by
  rw [ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval]
  rfl

/-- The physical `op_a_0 = 0` route, projected without unfolding the completed circuit record. -/
theorem MulChip.eval_opA0_eq_zero_of_shallowConstraints
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (shallow : ConstraintsHold.Shallow env ((MulChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 :=
  (controlFacts_of_mainConstraints input offset env shallow).2.2.2.2.2.2

/-- On an active typed MUL row, the physical control assertions resolve to the exact five-way
dispatch consumed by `advanceReady`. -/
theorem MulChip.selectorOneHot_of_shallowConstraints
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (shallow : ConstraintsHold.Shallow env ((MulChip.main input).operations offset))
    (real : Expression.eval env input.is_real = 1) :
    MulChip.SelectorOneHot
      (Eval.eval env (MulChip.selectors
        ((MulChip.circuit (p := p)).output input offset))) := by
  change MulChip.SelectorOneHot
    (Eval.eval env (MulChip.selectors
      ((MulChip.elaborated (p := p)).output input offset)))
  have control := controlFacts_of_mainConstraints input offset env shallow
  have sumOne := control.2.2.2.2.2.1.symm.trans real
  have oneHot := MulOperation.oneHot_of_sum_one control.1 control.2.1 control.2.2.1
    control.2.2.2.1 control.2.2.2.2.1 sumOne
  rw [MulChip.directOutput_eq]
  simpa only [MulChip.selectors, MulChip.SelectorOneHot, selectorVars, circuit_norm] using oneHot

end SP1Clean.Soundness
