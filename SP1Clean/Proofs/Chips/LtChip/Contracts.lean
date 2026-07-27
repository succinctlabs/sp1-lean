import SP1Clean.Proofs.Chips.LtChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # Lt — circuit-grounding contracts

Folded structural facts used by whole-machine grounding. Arithmetic meaning remains in
`LtChip.Spec`; this file projects only the retained reader, adapter/state passthrough, and the
chip-owned selector/routing constraints from the physical circuit.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private def LtChip.selectorVars (offset : ℕ) : Vector (Expression (ZMod p)) 2 :=
  Vector.mapRange 2 fun i => var { index := offset + i }

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private def LtChip.controlExpressions
    (input : Var LtChip.Inputs (ZMod p)) (offset : ℕ) : List (Expression (ZMod p)) :=
  let flags := LtChip.selectorVars (p := p) offset
  [ input.is_real - (flags[0] + flags[1]),
    flags[0] * (flags[0] - 1) - 0,
    flags[1] * (flags[1] - 1) - 0,
    input.adapter.op_a_0 - 0 ]

/-- Small folded carrier for Lt's four grounding-relevant control facts. -/
structure LtChip.ControlFacts (isReal isSlt isSltu opA0 : ZMod p) : Prop where
  selectorLink : isReal = isSlt + isSltu
  sltBinary : isSlt = 0 ∨ isSlt = 1
  sltuBinary : isSltu = 0 ∨ isSltu = 1
  opA0Zero : opA0 = 0

/-- The exact one-hot selector proposition consumed by Lt's `advanceReady`. -/
def LtChip.ActiveSelector (cols : Extracted.LtCols (ZMod p)) : Prop :=
  (cols.is_slt = 1 ∧ cols.is_sltu = 0) ∨ (cols.is_slt = 0 ∧ cols.is_sltu = 1)

set_option maxHeartbeats 4000000 in
private theorem LtChip.controlExpressions_subset_constraints
    (input : Var LtChip.Inputs (ZMod p)) (offset : ℕ) :
    ∀ e ∈ LtChip.controlExpressions (p := p) input offset,
      e ∈ ((LtChip.main input).operations offset).constraints := by
  intro e he
  simp only [LtChip.controlExpressions, LtChip.selectorVars, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · simp [LtChip.main, circuit_norm]
  · simp only [LtChip.main, circuit_norm]
    right; right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem
        (var { index := offset } * (var { index := offset } - 1))
        (0 : Expression (ZMod p)) _
  · simp only [LtChip.main, circuit_norm]
    right; right; right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem
        (var { index := offset + 1 } * (var { index := offset + 1 } - 1))
        (0 : Expression (ZMod p)) _
  · simp only [LtChip.main, circuit_norm]
    right; right; right; right; right; right; right; right; right
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 (0 : Expression (ZMod p)) _

/-- The physical Lt assertions identify the input selector with SP1's flag sum, make both flags
binary, and enforce the non-`x0` destination route. -/
theorem LtChip.controlFacts_of_mainConstraints
    (input : Var LtChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((LtChip.main input).operations offset).ConstraintsHold env) :
    LtChip.ControlFacts
      (Expression.eval env input.is_real)
      (Expression.eval env (var { index := offset }))
      (Expression.eval env (var { index := offset + 1 }))
      (Expression.eval env input.adapter.op_a_0) := by
  let flags := LtChip.selectorVars (p := p) offset
  have allConstraints := constraints.1
  have control (e : Expression (ZMod p))
      (he : e ∈ LtChip.controlExpressions (p := p) input offset) :
      Expression.eval env e = 0 :=
    allConstraints e (LtChip.controlExpressions_subset_constraints input offset e he)
  have link := control (input.is_real - (flags[0] + flags[1])) (by
    simp [LtChip.controlExpressions, flags])
  have g0 := control (flags[0] * (flags[0] - 1) - 0) (by
    simp [LtChip.controlExpressions, flags])
  have g1 := control (flags[1] * (flags[1] - 1) - 0) (by
    simp [LtChip.controlExpressions, flags])
  have route := control (input.adapter.op_a_0 - 0) (by
    simp [LtChip.controlExpressions])
  simp only [eval_sub, Expression.eval, sub_zero] at link g0 g1 route
  exact { selectorLink := sub_eq_zero.mp link
          sltBinary := bool_of_mul_pred g0
          sltuBinary := bool_of_mul_pred g1
          opA0Zero := route }

/-- A real physical Lt row has exactly one active opcode flag. -/
theorem LtChip.selectorActive_of_mainConstraints
    (input : Var LtChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((LtChip.main input).operations offset).ConstraintsHold env)
    (real : Expression.eval env input.is_real = 1) :
    (Expression.eval env (var { index := offset }) = 1 ∧
        Expression.eval env (var { index := offset + 1 }) = 0) ∨
      (Expression.eval env (var { index := offset }) = 0 ∧
        Expression.eval env (var { index := offset + 1 }) = 1) := by
  have control := LtChip.controlFacts_of_mainConstraints input offset env constraints
  have sumOne : Expression.eval env (var { index := offset }) +
      Expression.eval env (var { index := offset + 1 }) = 1 :=
    control.selectorLink.symm.trans real
  rcases control.sltuBinary with sltu0 | sltu1
  · exact Or.inl ⟨by simpa only [sltu0, add_zero] using sumOne, sltu0⟩
  · exact Or.inr ⟨by simpa only [sltu1, add_eq_right] using sumOne, sltu1⟩

/-- Lt passes its independent state input through to the completed row. -/
theorem LtChip.inputOutputState (env : Environment (ZMod p)) :
    ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state =
      ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).state := by
  let input : Var LtChip.Inputs (ZMod p) := varFromOffset LtChip.Inputs 0
  let offset := size LtChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset LtChip.Inputs 0 env
  have outputEq : Eval.eval env ((LtChip.circuit (p := p)).output input offset) =
      ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).state =
    (Eval.eval env ((LtChip.elaborated (p := p)).output input offset)).state
  rw [LtChip.directOutput_eq, LtChip.eval_inputs, LtChip.eval_columns]

/-- Lt passes its independent ALU adapter input through to the completed row. -/
theorem LtChip.inputOutputAdapter (env : Environment (ZMod p)) :
    ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  let input : Var LtChip.Inputs (ZMod p) := varFromOffset LtChip.Inputs 0
  let offset := size LtChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset LtChip.Inputs 0 env
  have outputEq : Eval.eval env ((LtChip.circuit (p := p)).output input offset) =
      ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).adapter =
    (Eval.eval env ((LtChip.elaborated (p := p)).output input offset)).adapter
  rw [LtChip.directOutput_eq, LtChip.eval_inputs, LtChip.eval_columns]

/-- The completed Lt columns at one physical component row. -/
noncomputable def LtChip.physicalCols (env : Environment (ZMod p)) :
    Extracted.LtCols (ZMod p) :=
  (⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env

/-- The completed Lt row view at one physical component row. -/
noncomputable def LtChip.physicalView (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  LtChip.rowView
    ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    (LtChip.physicalCols env)

/-- The folded physical view's selector is exactly the evaluated typed input selector. -/
theorem LtChip.physicalView_isReal (env : Environment (ZMod p)) :
    (LtChip.physicalView env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) LtChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset LtChip.Inputs 0) =
      (⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset LtChip.Inputs 0 env
  simpa only [LtChip.physicalView, LtChip.rowView] using
    congrArg (fun input : LtChip.Inputs (ZMod p) => input.is_real) inputEq.symm

/-- Component-level form of Lt's physical non-`x0` route. -/
theorem LtChip.rowViewOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    (LtChip.physicalView env).adapter.op_a_0 = 0 := by
  let input : Var LtChip.Inputs (ZMod p) := varFromOffset LtChip.Inputs 0
  let offset := size LtChip.Inputs
  have mainConstraints : ((LtChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have route := (LtChip.controlFacts_of_mainConstraints input offset env mainConstraints).opA0Zero
  have inputEq : Eval.eval env input =
      (⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset LtChip.Inputs 0 env
  change ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_a_0 = 0
  rw [← LtChip.inputOutputAdapter env, ← inputEq, LtChip.eval_inputAdapter,
    Readers.ALUTypeReader.eval_opA0]
  exact route

/-- Component-level exact opcode partition used by `advanceReady`. -/
theorem LtChip.rowViewSelectorActive_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (real : (LtChip.physicalView env).is_real = 1) :
    LtChip.ActiveSelector (LtChip.physicalCols env) := by
  let input : Var LtChip.Inputs (ZMod p) := varFromOffset LtChip.Inputs 0
  let offset := size LtChip.Inputs
  have mainConstraints : ((LtChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have realInput : Expression.eval env input.is_real = 1 := by
    have realValue : (Eval.eval env input).is_real = 1 :=
      (LtChip.physicalView_isReal env).symm.trans real
    exact (LtChip.eval_inputIsReal env input).symm.trans realValue
  have active := LtChip.selectorActive_of_mainConstraints input offset env mainConstraints realInput
  have outputEq : Eval.eval env ((LtChip.circuit (p := p)).output input offset) =
      LtChip.physicalCols env := by
    simp only [input, offset, LtChip.physicalCols, Component.rowOutput, circuit_norm]
  rw [LtChip.ActiveSelector, ← outputEq]
  change LtChip.ActiveSelector (Eval.eval env ((LtChip.elaborated (p := p)).output input offset))
  rw [LtChip.ActiveSelector, LtChip.directOutput_eq, LtChip.eval_columns]
  simpa only [offset, circuit_norm] using active

/-- The exact ALU reader input retained after Lt's 12 local witness cells. -/
def LtChip.aluTypeReaderInput (input : Var LtChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    var ⟨offset⟩ * 9 + var ⟨offset + 1⟩ * 10,
    var ⟨offset + 2⟩, 0, 0, 0⟩

theorem LtChip.aluTypeReader_mem (input : Var LtChip.Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 12, Readers.ALUTypeReader.circuit.toSubcircuit (offset + 12)
      (LtChip.aluTypeReaderInput input offset)⟩ ∈
      ((LtChip.main input).operations offset).subcircuits := by
  simp only [LtChip.main, LtChip.aluTypeReaderInput,
    Readers.ALUTypeReader.circuit, circuit_norm]

/-- The retained ALU reader binds source C to the decoded immediate on immediate rows. -/
theorem LtChip.rowViewOpCBinding_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (immediate : (LtChip.physicalView env).adapter.imm_c = 1) :
    (LtChip.physicalView env).adapter.op_c_memory.prev_value =
      (LtChip.physicalView env).adapter.op_c := by
  let input : Var LtChip.Inputs (ZMod p) := varFromOffset LtChip.Inputs 0
  let offset := size LtChip.Inputs
  let readerInput := LtChip.aluTypeReaderInput input offset
  have mainConstraints : ((LtChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have readerConstraints := constraintsHold_generalSubcircuit_of_mem env
    ((LtChip.main input).operations offset) Readers.ALUTypeReader.circuit readerInput
    (offset + 12) (LtChip.aluTypeReader_mem input offset) mainConstraints
  have inputEq : Eval.eval env input =
      (⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset LtChip.Inputs 0 env
  have immediateInput : Expression.eval env readerInput.cols.imm_c = 1 := by
    change Expression.eval env input.adapter.imm_c = 1
    change ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.imm_c = 1
      at immediate
    rw [← LtChip.inputOutputAdapter env, ← inputEq, LtChip.eval_inputs,
      Readers.ALUTypeReader.eval_immC] at immediate
    exact immediate
  have binding := Readers.ALUTypeReader.eval_opCPrev_eq_opC_of_mainConstraints
    readerInput (offset + 12) env readerConstraints immediateInput
  change ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_c_memory.prev_value =
    ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_c
  rw [← LtChip.inputOutputAdapter env, ← inputEq, LtChip.eval_inputs,
    Readers.ALUTypeReader.eval_opCPrev, Readers.ALUTypeReader.eval_opC]
  simpa only [readerInput, LtChip.aluTypeReaderInput] using binding

end SP1Clean.Soundness
