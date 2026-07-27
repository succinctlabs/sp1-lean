import SP1Clean.Proofs.Chips.BitwiseChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # Bitwise — circuit-grounding contracts

Folded structural facts used by whole-machine grounding.  Arithmetic meaning remains in
`BitwiseChip.Spec`; this file only projects the retained reader, adapter/state passthrough, and the
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
private def BitwiseChip.selectorVars (offset : ℕ) : Vector (Expression (ZMod p)) 3 :=
  Vector.mapRange 3 fun i => var { index := offset + i }

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private def BitwiseChip.controlExpressions
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) : List (Expression (ZMod p)) :=
  let flags := BitwiseChip.selectorVars (p := p) offset
  [ input.is_real - (flags[0] + flags[1] + flags[2]),
    flags[0] * (flags[0] - 1) - 0,
    flags[1] * (flags[1] - 1) - 0,
    flags[2] * (flags[2] - 1) - 0,
    input.adapter.op_a_0 - 0 ]

/-- Small folded carrier for Bitwise's five grounding-relevant control facts. -/
structure BitwiseChip.ControlFacts
    (isReal isXor isOr isAnd opA0 : ZMod p) : Prop where
  selectorLink : isReal = isXor + isOr + isAnd
  xorBinary : isXor = 0 ∨ isXor = 1
  orBinary : isOr = 0 ∨ isOr = 1
  andBinary : isAnd = 0 ∨ isAnd = 1
  opA0Zero : opA0 = 0

/-- The active-selector proposition consumed by Bitwise's `advanceReady`. -/
def BitwiseChip.ActiveSelector (cols : Extracted.BitwiseCols (ZMod p)) : Prop :=
  cols.is_and = 1 ∨ cols.is_or = 1 ∨ cols.is_xor = 1

set_option maxHeartbeats 4000000 in
private theorem BitwiseChip.controlExpressions_subset_constraints
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) :
    ∀ e ∈ BitwiseChip.controlExpressions (p := p) input offset,
      e ∈ ((BitwiseChip.main input).operations offset).constraints := by
  intro e he
  simp only [BitwiseChip.controlExpressions, BitwiseChip.selectorVars, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · simp [BitwiseChip.main, circuit_norm]
  · simp only [BitwiseChip.main, circuit_norm]
    right; right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem
        (var { index := offset } * (var { index := offset } - 1))
        (0 : Expression (ZMod p)) _
  · simp only [BitwiseChip.main, circuit_norm]
    right; right; right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem
        (var { index := offset + 1 } * (var { index := offset + 1 } - 1))
        (0 : Expression (ZMod p)) _
  · simp only [BitwiseChip.main, circuit_norm]
    right; right; right; right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem
        (var { index := offset + 2 } * (var { index := offset + 2 } - 1))
        (0 : Expression (ZMod p)) _
  · simp only [BitwiseChip.main, circuit_norm]
    right; right; right; right; right; right; right; right; right; right
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 (0 : Expression (ZMod p)) _

/-- The physical Bitwise assertions identify the explicit input selector with SP1's flag sum,
make each flag binary, and enforce the non-`x0` destination route. -/
theorem BitwiseChip.controlFacts_of_mainConstraints
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env) :
    BitwiseChip.ControlFacts
      (Expression.eval env input.is_real)
      (Expression.eval env (var { index := offset }))
      (Expression.eval env (var { index := offset + 1 }))
      (Expression.eval env (var { index := offset + 2 }))
      (Expression.eval env input.adapter.op_a_0) := by
  let flags := BitwiseChip.selectorVars (p := p) offset
  have allConstraints := constraints.1
  have control (e : Expression (ZMod p))
      (he : e ∈ BitwiseChip.controlExpressions (p := p) input offset) :
      Expression.eval env e = 0 :=
    allConstraints e (BitwiseChip.controlExpressions_subset_constraints input offset e he)
  have link := control (input.is_real - (flags[0] + flags[1] + flags[2])) (by
    simp [BitwiseChip.controlExpressions, flags])
  have g0 := control (flags[0] * (flags[0] - 1) - 0) (by
    simp [BitwiseChip.controlExpressions, flags])
  have g1 := control (flags[1] * (flags[1] - 1) - 0) (by
    simp [BitwiseChip.controlExpressions, flags])
  have g2 := control (flags[2] * (flags[2] - 1) - 0) (by
    simp [BitwiseChip.controlExpressions, flags])
  have route := control (input.adapter.op_a_0 - 0) (by
    simp [BitwiseChip.controlExpressions])
  simp only [eval_sub, Expression.eval, sub_zero] at link g0 g1 g2 route
  exact { selectorLink := sub_eq_zero.mp link
          xorBinary := bool_of_mul_pred g0
          orBinary := bool_of_mul_pred g1
          andBinary := bool_of_mul_pred g2
          opA0Zero := route }

/-- A real physical Bitwise row has at least one active opcode flag. The mutual-exclusion part is
already a proved conjunct of `BitwiseChip.Spec`; grounding only needs this existence half. -/
theorem BitwiseChip.selectorActive_of_mainConstraints
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env)
    (real : Expression.eval env input.is_real = 1) :
    Expression.eval env (var { index := offset + 2 }) = 1 ∨
      Expression.eval env (var { index := offset + 1 }) = 1 ∨
      Expression.eval env (var { index := offset }) = 1 := by
  have control := BitwiseChip.controlFacts_of_mainConstraints input offset env constraints
  have sumOne : Expression.eval env (var { index := offset }) +
      Expression.eval env (var { index := offset + 1 }) +
        Expression.eval env (var { index := offset + 2 }) = 1 :=
    control.selectorLink.symm.trans real
  rcases control.andBinary with and0 | and1
  · rcases control.orBinary with or0 | or1
    · rcases control.xorBinary with xor0 | xor1
      · exfalso
        rw [xor0, or0, and0] at sumOne
        simp at sumOne
      · exact Or.inr (Or.inr xor1)
    · exact Or.inr (Or.inl or1)
  · exact Or.inl and1

/-- Bitwise passes its independent state input through to the completed row. -/
theorem BitwiseChip.inputOutputState (env : Environment (ZMod p)) :
    ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state =
      ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).state := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset BitwiseChip.Inputs 0 env
  have outputEq : Eval.eval env ((BitwiseChip.circuit (p := p)).output input offset) =
      ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).state =
    (Eval.eval env ((BitwiseChip.elaborated (p := p)).output input offset)).state
  rw [BitwiseChip.directOutput_eq, BitwiseChip.eval_inputs, BitwiseChip.eval_columns]

/-- Bitwise passes its independent ALU adapter input through to the completed row. -/
theorem BitwiseChip.inputOutputAdapter (env : Environment (ZMod p)) :
    ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset BitwiseChip.Inputs 0 env
  have outputEq : Eval.eval env ((BitwiseChip.circuit (p := p)).output input offset) =
      ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).adapter =
    (Eval.eval env ((BitwiseChip.elaborated (p := p)).output input offset)).adapter
  rw [BitwiseChip.directOutput_eq, BitwiseChip.eval_inputs, BitwiseChip.eval_columns]

/-- The completed Bitwise view at one physical component row. Keeping this projection folded avoids
normalizing the full witnessed arithmetic row in every structural theorem statement. -/
noncomputable def BitwiseChip.physicalCols (env : Environment (ZMod p)) :
    Extracted.BitwiseCols (ZMod p) :=
  (⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env

/-- The completed Bitwise view at one physical component row. -/
noncomputable def BitwiseChip.physicalView (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  BitwiseChip.rowView
    ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    (BitwiseChip.physicalCols env)

/-- The folded physical view's selector is exactly the evaluated typed input selector. -/
theorem BitwiseChip.physicalView_isReal (env : Environment (ZMod p)) :
    (BitwiseChip.physicalView env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) BitwiseChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset BitwiseChip.Inputs 0) =
      (⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset BitwiseChip.Inputs 0 env
  simpa only [BitwiseChip.physicalView, BitwiseChip.rowView] using
    congrArg (fun input : BitwiseChip.Inputs (ZMod p) => input.is_real) inputEq.symm

/-- Component-level form of Bitwise's physical non-`x0` route. -/
theorem BitwiseChip.rowViewOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    (BitwiseChip.physicalView env).adapter.op_a_0 = 0 := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  have mainConstraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have route :=
    (BitwiseChip.controlFacts_of_mainConstraints input offset env mainConstraints).opA0Zero
  have inputEq : Eval.eval env input =
      (⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset BitwiseChip.Inputs 0 env
  change ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_a_0 = 0
  rw [← BitwiseChip.inputOutputAdapter env, ← inputEq, BitwiseChip.eval_inputAdapter,
    Readers.ALUTypeReader.eval_opA0]
  exact route

/-- Component-level active opcode partition used by `advanceReady`. -/
theorem BitwiseChip.rowViewSelectorActive_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (real : (BitwiseChip.physicalView env).is_real = 1) :
    BitwiseChip.ActiveSelector (BitwiseChip.physicalCols env) := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  have mainConstraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have realInput : Expression.eval env input.is_real = 1 := by
    have realValue : (Eval.eval env input).is_real = 1 :=
      (BitwiseChip.physicalView_isReal env).symm.trans real
    exact (BitwiseChip.eval_inputIsReal env input).symm.trans realValue
  have active := BitwiseChip.selectorActive_of_mainConstraints input offset env mainConstraints realInput
  have outputEq : Eval.eval env ((BitwiseChip.circuit (p := p)).output input offset) =
      BitwiseChip.physicalCols env := by
    simp only [input, offset, BitwiseChip.physicalCols, Component.rowOutput, circuit_norm]
  rw [BitwiseChip.ActiveSelector, ← outputEq]
  change BitwiseChip.ActiveSelector
    (Eval.eval env ((BitwiseChip.elaborated (p := p)).output input offset))
  rw [BitwiseChip.ActiveSelector, BitwiseChip.directOutput_eq, BitwiseChip.eval_columns]
  simpa only [offset, circuit_norm] using active

/-- The exact ALU reader input retained after Bitwise's 19 local witness cells. -/
def BitwiseChip.aluTypeReaderInput (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    var ⟨offset⟩ * 3 + var ⟨offset + 1⟩ * 4 + var ⟨offset + 2⟩ * 5,
    var ⟨offset + 11⟩ + var ⟨offset + 12⟩ * 256,
    var ⟨offset + 13⟩ + var ⟨offset + 14⟩ * 256,
    var ⟨offset + 15⟩ + var ⟨offset + 16⟩ * 256,
    var ⟨offset + 17⟩ + var ⟨offset + 18⟩ * 256⟩

theorem BitwiseChip.aluTypeReader_mem (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 19, Readers.ALUTypeReader.circuit.toSubcircuit (offset + 19)
      (BitwiseChip.aluTypeReaderInput input offset)⟩ ∈
      ((BitwiseChip.main input).operations offset).subcircuits := by
  simp only [BitwiseChip.main, BitwiseChip.aluTypeReaderInput,
    Readers.ALUTypeReader.circuit, circuit_norm]

/-- The retained ALU reader binds source C to the decoded immediate on immediate rows. -/
theorem BitwiseChip.rowViewOpCBinding_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (immediate : (BitwiseChip.physicalView env).adapter.imm_c = 1) :
    (BitwiseChip.physicalView env).adapter.op_c_memory.prev_value =
      (BitwiseChip.physicalView env).adapter.op_c := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  let readerInput := BitwiseChip.aluTypeReaderInput input offset
  have mainConstraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have readerConstraints := constraintsHold_generalSubcircuit_of_mem env
    ((BitwiseChip.main input).operations offset) Readers.ALUTypeReader.circuit readerInput
    (offset + 19) (BitwiseChip.aluTypeReader_mem input offset) mainConstraints
  have inputEq : Eval.eval env input =
      (⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset BitwiseChip.Inputs 0 env
  have immediateInput : Expression.eval env readerInput.cols.imm_c = 1 := by
    change Expression.eval env input.adapter.imm_c = 1
    change ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.imm_c = 1
      at immediate
    rw [← BitwiseChip.inputOutputAdapter env, ← inputEq, BitwiseChip.eval_inputs,
      Readers.ALUTypeReader.eval_immC] at immediate
    exact immediate
  have binding := Readers.ALUTypeReader.eval_opCPrev_eq_opC_of_mainConstraints
    readerInput (offset + 19) env readerConstraints immediateInput
  change ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_c_memory.prev_value =
    ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_c
  rw [← BitwiseChip.inputOutputAdapter env, ← inputEq, BitwiseChip.eval_inputs,
    Readers.ALUTypeReader.eval_opCPrev, Readers.ALUTypeReader.eval_opC]
  simpa only [readerInput, BitwiseChip.aluTypeReaderInput] using binding

end SP1Clean.Soundness
