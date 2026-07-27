import SP1Clean.Proofs.Chips.AddwChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # Addw — circuit-grounding contracts

Small folded facts exposing Addw's state/adapter passthrough and its physical non-`x0` routing
assertion.  These are structural circuit facts; arithmetic meaning remains in `AddwChip.Spec`.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

/-- The folded `main` assertion system contains Addw's `op_a_0 = 0` routing constraint. -/
theorem AddwChip.eval_inputOpA0_eq_zero_of_mainConstraints
    (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env ((AddwChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 := by
  have flagConstraint : Expression.eval env (input.adapter.op_a_0 - 0) = 0 := by
    apply constraints.1
    simp only [AddwChip.main, circuit_norm]
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

/-- Addw passes its independent state input through to the completed row. -/
theorem AddwChip.inputOutputState (env : Environment (ZMod p)) :
    ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state =
      ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).state := by
  let input : Var AddwChip.Inputs (ZMod p) := varFromOffset AddwChip.Inputs 0
  let offset := size AddwChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset AddwChip.Inputs 0 env
  have outputEq : Eval.eval env ((AddwChip.circuit (p := p)).output input offset) =
      ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).state =
    (Eval.eval env ((AddwChip.elaborated (p := p)).output input offset)).state
  rw [AddwChip.directOutput_eq, AddwChip.eval_inputs, AddwChip.eval_columns]

/-- Addw passes its independent ALU adapter input through to the completed row. -/
theorem AddwChip.inputOutputAdapter (env : Environment (ZMod p)) :
    ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  let input : Var AddwChip.Inputs (ZMod p) := varFromOffset AddwChip.Inputs 0
  let offset := size AddwChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset AddwChip.Inputs 0 env
  have outputEq : Eval.eval env ((AddwChip.circuit (p := p)).output input offset) =
      ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).adapter =
    (Eval.eval env ((AddwChip.elaborated (p := p)).output input offset)).adapter
  rw [AddwChip.directOutput_eq, AddwChip.eval_inputs, AddwChip.eval_columns]

/-- The exact ALU reader input retained after Addw's three local result-witness cells. -/
def AddwChip.aluTypeReaderInput (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  let value : Vector (Expression (ZMod p)) 2 :=
    Vector.mapRange 2 fun i => var { index := offset + i }
  let msb : Expression (ZMod p) := var { index := offset + 2 }
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 19,
    value[0], value[1], msb * 65535, msb * 65535⟩

/-- Addw retains its ALU reader as the third semantic subcircuit, at the end of the three-cell
witness prefix. -/
theorem AddwChip.aluTypeReader_mem (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 3,
      Readers.ALUTypeReader.circuit.toSubcircuit (offset + 3)
        (AddwChip.aluTypeReaderInput input offset)⟩ ∈
      ((AddwChip.main input).operations offset).subcircuits := by
  simp only [AddwChip.main, AddwChip.aluTypeReaderInput,
    Readers.ALUTypeReader.circuit, circuit_norm]

/-- Addw's physical reader constraints bind source C to the decoded immediate on the immediate
form.  This is an `advanceReady` fact, independent of the chip arithmetic `Spec`. -/
theorem AddwChip.rowViewOpCBinding_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (immediate :
      (AddwChip.rowView
        ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
        ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)).adapter.imm_c = 1) :
    (AddwChip.rowView
        ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
        ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)).adapter.op_c_memory.prev_value =
      (AddwChip.rowView
        ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
        ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)).adapter.op_c := by
  let input : Var AddwChip.Inputs (ZMod p) := varFromOffset AddwChip.Inputs 0
  let offset := size AddwChip.Inputs
  let readerInput := AddwChip.aluTypeReaderInput input offset
  have mainConstraints : ((AddwChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have readerConstraints := constraintsHold_generalSubcircuit_of_mem env
    ((AddwChip.main input).operations offset) Readers.ALUTypeReader.circuit readerInput
    (offset + 3) (AddwChip.aluTypeReader_mem input offset) mainConstraints
  have inputEq : Eval.eval env input =
      (⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset AddwChip.Inputs 0 env
  have immediateInput : Expression.eval env readerInput.cols.imm_c = 1 := by
    change Expression.eval env input.adapter.imm_c = 1
    change ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.imm_c = 1
      at immediate
    rw [← AddwChip.inputOutputAdapter env, ← inputEq, AddwChip.eval_inputs,
      Readers.ALUTypeReader.eval_immC] at immediate
    exact immediate
  have binding := Readers.ALUTypeReader.eval_opCPrev_eq_opC_of_mainConstraints
    readerInput (offset + 3) env readerConstraints immediateInput
  change ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_c_memory.prev_value =
    ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_c
  rw [← AddwChip.inputOutputAdapter env, ← inputEq, AddwChip.eval_inputs,
    Readers.ALUTypeReader.eval_opCPrev, Readers.ALUTypeReader.eval_opC]
  simpa only [readerInput, AddwChip.aluTypeReaderInput] using binding

end SP1Clean.Soundness
