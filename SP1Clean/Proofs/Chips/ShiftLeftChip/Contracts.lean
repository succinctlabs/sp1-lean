import SP1Clean.Proofs.Chips.ShiftLeftChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # ShiftLeft — circuit-grounding contracts

Folded structural facts used by whole-machine grounding. Arithmetic meaning remains in
`ShiftLeftChip.Spec`; this file projects only the retained reader, state/adapter passthrough, and
the chip-owned selector/routing constraints from the physical circuit.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The grounding-relevant ShiftLeft controls, separated from the expensive arithmetic tail. -/
structure ShiftLeftChip.ControlFacts
    (isReal isSll isSllw opA0 : ZMod p) : Prop where
  selectorLink : isReal = isSll + isSllw
  sllBinary : isSll = 0 ∨ isSll = 1
  sllwBinary : isSllw = 0 ∨ isSllw = 1
  opA0Zero : opA0 = 0

/-- The exact one-hot selector proposition consumed by ShiftLeft's `advanceReady`. -/
def ShiftLeftChip.ActiveSelector (cols : ShiftLeftChip.Columns (ZMod p)) : Prop :=
  (cols.is_sll = 1 ∧ cols.is_sllw = 0) ∨
    (cols.is_sllw = 1 ∧ cols.is_sll = 0)

omit [Fact (2 ^ 17 < p)] in
private theorem ShiftLeftChip.opA0Zero_of_coreSpec
    (cols : ShiftLeftChip.Columns (ZMod p))
    (core : ShiftLeftChip.CoreSpec cols) :
    cols.adapter.op_a_0 = 0 := by
  simp only [ShiftLeftChip.CoreSpec] at core
  tauto

-- Runs at the plain default: the former 4000000 ceiling was ~100x over; measured floor <= 40000.
/-- The physical ShiftLeft constraints identify `is_real` with the flag sum, make both flags
binary, and enforce the non-`x0` destination route in the folded core. -/
theorem ShiftLeftChip.controlFacts_of_mainConstraints
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((ShiftLeftChip.main input).operations offset).ConstraintsHold env) :
    ShiftLeftChip.ControlFacts
      (Expression.eval env input.is_real)
      (Expression.eval env (var { index := offset + 30 }))
      (Expression.eval env (var { index := offset + 31 }))
      (Expression.eval env input.adapter.op_a_0) := by
  have allConstraints := constraints.1
  have hlink := allConstraints
    (input.is_real -
      (var { index := offset + 30 } + var { index := offset + 31 }))
    (ShiftLeftChip.selectorLink_mem_constraints input offset)
  have hsll := allConstraints
    (var { index := offset + 30 } * (var { index := offset + 30 } - 1) - 0)
    (ShiftLeftChip.sllBool_mem_constraints input offset)
  have hsllw := allConstraints
    (var { index := offset + 31 } * (var { index := offset + 31 } - 1) - 0)
    (ShiftLeftChip.sllwBool_mem_constraints input offset)
  let coreInput := ShiftLeftChip.coreInput input offset
  have coreConstraints := constraintsHold_assertionSubcircuit_of_mem env
    ((ShiftLeftChip.main input).operations offset) ShiftLeftCore.circuit coreInput
    (offset + 33) (ShiftLeftChip.core_mem_subcircuits input offset) constraints
  have coreGuarantees :
      ((ShiftLeftCore.circuit.main coreInput).operations
        (offset + 33)).FullGuarantees env := by
    change
      (((FormalAssertion.isGeneralFormalCircuit ShiftLeftCore.circuit).main
        coreInput).operations (offset + 33)).FullGuarantees env
    rw [GeneralFormalCircuit.guarantees_iff]
    have noChannels :
        (FormalAssertion.isGeneralFormalCircuit
          ShiftLeftCore.circuit).channelsWithGuarantees =
          ([] : List (RawChannel (ZMod p))) := rfl
    rw [noChannels]
    simp only [List.not_mem_nil, false_implies, implies_true]
  have coreSoundness :=
    Circuit.can_replace_soundness coreConstraints coreGuarantees
  have core := (ShiftLeftCore.soundness (offset + 33) env coreInput
    (Eval.eval env coreInput) rfl trivial coreSoundness).1
  have hopa0 := ShiftLeftChip.opA0Zero_of_coreSpec (Eval.eval env coreInput) core
  simp only [eval_sub, Expression.eval, sub_zero] at hlink hsll hsllw
  change (Eval.eval env coreInput).adapter.op_a_0 = 0 at hopa0
  dsimp only [coreInput] at hopa0
  rw [ShiftLeftChip.coreInput_eq, ShiftLeftChip.eval_columns,
    Readers.ALUTypeReader.eval_opA0] at hopa0
  exact
    { selectorLink := sub_eq_zero.mp hlink
      sllBinary := bool_of_mul_pred hsll
      sllwBinary := bool_of_mul_pred hsllw
      opA0Zero := hopa0 }

/-- A real physical ShiftLeft row has exactly one active opcode flag. -/
theorem ShiftLeftChip.selectorActive_of_mainConstraints
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((ShiftLeftChip.main input).operations offset).ConstraintsHold env)
    (real : Expression.eval env input.is_real = 1) :
    (Expression.eval env (var { index := offset + 30 }) = 1 ∧
        Expression.eval env (var { index := offset + 31 }) = 0) ∨
      (Expression.eval env (var { index := offset + 31 }) = 1 ∧
        Expression.eval env (var { index := offset + 30 }) = 0) := by
  have control := ShiftLeftChip.controlFacts_of_mainConstraints input offset env constraints
  have sumOne :
      Expression.eval env (var { index := offset + 30 }) +
        Expression.eval env (var { index := offset + 31 }) = 1 :=
    control.selectorLink.symm.trans real
  rcases control.sllBinary with sll0 | sll1
  · exact Or.inr ⟨by simpa only [sll0, zero_add] using sumOne, sll0⟩
  · refine Or.inl ⟨sll1, ?_⟩
    have h := sumOne
    rw [sll1] at h
    linear_combination h

/-- ShiftLeft passes its independent state input through to the completed row. -/
theorem ShiftLeftChip.inputOutputState (env : Environment (ZMod p)) :
    ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state =
      ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).state := by
  let input : Var ShiftLeftChip.Inputs (ZMod p) :=
    varFromOffset ShiftLeftChip.Inputs 0
  let offset := size ShiftLeftChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset ShiftLeftChip.Inputs 0 env
  have outputEq : Eval.eval env ((ShiftLeftChip.circuit (p := p)).output input offset) =
      ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).state =
    (Eval.eval env ((ShiftLeftChip.elaborated (p := p)).output input offset)).state
  rw [ShiftLeftChip.directOutput_eq, ShiftLeftChip.eval_inputs,
    ShiftLeftChip.eval_columns]

/-- ShiftLeft passes its independent ALU adapter input through to the completed row. -/
theorem ShiftLeftChip.inputOutputAdapter (env : Environment (ZMod p)) :
    ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  let input : Var ShiftLeftChip.Inputs (ZMod p) :=
    varFromOffset ShiftLeftChip.Inputs 0
  let offset := size ShiftLeftChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset ShiftLeftChip.Inputs 0 env
  have outputEq : Eval.eval env ((ShiftLeftChip.circuit (p := p)).output input offset) =
      ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).adapter =
    (Eval.eval env ((ShiftLeftChip.elaborated (p := p)).output input offset)).adapter
  rw [ShiftLeftChip.directOutput_eq, ShiftLeftChip.eval_inputs,
    ShiftLeftChip.eval_columns]

/-- The completed ShiftLeft columns at one physical component row. -/
noncomputable def ShiftLeftChip.physicalCols (env : Environment (ZMod p)) :
    ShiftLeftChip.Columns (ZMod p) :=
  (⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env

/-- The completed ShiftLeft row view at one physical component row. -/
noncomputable def ShiftLeftChip.physicalView (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  ShiftLeftChip.rowView
    ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    (ShiftLeftChip.physicalCols env)

/-- The folded physical view's selector is exactly the evaluated typed input selector. -/
theorem ShiftLeftChip.physicalView_isReal (env : Environment (ZMod p)) :
    (ShiftLeftChip.physicalView env).is_real =
      (Eval.eval env
        (varFromOffset (F := ZMod p) ShiftLeftChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset ShiftLeftChip.Inputs 0) =
      (⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset ShiftLeftChip.Inputs 0 env
  simpa only [ShiftLeftChip.physicalView, ShiftLeftChip.rowView] using
    congrArg (fun input : ShiftLeftChip.Inputs (ZMod p) => input.is_real) inputEq.symm

/-- Component-level form of ShiftLeft's physical non-`x0` route. -/
theorem ShiftLeftChip.rowViewOpA0_eq_zero_of_constraints
    (env : Environment (ZMod p))
    (constraints :
      (⟨ShiftLeftChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env) :
    (ShiftLeftChip.physicalView env).adapter.op_a_0 = 0 := by
  let input : Var ShiftLeftChip.Inputs (ZMod p) :=
    varFromOffset ShiftLeftChip.Inputs 0
  let offset := size ShiftLeftChip.Inputs
  have mainConstraints : ((ShiftLeftChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have route :=
    (ShiftLeftChip.controlFacts_of_mainConstraints input offset env mainConstraints).opA0Zero
  have inputEq : Eval.eval env input =
      (⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset ShiftLeftChip.Inputs 0 env
  change ((⟨ShiftLeftChip.circuit (p := p)⟩ :
    Component (ZMod p)).rowOutput env).adapter.op_a_0 = 0
  rw [← ShiftLeftChip.inputOutputAdapter env, ← inputEq,
    ShiftLeftChip.eval_inputAdapter, Readers.ALUTypeReader.eval_opA0]
  exact route

/-- Component-level exact opcode partition used by `advanceReady`. -/
theorem ShiftLeftChip.rowViewSelectorActive_of_constraints
    (env : Environment (ZMod p))
    (constraints :
      (⟨ShiftLeftChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env)
    (real : (ShiftLeftChip.physicalView env).is_real = 1) :
    ShiftLeftChip.ActiveSelector (ShiftLeftChip.physicalCols env) := by
  let input : Var ShiftLeftChip.Inputs (ZMod p) :=
    varFromOffset ShiftLeftChip.Inputs 0
  let offset := size ShiftLeftChip.Inputs
  have mainConstraints : ((ShiftLeftChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have realInput : Expression.eval env input.is_real = 1 := by
    have realValue : (Eval.eval env input).is_real = 1 :=
      (ShiftLeftChip.physicalView_isReal env).symm.trans real
    exact (ShiftLeftChip.eval_inputIsReal env input).symm.trans realValue
  have active :=
    ShiftLeftChip.selectorActive_of_mainConstraints input offset env mainConstraints realInput
  have outputEq : Eval.eval env
      ((ShiftLeftChip.circuit (p := p)).output input offset) =
      ShiftLeftChip.physicalCols env := by
    simp only [input, offset, ShiftLeftChip.physicalCols,
      Component.rowOutput, circuit_norm]
  rw [ShiftLeftChip.ActiveSelector, ← outputEq]
  change ShiftLeftChip.ActiveSelector
    (Eval.eval env ((ShiftLeftChip.elaborated (p := p)).output input offset))
  rw [ShiftLeftChip.ActiveSelector, ShiftLeftChip.directOutput_eq,
    ShiftLeftChip.eval_columns]
  simpa only [offset, circuit_norm] using active

/-- The retained ALU reader binds source C to the decoded immediate on immediate rows. -/
theorem ShiftLeftChip.rowViewOpCBinding_of_constraints
    (env : Environment (ZMod p))
    (constraints :
      (⟨ShiftLeftChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env)
    (immediate : (ShiftLeftChip.physicalView env).adapter.imm_c = 1) :
    (ShiftLeftChip.physicalView env).adapter.op_c_memory.prev_value =
      (ShiftLeftChip.physicalView env).adapter.op_c := by
  let input : Var ShiftLeftChip.Inputs (ZMod p) :=
    varFromOffset ShiftLeftChip.Inputs 0
  let offset := size ShiftLeftChip.Inputs
  let readerInput := ShiftLeftChip.aluReaderInput input offset
  have mainConstraints : ((ShiftLeftChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have readerConstraints := constraintsHold_generalSubcircuit_of_mem env
    ((ShiftLeftChip.main input).operations offset) Readers.ALUTypeReader.circuit
    readerInput (offset + 33)
    (ShiftLeftChip.aluReader_mem_subcircuits input offset) mainConstraints
  have inputEq : Eval.eval env input =
      (⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset ShiftLeftChip.Inputs 0 env
  have immediateInput : Expression.eval env readerInput.cols.imm_c = 1 := by
    change Expression.eval env input.adapter.imm_c = 1
    change ((⟨ShiftLeftChip.circuit (p := p)⟩ :
      Component (ZMod p)).rowOutput env).adapter.imm_c = 1 at immediate
    rw [← ShiftLeftChip.inputOutputAdapter env, ← inputEq,
      ShiftLeftChip.eval_inputs, Readers.ALUTypeReader.eval_immC] at immediate
    exact immediate
  have binding := Readers.ALUTypeReader.eval_opCPrev_eq_opC_of_mainConstraints
    readerInput (offset + 33) env readerConstraints immediateInput
  change ((⟨ShiftLeftChip.circuit (p := p)⟩ :
    Component (ZMod p)).rowOutput env).adapter.op_c_memory.prev_value =
      ((⟨ShiftLeftChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowOutput env).adapter.op_c
  rw [← ShiftLeftChip.inputOutputAdapter env, ← inputEq,
    ShiftLeftChip.eval_inputs, Readers.ALUTypeReader.eval_opCPrev,
    Readers.ALUTypeReader.eval_opC]
  simpa only [readerInput, ShiftLeftChip.aluReaderInput] using binding

end SP1Clean.Soundness
