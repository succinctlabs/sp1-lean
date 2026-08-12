import SP1Clean.Proofs.Chips.ShiftRightChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # ShiftRight — circuit-grounding contracts

Folded structural facts used by whole-machine grounding. Arithmetic meaning remains in
`ShiftRightChip.Spec`; this file projects only the retained reader, state/adapter passthrough, and
the chip-owned selector/routing constraints from the physical circuit.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The grounding-relevant ShiftRight controls, separated from the expensive arithmetic tail. -/
structure ShiftRightChip.ControlFacts
    (isReal isSrl isSra isSrlw isSraw opA0 : ZMod p) : Prop where
  selectorLink : isReal = isSrl + isSra + isSrlw + isSraw
  srlBinary : isSrl = 0 ∨ isSrl = 1
  sraBinary : isSra = 0 ∨ isSra = 1
  srlwBinary : isSrlw = 0 ∨ isSrlw = 1
  srawBinary : isSraw = 0 ∨ isSraw = 1
  opA0Zero : opA0 = 0

/-- The exact one-hot selector proposition consumed by ShiftRight's `advanceReady`. -/
def ShiftRightChip.ActiveSelector (cols : ShiftRightChip.Columns (ZMod p)) : Prop :=
  (cols.is_srl = 1 ∧ cols.is_sra = 0 ∧ cols.is_srlw = 0 ∧ cols.is_sraw = 0) ∨
  (cols.is_sra = 1 ∧ cols.is_srl = 0 ∧ cols.is_srlw = 0 ∧ cols.is_sraw = 0) ∨
  (cols.is_srlw = 1 ∧ cols.is_srl = 0 ∧ cols.is_sra = 0 ∧ cols.is_sraw = 0) ∨
  (cols.is_sraw = 1 ∧ cols.is_srl = 0 ∧ cols.is_sra = 0 ∧ cols.is_srlw = 0)

omit [Fact (2 ^ 17 < p)] in
private theorem ShiftRightChip.opA0Zero_of_coreSpec
    (cols : ShiftRightChip.Columns (ZMod p))
    (core : ShiftRightChip.CoreSpec cols) :
    cols.adapter.op_a_0 = 0 := by
  simp only [ShiftRightChip.CoreSpec] at core
  tauto

-- Runs at the plain default: the former 4000000 ceiling was ~100x over; measured floor <= 40000.
/-- The physical ShiftRight constraints identify `is_real` with the flag sum, make all four flags
binary, and enforce the non-`x0` destination route in the folded core. -/
theorem ShiftRightChip.controlFacts_of_mainConstraints
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((ShiftRightChip.main input).operations offset).ConstraintsHold env) :
    ShiftRightChip.ControlFacts
      (Expression.eval env input.is_real)
      (Expression.eval env (var { index := offset + 32 }))
      (Expression.eval env (var { index := offset + 33 }))
      (Expression.eval env (var { index := offset + 34 }))
      (Expression.eval env (var { index := offset + 35 }))
      (Expression.eval env input.adapter.op_a_0) := by
  have allConstraints := constraints.1
  have hlink := allConstraints
    (input.is_real -
      (var { index := offset + 32 } + var { index := offset + 33 } +
        var { index := offset + 34 } + var { index := offset + 35 }))
    (ShiftRightChip.selectorLink_mem_constraints input offset)
  have hsrl := allConstraints
    (var { index := offset + 32 } * (var { index := offset + 32 } - 1) - 0)
    (ShiftRightChip.srlBool_mem_constraints input offset)
  have hsra := allConstraints
    (var { index := offset + 33 } * (var { index := offset + 33 } - 1) - 0)
    (ShiftRightChip.sraBool_mem_constraints input offset)
  have hsrlw := allConstraints
    (var { index := offset + 34 } * (var { index := offset + 34 } - 1) - 0)
    (ShiftRightChip.srlwBool_mem_constraints input offset)
  have hsraw := allConstraints
    (var { index := offset + 35 } * (var { index := offset + 35 } - 1) - 0)
    (ShiftRightChip.srawBool_mem_constraints input offset)
  let coreInput := ShiftRightChip.coreInput input offset
  have coreConstraints := constraintsHold_assertionSubcircuit_of_mem env
    ((ShiftRightChip.main input).operations offset) ShiftRightCore.circuit coreInput
    (offset + 37) (ShiftRightChip.core_mem_subcircuits input offset) constraints
  have coreGuarantees :
      ((ShiftRightCore.circuit.main coreInput).operations
        (offset + 37)).FullGuarantees env := by
    change
      (((FormalAssertion.isGeneralFormalCircuit ShiftRightCore.circuit).main
        coreInput).operations (offset + 37)).FullGuarantees env
    rw [GeneralFormalCircuit.guarantees_iff]
    have noChannels :
        (FormalAssertion.isGeneralFormalCircuit
          ShiftRightCore.circuit).channelsWithGuarantees =
          ([] : List (RawChannel (ZMod p))) := rfl
    rw [noChannels]
    simp only [List.not_mem_nil, false_implies, implies_true]
  have coreSoundness :=
    Circuit.can_replace_soundness coreConstraints coreGuarantees
  have core := (ShiftRightCore.soundness (offset + 37) env coreInput
    (Eval.eval env coreInput) rfl trivial coreSoundness).1
  have hopa0 := ShiftRightChip.opA0Zero_of_coreSpec (Eval.eval env coreInput) core
  simp only [eval_sub, Expression.eval, sub_zero] at hlink hsrl hsra hsrlw hsraw
  change (Eval.eval env coreInput).adapter.op_a_0 = 0 at hopa0
  dsimp only [coreInput] at hopa0
  rw [ShiftRightChip.coreInput_eq, ShiftRightChip.eval_columns,
    Readers.ALUTypeReader.eval_opA0] at hopa0
  exact
    { selectorLink := sub_eq_zero.mp hlink
      srlBinary := bool_of_mul_pred hsrl
      sraBinary := bool_of_mul_pred hsra
      srlwBinary := bool_of_mul_pred hsrlw
      srawBinary := bool_of_mul_pred hsraw
      opA0Zero := hopa0 }

/-- A real physical ShiftRight row has exactly one active opcode flag. -/
theorem ShiftRightChip.selectorActive_of_mainConstraints
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((ShiftRightChip.main input).operations offset).ConstraintsHold env)
    (real : Expression.eval env input.is_real = 1) :
    (Expression.eval env (var { index := offset + 32 }) = 1 ∧
      Expression.eval env (var { index := offset + 33 }) = 0 ∧
      Expression.eval env (var { index := offset + 34 }) = 0 ∧
      Expression.eval env (var { index := offset + 35 }) = 0) ∨
    (Expression.eval env (var { index := offset + 33 }) = 1 ∧
      Expression.eval env (var { index := offset + 32 }) = 0 ∧
      Expression.eval env (var { index := offset + 34 }) = 0 ∧
      Expression.eval env (var { index := offset + 35 }) = 0) ∨
    (Expression.eval env (var { index := offset + 34 }) = 1 ∧
      Expression.eval env (var { index := offset + 32 }) = 0 ∧
      Expression.eval env (var { index := offset + 33 }) = 0 ∧
      Expression.eval env (var { index := offset + 35 }) = 0) ∨
    (Expression.eval env (var { index := offset + 35 }) = 1 ∧
      Expression.eval env (var { index := offset + 32 }) = 0 ∧
      Expression.eval env (var { index := offset + 33 }) = 0 ∧
      Expression.eval env (var { index := offset + 34 }) = 0) := by
  have control := ShiftRightChip.controlFacts_of_mainConstraints input offset env constraints
  have sumOne :
      Expression.eval env (var { index := offset + 32 }) +
        Expression.eval env (var { index := offset + 33 }) +
        Expression.eval env (var { index := offset + 34 }) +
        Expression.eval env (var { index := offset + 35 }) = 1 :=
    control.selectorLink.symm.trans real
  let flags : Vector (ZMod p) 4 :=
    #v[Expression.eval env (var { index := offset + 32 }),
       Expression.eval env (var { index := offset + 33 }),
       Expression.eval env (var { index := offset + 34 }),
       Expression.eval env (var { index := offset + 35 })]
  have oneHot := ShiftRightChip.one_hot_resolve flags
    control.srlBinary control.sraBinary control.srlwBinary control.srawBinary
    (Or.inr sumOne)
  simp only [flags, Vector.getElem_mk, List.getElem_toArray] at oneHot
  rcases control.srlBinary with srl0 | srl1
  · rcases control.sraBinary with sra0 | sra1
    · rcases control.srlwBinary with srlw0 | srlw1
      · exact Or.inr (Or.inr (Or.inr
          ⟨by simpa only [srl0, sra0, srlw0, zero_add] using sumOne,
            srl0, sra0, srlw0⟩))
      · obtain ⟨srl0', sra0', sraw0⟩ := oneHot.2.2.1 srlw1
        exact Or.inr (Or.inr (Or.inl ⟨srlw1, srl0', sra0', sraw0⟩))
    · obtain ⟨srl0', srlw0, sraw0⟩ := oneHot.2.1 sra1
      exact Or.inr (Or.inl ⟨sra1, srl0', srlw0, sraw0⟩)
  · obtain ⟨sra0, srlw0, sraw0⟩ := oneHot.1 srl1
    exact Or.inl ⟨srl1, sra0, srlw0, sraw0⟩

/-- ShiftRight passes its independent state input through to the completed row. -/
theorem ShiftRightChip.inputOutputState (env : Environment (ZMod p)) :
    ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state =
      ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).state := by
  let input : Var ShiftRightChip.Inputs (ZMod p) :=
    varFromOffset ShiftRightChip.Inputs 0
  let offset := size ShiftRightChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset ShiftRightChip.Inputs 0 env
  have outputEq : Eval.eval env ((ShiftRightChip.circuit (p := p)).output input offset) =
      ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).state =
    (Eval.eval env ((ShiftRightChip.elaborated (p := p)).output input offset)).state
  rw [ShiftRightChip.directOutput_eq, ShiftRightChip.eval_inputs,
    ShiftRightChip.eval_columns]

/-- ShiftRight passes its independent ALU adapter input through to the completed row. -/
theorem ShiftRightChip.inputOutputAdapter (env : Environment (ZMod p)) :
    ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  let input : Var ShiftRightChip.Inputs (ZMod p) :=
    varFromOffset ShiftRightChip.Inputs 0
  let offset := size ShiftRightChip.Inputs
  have inputEq : Eval.eval env input =
      ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset ShiftRightChip.Inputs 0 env
  have outputEq : Eval.eval env ((ShiftRightChip.circuit (p := p)).output input offset) =
      ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).adapter =
    (Eval.eval env ((ShiftRightChip.elaborated (p := p)).output input offset)).adapter
  rw [ShiftRightChip.directOutput_eq, ShiftRightChip.eval_inputs,
    ShiftRightChip.eval_columns]

/-- The completed ShiftRight columns at one physical component row. -/
noncomputable def ShiftRightChip.physicalCols (env : Environment (ZMod p)) :
    ShiftRightChip.Columns (ZMod p) :=
  (⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env

/-- The completed ShiftRight row view at one physical component row. -/
noncomputable def ShiftRightChip.physicalView (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  ShiftRightChip.rowView
    ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    (ShiftRightChip.physicalCols env)

/-- The folded physical view's selector is exactly the evaluated typed input selector. -/
theorem ShiftRightChip.physicalView_isReal (env : Environment (ZMod p)) :
    (ShiftRightChip.physicalView env).is_real =
      (Eval.eval env
        (varFromOffset (F := ZMod p) ShiftRightChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset ShiftRightChip.Inputs 0) =
      (⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset ShiftRightChip.Inputs 0 env
  simpa only [ShiftRightChip.physicalView, ShiftRightChip.rowView] using
    congrArg (fun input : ShiftRightChip.Inputs (ZMod p) => input.is_real) inputEq.symm

/-- Component-level form of ShiftRight's physical non-`x0` route. -/
theorem ShiftRightChip.rowViewOpA0_eq_zero_of_constraints
    (env : Environment (ZMod p))
    (constraints :
      (⟨ShiftRightChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env) :
    (ShiftRightChip.physicalView env).adapter.op_a_0 = 0 := by
  let input : Var ShiftRightChip.Inputs (ZMod p) :=
    varFromOffset ShiftRightChip.Inputs 0
  let offset := size ShiftRightChip.Inputs
  have mainConstraints : ((ShiftRightChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have route :=
    (ShiftRightChip.controlFacts_of_mainConstraints input offset env mainConstraints).opA0Zero
  have inputEq : Eval.eval env input =
      (⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset ShiftRightChip.Inputs 0 env
  change ((⟨ShiftRightChip.circuit (p := p)⟩ :
    Component (ZMod p)).rowOutput env).adapter.op_a_0 = 0
  rw [← ShiftRightChip.inputOutputAdapter env, ← inputEq,
    ShiftRightChip.eval_inputAdapter, Readers.ALUTypeReader.eval_opA0]
  exact route

/-- Component-level exact opcode partition used by `advanceReady`. -/
theorem ShiftRightChip.rowViewSelectorActive_of_constraints
    (env : Environment (ZMod p))
    (constraints :
      (⟨ShiftRightChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env)
    (real : (ShiftRightChip.physicalView env).is_real = 1) :
    ShiftRightChip.ActiveSelector (ShiftRightChip.physicalCols env) := by
  let input : Var ShiftRightChip.Inputs (ZMod p) :=
    varFromOffset ShiftRightChip.Inputs 0
  let offset := size ShiftRightChip.Inputs
  have mainConstraints : ((ShiftRightChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have realInput : Expression.eval env input.is_real = 1 := by
    have realValue : (Eval.eval env input).is_real = 1 :=
      (ShiftRightChip.physicalView_isReal env).symm.trans real
    exact (ShiftRightChip.eval_inputIsReal env input).symm.trans realValue
  have active :=
    ShiftRightChip.selectorActive_of_mainConstraints input offset env mainConstraints realInput
  have outputEq : Eval.eval env
      ((ShiftRightChip.circuit (p := p)).output input offset) =
      ShiftRightChip.physicalCols env := by
    simp only [input, offset, ShiftRightChip.physicalCols,
      Component.rowOutput, circuit_norm]
  rw [ShiftRightChip.ActiveSelector, ← outputEq]
  change ShiftRightChip.ActiveSelector
    (Eval.eval env ((ShiftRightChip.elaborated (p := p)).output input offset))
  rw [ShiftRightChip.ActiveSelector, ShiftRightChip.directOutput_eq,
    ShiftRightChip.eval_columns]
  simpa only [offset, circuit_norm] using active

/-- The retained ALU reader binds source C to the decoded immediate on immediate rows. -/
theorem ShiftRightChip.rowViewOpCBinding_of_constraints
    (env : Environment (ZMod p))
    (constraints :
      (⟨ShiftRightChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env)
    (immediate : (ShiftRightChip.physicalView env).adapter.imm_c = 1) :
    (ShiftRightChip.physicalView env).adapter.op_c_memory.prev_value =
      (ShiftRightChip.physicalView env).adapter.op_c := by
  let input : Var ShiftRightChip.Inputs (ZMod p) :=
    varFromOffset ShiftRightChip.Inputs 0
  let offset := size ShiftRightChip.Inputs
  let readerInput := ShiftRightChip.aluReaderInput input offset
  have mainConstraints : ((ShiftRightChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have readerConstraints := constraintsHold_generalSubcircuit_of_mem env
    ((ShiftRightChip.main input).operations offset) Readers.ALUTypeReader.circuit
    readerInput (offset + 37)
    (ShiftRightChip.aluReader_mem_subcircuits input offset) mainConstraints
  have inputEq : Eval.eval env input =
      (⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset ShiftRightChip.Inputs 0 env
  have immediateInput : Expression.eval env readerInput.cols.imm_c = 1 := by
    change Expression.eval env input.adapter.imm_c = 1
    change ((⟨ShiftRightChip.circuit (p := p)⟩ :
      Component (ZMod p)).rowOutput env).adapter.imm_c = 1 at immediate
    rw [← ShiftRightChip.inputOutputAdapter env, ← inputEq,
      ShiftRightChip.eval_inputs, Readers.ALUTypeReader.eval_immC] at immediate
    exact immediate
  have binding := Readers.ALUTypeReader.eval_opCPrev_eq_opC_of_mainConstraints
    readerInput (offset + 37) env readerConstraints immediateInput
  change ((⟨ShiftRightChip.circuit (p := p)⟩ :
    Component (ZMod p)).rowOutput env).adapter.op_c_memory.prev_value =
      ((⟨ShiftRightChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowOutput env).adapter.op_c
  rw [← ShiftRightChip.inputOutputAdapter env, ← inputEq,
    ShiftRightChip.eval_inputs, Readers.ALUTypeReader.eval_opCPrev,
    Readers.ALUTypeReader.eval_opC]
  simpa only [readerInput, ShiftRightChip.aluReaderInput] using binding

end SP1Clean.Soundness
