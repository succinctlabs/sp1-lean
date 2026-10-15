import SP1Clean.Alignment.Chips.BitwiseChip.Bridge
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
private def BitwiseChip.controlExpressions
    (input : Var BitwiseChip.Inputs (ZMod p)) : List (Expression (ZMod p)) :=
  [ input.isXor * (input.isXor - 1) - 0,
    input.isOr * (input.isOr - 1) - 0,
    input.isAnd * (input.isAnd - 1) - 0,
    input.adapter.op_a_0 - 0 ]

/-- The selector booleans and destination route needed for Bitwise grounding. -/
structure BitwiseChip.ControlFacts (isXor isOr isAnd opA0 : ZMod p) : Prop where
  xorBinary : isXor = 0 ∨ isXor = 1
  orBinary : isOr = 0 ∨ isOr = 1
  andBinary : isAnd = 0 ∨ isAnd = 1
  opA0Zero : opA0 = 0

/-- The active-selector proposition consumed by Bitwise's `advanceReady`. -/
def BitwiseChip.ActiveSelector (cols : BitwiseChip.Columns (ZMod p)) : Prop :=
  cols.is_and = 1 ∨ cols.is_or = 1 ∨ cols.is_xor = 1

-- Runs at the plain default: the former 4000000 ceiling was ~100x over; measured floor <= 40000.
private theorem BitwiseChip.controlExpressions_subset_constraints
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) :
    ∀ e ∈ BitwiseChip.controlExpressions (p := p) input,
      e ∈ ((BitwiseChip.main input).operations offset).constraints := by
  intro e he
  simp only [BitwiseChip.controlExpressions, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · simp only [BitwiseChip.main, circuit_norm]
    right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem (input.isXor * (input.isXor - 1)) (0 : Expression (ZMod p)) _
  · simp only [BitwiseChip.main, circuit_norm]
    right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem (input.isOr * (input.isOr - 1)) (0 : Expression (ZMod p)) _
  · simp only [BitwiseChip.main, circuit_norm]
    right; right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem (input.isAnd * (input.isAnd - 1)) (0 : Expression (ZMod p)) _
  · simp only [BitwiseChip.main, circuit_norm]
    right; right; right; right; right; right; right; right
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 (0 : Expression (ZMod p)) _

/-- Physical Bitwise assertions make each explicit selector binary and enforce a non-`x0`
destination. Activity is already their sum by construction. -/
theorem BitwiseChip.controlFacts_of_mainConstraints
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env) :
    BitwiseChip.ControlFacts
      (Expression.eval env input.isXor)
      (Expression.eval env input.isOr)
      (Expression.eval env input.isAnd)
      (Expression.eval env input.adapter.op_a_0) := by
  have allConstraints := constraints.1
  have control (e : Expression (ZMod p))
      (he : e ∈ BitwiseChip.controlExpressions (p := p) input) :
      Expression.eval env e = 0 :=
    allConstraints e (BitwiseChip.controlExpressions_subset_constraints input offset e he)
  have g0 := control (input.isXor * (input.isXor - 1) - 0) (by
    simp [BitwiseChip.controlExpressions])
  have g1 := control (input.isOr * (input.isOr - 1) - 0) (by
    simp [BitwiseChip.controlExpressions])
  have g2 := control (input.isAnd * (input.isAnd - 1) - 0) (by
    simp [BitwiseChip.controlExpressions])
  have route := control (input.adapter.op_a_0 - 0) (by
    simp [BitwiseChip.controlExpressions])
  simp only [eval_sub, Expression.eval, sub_zero] at g0 g1 g2 route
  exact ⟨bool_of_mul_pred g0, bool_of_mul_pred g1, bool_of_mul_pred g2, route⟩

/-- A real physical Bitwise row has at least one active opcode flag. The mutual-exclusion part is
already a proved conjunct of `BitwiseChip.Spec`; grounding only needs this existence half. -/
theorem BitwiseChip.selectorActive_of_mainConstraints
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env)
    (real : Expression.eval env input.is_real = 1) :
    Expression.eval env input.isAnd = 1 ∨
      Expression.eval env input.isOr = 1 ∨
      Expression.eval env input.isXor = 1 := by
  have control := BitwiseChip.controlFacts_of_mainConstraints input offset env constraints
  have sumOne : Expression.eval env input.isXor +
      Expression.eval env input.isOr +
        Expression.eval env input.isAnd = 1 := real
  rcases control.andBinary with and0 | and1
  · rcases control.orBinary with or0 | or1
    · rcases control.xorBinary with xor0 | xor1
      · rw [xor0, or0, and0] at sumOne
        simp at sumOne
      · exact Or.inr (Or.inr xor1)
    · exact Or.inr (Or.inl or1)
  · exact Or.inl and1

/-- Bitwise passes its independent state input through to the completed row. -/
theorem BitwiseChip.inputOutputState (env : Environment (ZMod p)) :
    (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowInput env).state =
      (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowOutput env).state := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  have inputEq : Eval.eval env input =
      (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset BitwiseChip.Inputs 0 env
  have outputEq : Eval.eval env ((BitwiseChip.circuit (p := p)).output input offset) =
      (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).state =
    (Eval.eval env ((BitwiseChip.elaborated (p := p)).output input offset)).state
  rw [BitwiseChip.directOutput_eq, BitwiseChip.eval_inputs, BitwiseChip.eval_columns]

/-- Bitwise passes its independent ALU adapter input through to the completed row. -/
theorem BitwiseChip.inputOutputAdapter (env : Environment (ZMod p)) :
    (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowInput env).adapter =
      (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowOutput env).adapter := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  have inputEq : Eval.eval env input =
      (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset BitwiseChip.Inputs 0 env
  have outputEq : Eval.eval env ((BitwiseChip.circuit (p := p)).output input offset) =
      (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowOutput env) := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  change (Eval.eval env input).adapter =
    (Eval.eval env ((BitwiseChip.elaborated (p := p)).output input offset)).adapter
  rw [BitwiseChip.directOutput_eq, BitwiseChip.eval_inputs, BitwiseChip.eval_columns]

/-- The completed Bitwise view at one physical component row. Keeping this projection folded avoids
normalizing the full witnessed arithmetic row in every structural theorem statement. -/
noncomputable def BitwiseChip.physicalCols (env : Environment (ZMod p)) :
    BitwiseChip.Columns (ZMod p) :=
  ({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowOutput env

/-- The completed Bitwise view at one physical component row. -/
noncomputable def BitwiseChip.physicalView (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  BitwiseChip.rowView
    (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowInput env)
    (BitwiseChip.physicalCols env)

/-- The folded physical view's selector is exactly the evaluated typed input selector. -/
theorem BitwiseChip.physicalView_isReal (env : Environment (ZMod p)) :
    (BitwiseChip.physicalView env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) BitwiseChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset BitwiseChip.Inputs 0) =
      ({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset BitwiseChip.Inputs 0 env
  simpa only [BitwiseChip.physicalView, BitwiseChip.rowView] using
    congrArg (fun input : BitwiseChip.Inputs (ZMod p) => input.is_real) inputEq.symm

/-- Component-level form of Bitwise's physical non-`x0` route. -/
theorem BitwiseChip.rowViewOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints :
      ({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).operations.ConstraintsHold env) :
    (BitwiseChip.physicalView env).adapter.op_a_0 = 0 := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  have mainConstraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have route :=
    (BitwiseChip.controlFacts_of_mainConstraints input offset env mainConstraints).opA0Zero
  have inputEq : Eval.eval env input =
      ({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset BitwiseChip.Inputs 0 env
  change (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowOutput env).adapter.op_a_0 = 0
  rw [← BitwiseChip.inputOutputAdapter env, ← inputEq, BitwiseChip.eval_inputAdapter,
    Readers.ALUTypeReader.eval_opA0]
  exact route

/-- Component-level active opcode partition used by `advanceReady`. -/
theorem BitwiseChip.rowViewSelectorActive_of_constraints (env : Environment (ZMod p))
    (constraints :
      ({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).operations.ConstraintsHold env)
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

/-- The exact ALU reader input retained after Bitwise's sixteen byte witness cells. -/
def BitwiseChip.aluTypeReaderInput (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    input.isXor * 3 + input.isOr * 4 + input.isAnd * 5,
    var ⟨offset + 8⟩ + var ⟨offset + 9⟩ * 256,
    var ⟨offset + 10⟩ + var ⟨offset + 11⟩ * 256,
    var ⟨offset + 12⟩ + var ⟨offset + 13⟩ * 256,
    var ⟨offset + 14⟩ + var ⟨offset + 15⟩ * 256⟩

theorem BitwiseChip.aluTypeReader_mem (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 16, Readers.ALUTypeReader.circuit.toSubcircuit (offset + 16)
      (BitwiseChip.aluTypeReaderInput input offset)⟩ ∈
      ((BitwiseChip.main input).operations offset).subcircuits := by
  simp only [BitwiseChip.main, BitwiseChip.aluTypeReaderInput,
    Readers.ALUTypeReader.circuit, circuit_norm]

/-- The retained ALU reader binds source C to the decoded immediate on immediate rows. -/
theorem BitwiseChip.rowViewOpCBinding_of_constraints (env : Environment (ZMod p))
    (constraints :
      ({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).operations.ConstraintsHold env)
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
    (offset + 16) (BitwiseChip.aluTypeReader_mem input offset) mainConstraints
  have inputEq : Eval.eval env input =
      ({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset BitwiseChip.Inputs 0 env
  have immediateInput : Expression.eval env readerInput.cols.imm_c = 1 := by
    change Expression.eval env input.adapter.imm_c = 1
    change (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowOutput env).adapter.imm_c = 1
      at immediate
    rw [← BitwiseChip.inputOutputAdapter env, ← inputEq, BitwiseChip.eval_inputs,
      Readers.ALUTypeReader.eval_immC] at immediate
    exact immediate
  have binding := Readers.ALUTypeReader.eval_opCPrev_eq_opC_of_mainConstraints
    readerInput (offset + 16) env readerConstraints immediateInput
  change (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowOutput env).adapter.op_c_memory.prev_value =
    (({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).rowOutput env).adapter.op_c
  rw [← BitwiseChip.inputOutputAdapter env, ← inputEq, BitwiseChip.eval_inputs,
    Readers.ALUTypeReader.eval_opCPrev, Readers.ALUTypeReader.eval_opC]
  simpa only [readerInput, BitwiseChip.aluTypeReaderInput] using binding

/-- With binary flags summing to one, Bitwise's committed opcode combination avoids `ECALL`'s
discriminant `50`. -/
private theorem BitwiseChip.flagCombo_ne_ecall {x y z : ZMod p}
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1)
    (hsum : x + y + z = 1) :
    x * 3 + y * 4 + z * 5 ≠ (50 : ZMod p) := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℕ, a ≤ 1 ∧ x = (a : ZMod p) := by
    rcases hx with h | h
    · exact ⟨0, Nat.zero_le 1, by rw [h, Nat.cast_zero]⟩
    · exact ⟨1, Nat.le_refl 1, by rw [h, Nat.cast_one]⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℕ, b ≤ 1 ∧ y = (b : ZMod p) := by
    rcases hy with h | h
    · exact ⟨0, Nat.zero_le 1, by rw [h, Nat.cast_zero]⟩
    · exact ⟨1, Nat.le_refl 1, by rw [h, Nat.cast_one]⟩
  obtain ⟨c, hc, rfl⟩ : ∃ c : ℕ, c ≤ 1 ∧ z = (c : ZMod p) := by
    rcases hz with h | h
    · exact ⟨0, Nat.zero_le 1, by rw [h, Nat.cast_zero]⟩
    · exact ⟨1, Nat.le_refl 1, by rw [h, Nat.cast_one]⟩
  have hp : (131072 : ℕ) < p := by
    have hfact : (2 : ℕ) ^ 17 < p := Fact.out
    norm_num at hfact
    exact hfact
  have hsumNat : ((a + b + c : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by exact_mod_cast hsum
  have hs := congrArg ZMod.val hsumNat
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hs
  intro h
  have hcast : ((a * 3 + b * 4 + c * 5 : ℕ) : ZMod p) = ((50 : ℕ) : ZMod p) := by
    exact_mod_cast h
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
  omega

/-- A real physical Bitwise row's Program-bus opcode is never the `ECALL` discriminant `50`
(the committed-fragment re-base's per-chip strengthening fact). -/
theorem BitwiseChip.physicalViewOpcode_ne_ecall (env : Environment (ZMod p))
    (constraints :
      ({ circuit := BitwiseChip.circuit (p := p) } : Component (ZMod p)).operations.ConstraintsHold env)
    (real : (BitwiseChip.physicalView env).is_real = 1) :
    (BitwiseChip.physicalView env).opcode ≠ (50 : ZMod p) := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  have mainConstraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have control := BitwiseChip.controlFacts_of_mainConstraints input offset env mainConstraints
  have realInput : Expression.eval env input.is_real = 1 := by
    have realValue : (Eval.eval env input).is_real = 1 :=
      (BitwiseChip.physicalView_isReal env).symm.trans real
    exact (BitwiseChip.eval_inputIsReal env input).symm.trans realValue
  have sumOne : Expression.eval env input.isXor +
      Expression.eval env input.isOr +
        Expression.eval env input.isAnd = 1 := realInput
  have notEcall :
      Expression.eval env input.isXor * 3 +
          Expression.eval env input.isOr * 4 +
          Expression.eval env input.isAnd * 5 ≠ (50 : ZMod p) :=
    BitwiseChip.flagCombo_ne_ecall control.xorBinary control.orBinary control.andBinary sumOne
  have outputEq : Eval.eval env ((BitwiseChip.circuit (p := p)).output input offset) =
      BitwiseChip.physicalCols env := by
    simp only [input, offset, BitwiseChip.physicalCols, Component.rowOutput, circuit_norm]
  show (BitwiseChip.physicalCols env).is_xor * 3 + (BitwiseChip.physicalCols env).is_or * 4 +
    (BitwiseChip.physicalCols env).is_and * 5 ≠ (50 : ZMod p)
  rw [← outputEq]
  change (Eval.eval env ((BitwiseChip.elaborated (p := p)).output input offset)).is_xor * 3 +
      (Eval.eval env ((BitwiseChip.elaborated (p := p)).output input offset)).is_or * 4 +
      (Eval.eval env ((BitwiseChip.elaborated (p := p)).output input offset)).is_and * 5 ≠
    (50 : ZMod p)
  rw [BitwiseChip.directOutput_eq, BitwiseChip.eval_columns]
  simpa only [offset, circuit_norm] using notEcall

end SP1Clean.Soundness
