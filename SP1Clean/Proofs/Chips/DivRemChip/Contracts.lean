import SP1Clean.Proofs.Chips.DivRemChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # DivRem — circuit-grounding contracts

Folded structural facts crossing the completed DivRem circuit boundary.  The 217-cell witness row
and its arithmetic evidence stay opaque: this module exposes only the retained R-type reader,
adapter passthrough, and the physical `op_a_0 = 0` routing assertion needed by whole-machine
grounding.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The exact R-type reader input retained after DivRem's 217-cell witness prefix. -/
def DivRemChip.rTypeReaderInput (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.RTypeReader.Inputs (ZMod p) :=
  let cols := DivRemChip.populatedRowAt input offset
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    cols.is_divu * 16 + cols.is_remu * 18 + cols.is_div * 15 + cols.is_rem * 17 +
      cols.is_divw * 25 + cols.is_remw * 27 + cols.is_divuw * 26 + cols.is_remuw * 28,
    cols.a[0], cols.a[1], cols.a[2], cols.a[3]⟩

/-- The retained R-type reader occurs immediately after the folded witness prefix. -/
theorem DivRemChip.rTypeReader_mem (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 217, Readers.RTypeReader.circuit.toSubcircuit (offset + 217)
      (DivRemChip.rTypeReaderInput input offset)⟩ ∈
      ((DivRemChip.main input).operations offset).subcircuits := by
  simp only [DivRemChip.main, DivRemChip.rTypeReaderInput, circuit_norm]
  right
  simp only [DivRemChip.constrainRow, circuit_norm]
  right; left
  simp only [DivRemChip.populateRow_output_eq, Nat.add_zero]

/-- The DivRem arithmetic-core assertion boundary is retained at the same post-witness offset. -/
private theorem DivRemChip.divRemCore_mem
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 217, DivRemCore.circuit.toSubcircuit (offset + 217)
      (DivRemChip.populatedRowAt input offset)⟩ ∈
      ((DivRemChip.main input).operations offset).subcircuits := by
  simp only [DivRemChip.main, circuit_norm]
  right
  simp only [DivRemChip.constrainRow, circuit_norm]
  right; right; right; left
  simp only [DivRemChip.populateRow_output_eq, Nat.add_zero]

/-- DivRemCore's shallow constraint contract exposes the final physical routing assertion without
normalizing either multiplication subcircuit or the byte-interaction tail. -/
private theorem DivRemChip.opA0_eq_zero_of_coreShallowConstraints
    (env : Environment (ZMod p)) (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ)
    (shallow : ConstraintsHold.Shallow env ((DivRemCore.main cols).operations offset)) :
    Expression.eval env cols.adapter.op_a_0 = 0 := by
  simp only [DivRemCore.main, Circuit.operations, Circuit.bind_def, assertion,
    DivRemChip.assertZeros, Channel.pullIf, HasAssertEq.assert_eq,
    Expression.assertEquals, Operations.localLength] at shallow
  simp only [ConstraintsHold.Shallow, Operations.forAllNoOffset_append,
    Operations.forAllNoOffset, DivRemChip.forAllNoOffset_map_assert, true_and,
    and_true] at shallow
  exact shallow _ (DivRemChip.opA0_mem_ownAsserts cols)

/-- DivRem's completed circuit output is exactly the named folded witness layout. -/
theorem DivRemChip.circuit_output_eq (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    (DivRemChip.circuit (p := p)).output input offset =
      DivRemChip.populatedRowAt input offset := by
  change (DivRemChip.elaborated (p := p)).output input offset = _
  rw [← DivRemChip.elaborated.output_eq, DivRemChip.main_output_eq_populateRow,
    DivRemChip.populateRow_output_eq]

/-- The completed circuit retains `DivRemChip.main` as its physical row program.  Naming this
projection prevents contract constructors from unfolding the full circuit record during unification. -/
theorem DivRemChip.circuit_main_eq :
    (DivRemChip.circuit (p := p)).main = DivRemChip.main := rfl

/-- DivRem's direct output passes the independent R-type adapter through unchanged. -/
theorem DivRemChip.eval_output_adapter (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) :
    (Eval.eval env input).adapter =
      (Eval.eval env ((DivRemChip.circuit (p := p)).output input offset)).adapter := by
  rw [DivRemChip.circuit_output_eq, DivRemChip.eval_inputs,
    DivRemChip.eval_divRemCols_adapter_verifier, DivRemChip.populatedRowAt_adapter_eq]

/-- DivRem's direct output passes the independent CPU-state block through unchanged. -/
theorem DivRemChip.eval_output_state (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) :
    (Eval.eval env input).state =
      (Eval.eval env ((DivRemChip.circuit (p := p)).output input offset)).state := by
  rw [DivRemChip.circuit_output_eq, DivRemChip.eval_inputs,
    DivRemChip.eval_divRemCols_state_verifier, DivRemChip.populatedRowAt_state_eq]

/-- Scalar projection of DivRem's committed destination word. -/
theorem DivRemChip.eval_output_a (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) :
    (Eval.eval env ((DivRemChip.circuit (p := p)).output input offset)).a =
      Eval.eval env (DivRemChip.populatedRowAt input offset).a := by
  rw [DivRemChip.circuit_output_eq, DivRemChip.eval_divRemCols_a_verifier]

/-- Component-level adapter passthrough, with the large output layout kept folded. -/
theorem DivRemChip.inputOutputAdapter (env : Environment (ZMod p)) :
    ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  let input : Var DivRemChip.Inputs (ZMod p) := varFromOffset DivRemChip.Inputs 0
  let offset := size DivRemChip.Inputs
  have inputEq : Eval.eval env input =
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset DivRemChip.Inputs 0 env
  have outputEq : Eval.eval env ((DivRemChip.circuit (p := p)).output input offset) =
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  exact DivRemChip.eval_output_adapter input offset env

/-- DivRem's complete physical constraints force the non-`x0` routing flag, without invoking the
arithmetic `Spec` or any Memory assumption. -/
theorem DivRemChip.inputOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter.op_a_0 = 0 := by
  let input : Var DivRemChip.Inputs (ZMod p) := varFromOffset DivRemChip.Inputs 0
  let offset := size DivRemChip.Inputs
  let cols := DivRemChip.populatedRowAt input offset
  have rowConstraints : ((DivRemChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have coreFlat := constraintsHoldFlat_subcircuit_of_mem env
    ((DivRemChip.main input).operations offset)
    (DivRemCore.circuit.toSubcircuit (offset + 217) cols)
    (DivRemChip.divRemCore_mem input offset) rowConstraints
  have coreShallow : ConstraintsHold.Shallow env
      ((DivRemCore.main cols).operations (offset + 217)) := by
    apply FlatOperation.shallowConstraints_of_constraintsHoldFlat
    simpa only [DivRemCore.circuit, FormalAssertion.toSubcircuit,
      Operations.toNested_toFlat] using coreFlat
  have flagZero := DivRemChip.opA0_eq_zero_of_coreShallowConstraints env cols
    (offset + 217) coreShallow
  have inputEq : Eval.eval env input =
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset DivRemChip.Inputs 0 env
  rw [DivRemChip.populatedRowAt_adapter_eq] at flagZero
  rw [← inputEq, DivRemChip.eval_inputs, Readers.RTypeReader.eval_opA0]
  exact flagZero

/-- Row-view form of DivRem's physical routing assertion. -/
theorem DivRemChip.rowViewOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    (DivRemChip.rowView
      ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
      ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)).adapter.op_a_0 = 0 := by
  change ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_a_0 = 0
  rw [← DivRemChip.inputOutputAdapter env]
  exact DivRemChip.inputOpA0_eq_zero_of_constraints env constraints

/-! ## Physical row view and the ECALL opcode exclusion -/

/-- The completed DivRem columns at one physical component row. -/
noncomputable def DivRemChip.physicalCols (env : Environment (ZMod p)) :
    DivRemChip.Columns (ZMod p) :=
  (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env

/-- The completed DivRem row view at one physical component row. -/
noncomputable def DivRemChip.physicalView (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  DivRemChip.rowView
    ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    (DivRemChip.physicalCols env)

/-- The DivRemCore shallow tail forces the unconditional eight-flag sum `Σ flags = 1` (`E367`)
and the eight selector boolean gates, without touching the arithmetic evidence cluster. -/
private theorem DivRemChip.selectionFacts_of_coreShallowConstraints
    (env : Environment (ZMod p)) (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ)
    (shallow : ConstraintsHold.Shallow env ((DivRemCore.main cols).operations offset)) :
    Expression.eval env cols.is_divu + Expression.eval env cols.is_remu +
        Expression.eval env cols.is_div + Expression.eval env cols.is_rem +
        Expression.eval env cols.is_divw + Expression.eval env cols.is_remw +
        Expression.eval env cols.is_divuw + Expression.eval env cols.is_remuw = 1 ∧
      (Expression.eval env cols.is_divu = 0 ∨ Expression.eval env cols.is_divu = 1) ∧
      (Expression.eval env cols.is_remu = 0 ∨ Expression.eval env cols.is_remu = 1) ∧
      (Expression.eval env cols.is_div = 0 ∨ Expression.eval env cols.is_div = 1) ∧
      (Expression.eval env cols.is_rem = 0 ∨ Expression.eval env cols.is_rem = 1) ∧
      (Expression.eval env cols.is_divw = 0 ∨ Expression.eval env cols.is_divw = 1) ∧
      (Expression.eval env cols.is_remw = 0 ∨ Expression.eval env cols.is_remw = 1) ∧
      (Expression.eval env cols.is_divuw = 0 ∨ Expression.eval env cols.is_divuw = 1) ∧
      (Expression.eval env cols.is_remuw = 0 ∨ Expression.eval env cols.is_remuw = 1) := by
  simp only [DivRemCore.main, Circuit.operations, Circuit.bind_def, assertion,
    DivRemChip.assertZeros, Channel.pullIf, HasAssertEq.assert_eq,
    Expression.assertEquals, Operations.localLength] at shallow
  simp only [ConstraintsHold.Shallow, Operations.forAllNoOffset_append,
    Operations.forAllNoOffset, DivRemChip.forAllNoOffset_map_assert, true_and,
    and_true] at shallow
  have hsum : Expression.eval env ((1 : Expression (ZMod p)) -
      (cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem +
        cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw)) = 0 :=
    shallow _ (DivRemChip.flagsSum_mem_ownAsserts cols)
  have g0 : Expression.eval env (cols.is_divu * (cols.is_divu - 1)) = 0 :=
    shallow _ (DivRemChip.isDivu_gate_mem_ownAsserts cols)
  have g1 : Expression.eval env (cols.is_remu * (cols.is_remu - 1)) = 0 :=
    shallow _ (DivRemChip.isRemu_gate_mem_ownAsserts cols)
  have g2 : Expression.eval env (cols.is_div * (cols.is_div - 1)) = 0 :=
    shallow _ (DivRemChip.isDiv_gate_mem_ownAsserts cols)
  have g3 : Expression.eval env (cols.is_rem * (cols.is_rem - 1)) = 0 :=
    shallow _ (DivRemChip.isRem_gate_mem_ownAsserts cols)
  have g4 : Expression.eval env (cols.is_divw * (cols.is_divw - 1)) = 0 :=
    shallow _ (DivRemChip.isDivw_gate_mem_ownAsserts cols)
  have g5 : Expression.eval env (cols.is_remw * (cols.is_remw - 1)) = 0 :=
    shallow _ (DivRemChip.isRemw_gate_mem_ownAsserts cols)
  have g6 : Expression.eval env (cols.is_divuw * (cols.is_divuw - 1)) = 0 :=
    shallow _ (DivRemChip.isDivuw_gate_mem_ownAsserts cols)
  have g7 : Expression.eval env (cols.is_remuw * (cols.is_remuw - 1)) = 0 :=
    shallow _ (DivRemChip.isRemuw_gate_mem_ownAsserts cols)
  simp only [circuit_norm] at hsum g0 g1 g2 g3 g4 g5 g6 g7 ⊢
  exact ⟨by linear_combination -hsum, bool_of_mul_pred g0, bool_of_mul_pred g1,
    bool_of_mul_pred g2, bool_of_mul_pred g3, bool_of_mul_pred g4, bool_of_mul_pred g5,
    bool_of_mul_pred g6, bool_of_mul_pred g7⟩

/-- The eight one-hot selectors weight to an R-type discriminant that is never the `ECALL` value
`50`.  Stating the arithmetic over opaque field elements keeps the folded 217-cell witness row out of
the `push_cast`/`ring` atom normalisation, where projecting it is ruinously expensive. -/
private theorem DivRemChip.encodedOpcode_ne_ecall {f0 f1 f2 f3 f4 f5 f6 f7 : ZMod p}
    (b0 : f0 = 0 ∨ f0 = 1) (b1 : f1 = 0 ∨ f1 = 1) (b2 : f2 = 0 ∨ f2 = 1) (b3 : f3 = 0 ∨ f3 = 1)
    (b4 : f4 = 0 ∨ f4 = 1) (b5 : f5 = 0 ∨ f5 = 1) (b6 : f6 = 0 ∨ f6 = 1) (b7 : f7 = 0 ∨ f7 = 1)
    (hsum : f0 + f1 + f2 + f3 + f4 + f5 + f6 + f7 = 1) :
    f0 * 16 + f1 * 18 + f2 * 15 + f3 * 17 + f4 * 25 + f5 * 27 + f6 * 26 + f7 * 28 ≠
      (50 : ZMod p) := by
  have hvals := DivRemChip.flags_val_sum b0 b1 b2 b3 b4 b5 b6 b7 hsum
  intro h
  have hp := Fact.out (p := 2 ^ 17 < p)
  haveI : NeZero p := ⟨by omega⟩
  have hcast : f0 * 16 + f1 * 18 + f2 * 15 + f3 * 17 + f4 * 25 + f5 * 27 + f6 * 26 + f7 * 28 =
      ((f0.val * 16 + f1.val * 18 + f2.val * 15 + f3.val * 17 + f4.val * 25 + f5.val * 27 +
        f6.val * 26 + f7.val * 28 : ℕ) : ZMod p) := by
    push_cast [ZMod.natCast_zmod_val]
    ring
  rw [hcast] at h
  have hval := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by omega),
    show (50 : ZMod p) = ((50 : ℕ) : ZMod p) from by norm_cast,
    ZMod.val_natCast_of_lt (show (50 : ℕ) < p by omega)] at hval
  omega

/-- A real physical DivRem row's Program-bus opcode is never the `ECALL` discriminant `50`
(the committed-fragment re-base's per-chip strengthening fact). -/
theorem DivRemChip.physicalViewOpcode_ne_ecall (env : Environment (ZMod p))
    (constraints :
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (_real : (DivRemChip.physicalView env).is_real = 1) :
    (DivRemChip.physicalView env).opcode ≠ (50 : ZMod p) := by
  let input : Var DivRemChip.Inputs (ZMod p) := varFromOffset DivRemChip.Inputs 0
  let offset := size DivRemChip.Inputs
  let cols := DivRemChip.populatedRowAt input offset
  have rowConstraints : ((DivRemChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have coreFlat := constraintsHoldFlat_subcircuit_of_mem env
    ((DivRemChip.main input).operations offset)
    (DivRemCore.circuit.toSubcircuit (offset + 217) cols)
    (DivRemChip.divRemCore_mem input offset) rowConstraints
  have coreShallow : ConstraintsHold.Shallow env
      ((DivRemCore.main cols).operations (offset + 217)) := by
    apply FlatOperation.shallowConstraints_of_constraintsHoldFlat
    simpa only [DivRemCore.circuit, FormalAssertion.toSubcircuit,
      Operations.toNested_toFlat] using coreFlat
  obtain ⟨hsum, b0, b1, b2, b3, b4, b5, b6, b7⟩ :=
    DivRemChip.selectionFacts_of_coreShallowConstraints env cols (offset + 217) coreShallow
  have outputEq : Eval.eval env ((DivRemChip.circuit (p := p)).output input offset) =
      DivRemChip.physicalCols env := by
    simp only [input, offset, DivRemChip.physicalCols, Component.rowOutput, circuit_norm]
  have colsEval : DivRemChip.physicalCols env = Eval.eval env cols := by
    rw [← outputEq, DivRemChip.circuit_output_eq]
  have f0 : (DivRemChip.physicalCols env).is_divu = Expression.eval env cols.is_divu := by
    rw [colsEval, DivRemChip.eval_divRemCols_isDivu_verifier, CircuitType.eval_expr]
  have f1 : (DivRemChip.physicalCols env).is_remu = Expression.eval env cols.is_remu := by
    rw [colsEval, DivRemChip.eval_divRemCols_isRemu_verifier, CircuitType.eval_expr]
  have f2 : (DivRemChip.physicalCols env).is_div = Expression.eval env cols.is_div := by
    rw [colsEval, DivRemChip.eval_divRemCols_isDiv_verifier, CircuitType.eval_expr]
  have f3 : (DivRemChip.physicalCols env).is_rem = Expression.eval env cols.is_rem := by
    rw [colsEval, DivRemChip.eval_divRemCols_isRem_verifier, CircuitType.eval_expr]
  have f4 : (DivRemChip.physicalCols env).is_divw = Expression.eval env cols.is_divw := by
    rw [colsEval, DivRemChip.eval_divRemCols_isDivw_verifier, CircuitType.eval_expr]
  have f5 : (DivRemChip.physicalCols env).is_remw = Expression.eval env cols.is_remw := by
    rw [colsEval, DivRemChip.eval_divRemCols_isRemw_verifier, CircuitType.eval_expr]
  have f6 : (DivRemChip.physicalCols env).is_divuw = Expression.eval env cols.is_divuw := by
    rw [colsEval, DivRemChip.eval_divRemCols_isDivuw_verifier, CircuitType.eval_expr]
  have f7 : (DivRemChip.physicalCols env).is_remuw = Expression.eval env cols.is_remuw := by
    rw [colsEval, DivRemChip.eval_divRemCols_isRemuw_verifier, CircuitType.eval_expr]
  simp only [DivRemChip.physicalView, DivRemChip.rowView, DivRemContract.encodedOpcode]
  rw [f0, f1, f2, f3, f4, f5, f6, f7]
  exact DivRemChip.encodedOpcode_ne_ecall b0 b1 b2 b3 b4 b5 b6 b7 hsum

end SP1Clean.Soundness
