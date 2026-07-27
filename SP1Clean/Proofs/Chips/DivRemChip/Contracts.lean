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
  right
  left
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
  right
  right
  right
  left
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
  rw [DivRemChip.circuit_output_eq]
  rw [DivRemChip.eval_inputs, DivRemChip.eval_divRemCols_adapter_verifier,
    DivRemChip.populatedRowAt_adapter_eq]

/-- DivRem's direct output passes the independent CPU-state block through unchanged. -/
theorem DivRemChip.eval_output_state (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) :
    (Eval.eval env input).state =
      (Eval.eval env ((DivRemChip.circuit (p := p)).output input offset)).state := by
  rw [DivRemChip.circuit_output_eq]
  rw [DivRemChip.eval_inputs, DivRemChip.eval_divRemCols_state_verifier,
    DivRemChip.populatedRowAt_state_eq]

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

end SP1Clean.Soundness
