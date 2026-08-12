import SP1Clean.Soundness.TypedMemory

/-! # Add — circuit-grounding contracts

The first `CircuitGroundingContracts`-family per-chip file: closed-form evaluation and membership
facts connecting `AddChip.circuit`'s public Clean surface (the retained `main` interaction list and
the elaborated `circuit.output`) to the generic typed-Memory grounding layer.  Nothing here touches
the flattened `Component` projections — the single `rowOutput → circuit.output` identification
happens once, over abstract circuits, in `circuitRegisterOperandPullShape_of_exposure`
(`Soundness/TypedMemory.lean`), which keeps the kernel cost of these per-chip theorems low. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- Symbolic one-field equality constraint, factored so concrete row expressions are never unfolded
while the kernel checks the membership proof. -/
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

/-- Project Add's routing assertion while the circuit input remains opaque.  Keeping this type
symbolic prevents component-level callers from normalizing the entire concrete row during defeq. -/
private theorem addInputOpA0_eq_zero_of_mainConstraints
    (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env ((AddChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 := by
  have flagConstraint : Expression.eval env (input.adapter.op_a_0 - 0) = 0 := by
    apply constraints.1
    simp only [AddChip.main, circuit_norm]
    right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 0 _
  rw [eval_sub] at flagConstraint
  simpa only [Expression.eval] using sub_eq_zero.mp flagConstraint

-- This lemma and its `op_c` twin run at the plain default: the former 1000000 ceilings were ~25x
-- over; measured floors <= 40000.
omit [Fact (2 ^ 24 < p)] in
/-- Add's evaluated `op_b` reader index is the corresponding evaluated input projection. -/
theorem AddChip.eval_opB (env : Environment (ZMod p)) (input : Var AddChip.Inputs (ZMod p)) :
    Expression.eval env input.adapter.op_b = (Eval.eval env input).adapter.op_b := by
  rw [ProvableStruct.eval_var_eq_eval]
  have hAdapter : (ProvableStruct.eval env input).adapter = Eval.eval env input.adapter := rfl
  rw [hAdapter, ProvableStruct.eval_eq_eval]
  symm
  simp only [ProvableStruct.structEvalProjectionExpr]

omit [Fact (2 ^ 24 < p)] in
/-- Add's evaluated `op_c` reader index is the corresponding evaluated input projection. -/
theorem AddChip.eval_opC (env : Environment (ZMod p)) (input : Var AddChip.Inputs (ZMod p)) :
    Expression.eval env input.adapter.op_c = (Eval.eval env input).adapter.op_c := by
  rw [ProvableStruct.eval_var_eq_eval]
  have hAdapter : (ProvableStruct.eval env input).adapter = Eval.eval env input.adapter := rfl
  rw [hAdapter, ProvableStruct.eval_eq_eval]
  symm
  simp only [ProvableStruct.structEvalProjectionExpr]

omit [Fact (2 ^ 24 < p)] in
/-- Add's evaluated `op_b` prior word is the corresponding evaluated input projection. -/
theorem AddChip.eval_opBPrevValue (env : Environment (ZMod p))
    (input : Var AddChip.Inputs (ZMod p)) :
    Eval.eval env input.adapter.op_b_memory.prev_value =
      (Eval.eval env input).adapter.op_b_memory.prev_value := by
  rw [ProvableStruct.eval_var_eq_eval]
  have hAdapter : (ProvableStruct.eval env input).adapter = Eval.eval env input.adapter := rfl
  rw [hAdapter, ProvableStruct.eval_eq_eval]
  have hMemory : (ProvableStruct.eval env input.adapter).op_b_memory =
      Eval.eval env input.adapter.op_b_memory := rfl
  rw [hMemory, ProvableStruct.eval_eq_eval]
  rfl

omit [Fact (2 ^ 24 < p)] in
/-- Add's evaluated `op_c` prior word is the corresponding evaluated input projection. -/
theorem AddChip.eval_opCPrevValue (env : Environment (ZMod p))
    (input : Var AddChip.Inputs (ZMod p)) :
    Eval.eval env input.adapter.op_c_memory.prev_value =
      (Eval.eval env input).adapter.op_c_memory.prev_value := by
  rw [ProvableStruct.eval_var_eq_eval]
  have hAdapter : (ProvableStruct.eval env input).adapter = Eval.eval env input.adapter := rfl
  rw [hAdapter, ProvableStruct.eval_eq_eval]
  have hMemory : (ProvableStruct.eval env input.adapter).op_c_memory =
      Eval.eval env input.adapter.op_c_memory := rfl
  rw [hMemory, ProvableStruct.eval_eq_eval]
  rfl

/-- The native Add circuit passes its independent state input through to the output row. -/
theorem AddChip.inputOutputState (env : Environment (ZMod p)) :
    ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state =
      ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).state := by
  have inputEq : Eval.eval env (varFromOffset AddChip.Inputs 0) =
      ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset AddChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((AddChip.circuit (p := p)).output (varFromOffset AddChip.Inputs 0)
        (size AddChip.Inputs)) =
      ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  simp only [AddChip.circuit, circuit_norm]

/-- The native Add circuit passes its independent R-type adapter input through to the output row. -/
theorem AddChip.inputOutputAdapter (env : Environment (ZMod p)) :
    ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  have inputEq : Eval.eval env (varFromOffset AddChip.Inputs 0) =
      ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset AddChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((AddChip.circuit (p := p)).output (varFromOffset AddChip.Inputs 0)
        (size AddChip.Inputs)) =
      ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
    simp only [Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  simp only [AddChip.circuit, circuit_norm]

/-- Add's physical assertion system pins the canonical zero-register indicator to the non-`x0`
routing branch.  This is read from the complete flattened constraint list, independently of the
chip's semantic `Spec` and of any Memory-channel guarantee. -/
theorem AddChip.inputOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints : (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter.op_a_0 = 0 := by
  let input : Var AddChip.Inputs (ZMod p) := varFromOffset AddChip.Inputs 0
  let offset := size AddChip.Inputs
  have rowConstraints : Operations.ConstraintsHold env ((AddChip.main input).operations offset) :=
    (Component.constraintsHold_iff env).mp constraints
  have flagConstraint : Expression.eval env input.adapter.op_a_0 = 0 :=
    addInputOpA0_eq_zero_of_mainConstraints input offset env rowConstraints
  have inputEq : Eval.eval env input =
      (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset AddChip.Inputs 0 env
  rw [← inputEq, AddChip.eval_inputs, Readers.RTypeReader.eval_opA0]
  exact flagConstraint

/-- Row-view form of Add's physical routing constraint.  The circuit passes the adapter block through
unchanged, so the constraint on the input flag is the flag committed by the Program interaction. -/
theorem AddChip.rowViewOpA0_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints : (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    (AddChip.rowView
      ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
      ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)).adapter.op_a_0 = 0 := by
  change ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_a_0 = 0
  rw [← AddChip.inputOutputAdapter env]
  exact AddChip.inputOpA0_eq_zero_of_constraints env constraints

/-- Closed-form facts for Add's source-B register pull: the exact `RTypeReader` Memory pull is in
`main`'s retained interaction list, and its gate/index/prior-value expressions evaluate to the
semantic row view. -/
theorem AddChip.opBPullContract :
    DecodedInstructionRow.CircuitRegisterOperandPullContractAt
      (AddChip.circuit (p := p)) AddChip.rowView (fun input => input.is_real)
      (fun adapter => adapter.op_b[0]) (fun adapter => adapter.op_b_memory.prev_value) := by
  unfold DecodedInstructionRow.CircuitRegisterOperandPullContractAt
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => input.state.clk_high,
    fun input _ => input.adapter.op_b_memory.access_timestamp.prev_low,
    fun input _ => input.adapter.op_b,
    fun input _ => input.adapter.op_b_memory.prev_value, ?_, ?_, ?_, ?_⟩
  · intro input offset
    show _ ∈ ((AddChip.main input).operations offset).interactionsWith memoryChannel.toRaw
    rw [AddChip.interactionsWith_memory_eq]
    exact List.mem_map_of_mem (AddChip.opBPull_mem_exposedMemoryInteractions input offset)
  · intro env
    exact (AddChip.eval_isReal env _).symm
  · intro env
    simp only [AddChip.circuit, AddChip.rowView, Extracted.RTypeReader.toAdapterView, circuit_norm]
  · intro env
    simp only [AddChip.circuit, AddChip.rowView, Extracted.RTypeReader.toAdapterView, circuit_norm]

/-- Closed-form facts for Add's source-C register pull. -/
theorem AddChip.opCPullContract :
    DecodedInstructionRow.CircuitRegisterOperandPullContractAt
      (AddChip.circuit (p := p)) AddChip.rowView (fun input => input.is_real)
      (fun adapter => adapter.op_c[0]) (fun adapter => adapter.op_c_memory.prev_value) := by
  unfold DecodedInstructionRow.CircuitRegisterOperandPullContractAt
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => input.state.clk_high,
    fun input _ => input.adapter.op_c_memory.access_timestamp.prev_low,
    fun input _ => input.adapter.op_c,
    fun input _ => input.adapter.op_c_memory.prev_value, ?_, ?_, ?_, ?_⟩
  · intro input offset
    show _ ∈ ((AddChip.main input).operations offset).interactionsWith memoryChannel.toRaw
    rw [AddChip.interactionsWith_memory_eq]
    exact List.mem_map_of_mem (AddChip.opCPull_mem_exposedMemoryInteractions input offset)
  · intro env
    exact (AddChip.eval_isReal env _).symm
  · intro env
    simp only [AddChip.circuit, AddChip.rowView, Extracted.RTypeReader.toAdapterView, circuit_norm]
  · intro env
    simp only [AddChip.circuit, AddChip.rowView, Extracted.RTypeReader.toAdapterView, circuit_norm]

/-- Add's two source-register values are carried by the exact `RTypeReader` Memory pulls composed
into the chip.  This bundle is the template obligation for the other reader families. -/
theorem AddChip.registerOperandPullContract :
    DecodedInstructionRow.CircuitRegisterOperandPullContract
      (AddChip.circuit (p := p)) AddChip.rowView (fun input => input.is_real) :=
  ⟨AddChip.opBPullContract, AddChip.opCPullContract⟩

/-- Descriptor-level Add instance consumed by decoded rows and, eventually, the supported-chip
registry theorem. -/
theorem addChip_registerOperandPullShape_descriptor :
    DecodedInstructionRow.RegisterOperandPullShape
      (⟨AddChip.kind, AddChip.circuit, rfl, [.ADD], .nonX0⟩ : SupportedChip p) := by
  apply DecodedInstructionRow.registerOperandPullShape_of_circuitContract
    AddChip.kind AddChip.circuit rfl [.ADD] .nonX0 (fun input => input.is_real)
  · intro input output
    rfl
  · exact AddChip.registerOperandPullContract

end SP1Clean.Soundness
