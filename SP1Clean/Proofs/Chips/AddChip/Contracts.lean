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

set_option maxHeartbeats 1000000 in
omit [Fact (2 ^ 24 < p)] in
/-- Add's evaluated `op_b` reader index is the corresponding evaluated input projection. -/
theorem AddChip.eval_opB (env : Environment (ZMod p)) (input : Var AddChip.Inputs (ZMod p)) :
    Expression.eval env input.adapter.op_b = (Eval.eval env input).adapter.op_b := by
  rw [ProvableStruct.eval_var_eq_eval]
  have hAdapter : (ProvableStruct.eval env input).adapter = Eval.eval env input.adapter := rfl
  rw [hAdapter, ProvableStruct.eval_eq_eval]
  symm
  simp only [ProvableStruct.structEvalProjectionExpr]

set_option maxHeartbeats 1000000 in
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
