import SP1Clean.Soundness.TypedMemory

/-! # Exact Memory operand contracts for supported instruction chips

This module proves the small interaction-shape facts that connect each retained chip circuit to the
generic timed-Memory grounding layer.  These are chip-boundary theorems over the circuits' actual
evaluated Clean interactions, not operation-level faithfulness bridges or a parallel lookup model.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

set_option maxHeartbeats 1000000 in
omit [Fact (2 ^ 24 < p)] in
/-- Evaluate the canonical register-shaped Memory pull without unfolding a concrete chip input. -/
theorem eval_registerMemoryMessage (env : Environment (ZMod p))
    (clkHigh prevLow index : Expression (ZMod p)) (value : Word (Expression (ZMod p))) :
    Eval.eval env (⟨clkHigh, prevLow, index, 0, 0, value⟩ : MemoryMsg (Expression (ZMod p))) =
      (⟨Expression.eval env clkHigh, Expression.eval env prevLow, Expression.eval env index,
        0, 0, Eval.eval env value⟩ : MemoryMsg (ZMod p)) := by
  rw [ProvableStruct.eval_eq_eval]
  simp only [ProvableStruct.structEvalLiteralProc, Expression.eval]

/-- Package an active canonical register pull into the operand witness expected by the chip-level
contract.  Keeping this dependent-record assembly generic prevents concrete completed circuits from
being unfolded while Lean unifies the `MemoryMsg` projections. -/
theorem registerPullWitness_of_registerMessage
    (interactions : List (TypedInteraction (memoryChannel (p := p))))
    (clkHigh prevLow addr0 : ZMod p) (value expected : Word (ZMod p))
    (member : (⟨clkHigh, prevLow, addr0, 0, 0, value⟩ : MemoryMsg (ZMod p)) ∈
      consumedMessages interactions)
    (index : BitVec 5) (indexEq : (index.toNat : ZMod p) = addr0)
    (valueEq : value = expected) :
    ∃ message ∈ consumedMessages interactions,
      Semantics.MemoryMsg.locOf message = Semantics.MemLoc.reg index ∧
      message.value = expected := by
  let message : MemoryMsg (ZMod p) := ⟨clkHigh, prevLow, addr0, 0, 0, value⟩
  refine ⟨message, member, ?_, valueEq⟩
  exact Semantics.MemoryMsg.locOf_register message index indexEq rfl rfl

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

/-- Add's flattened component retains exactly the Memory list declared through `exposedChannels`. -/
theorem AddChip.componentInteractionsWith_memory_eq :
    (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionsWith
        memoryChannel.toRaw =
      (AddChip.exposedMemoryInteractions (varFromOffset AddChip.Inputs 0)
        (size AddChip.Inputs)).map ChannelInteraction.toRaw := by
  rw [Component.interactionsWith_eq]
  exact AddChip.interactionsWith_memory_eq _ _

set_option maxHeartbeats 2000000 in
/-- Transport Add's row-local source-B pull to the flattened component interaction list once. -/
theorem AddChip.eval_opBPull_mem_componentConsumed (env : Environment (ZMod p))
    (input : Var AddChip.Inputs (ZMod p))
    (input_eq : input = varFromOffset AddChip.Inputs 0)
    (active : Expression.eval env input.is_real = 1) :
    Eval.eval env
        (⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
          input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ :
          MemoryMsg (Expression (ZMod p))) ∈
      consumedMessages (typedInteractionValuesWith
        (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).operations memoryChannel env) := by
  subst input
  apply eval_pulledIf_message_mem_consumedMessages
    (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).operations memoryChannel env
    (varFromOffset AddChip.Inputs 0).is_real _
  · rw [AddChip.componentInteractionsWith_memory_eq]
    exact List.mem_map_of_mem (AddChip.opBPull_mem_exposedMemoryInteractions _ _)
  · have := Fact.out (p := 2 ^ 24 < p)
    omega
  · exact active

set_option maxHeartbeats 2000000 in
/-- Transport Add's row-local source-C pull to the flattened component interaction list once. -/
theorem AddChip.eval_opCPull_mem_componentConsumed (env : Environment (ZMod p))
    (input : Var AddChip.Inputs (ZMod p))
    (input_eq : input = varFromOffset AddChip.Inputs 0)
    (active : Expression.eval env input.is_real = 1) :
    Eval.eval env
        (⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
          input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩ :
          MemoryMsg (Expression (ZMod p))) ∈
      consumedMessages (typedInteractionValuesWith
        (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).operations memoryChannel env) := by
  subst input
  apply eval_pulledIf_message_mem_consumedMessages
    (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).operations memoryChannel env
    (varFromOffset AddChip.Inputs 0).is_real _
  · rw [AddChip.componentInteractionsWith_memory_eq]
    exact List.mem_map_of_mem (AddChip.opCPull_mem_exposedMemoryInteractions _ _)
  · have := Fact.out (p := 2 ^ 24 < p)
    omega
  · exact active

set_option maxHeartbeats 4000000 in
/-- Add's source-B value is carried by the exact `RTypeReader` Memory pull composed into the chip. -/
theorem addChip_opBPull :
    DecodedInstructionRow.CircuitRegisterOperandPullAt
      (AddChip.circuit (p := p)) AddChip.rowView (fun input => input.is_real)
      AddChip.kind.advanceReady (fun adapter => adapter.imm_b)
      (fun adapter => adapter.op_b[0]) (fun adapter => adapter.op_b_memory.prev_value) := by
  intro data physical rowView
  dsimp only
  intro program state viewEq ready
  let component : Component (ZMod p) := ⟨AddChip.circuit⟩
  let env := Environment.fromArray physical data
  let input : Var AddChip.Inputs (ZMod p) := varFromOffset AddChip.Inputs 0
  have inputEq : Eval.eval env input = component.rowInput env :=
    eval_varFromOffset_valueFromOffset AddChip.Inputs 0 env
  have adapterEq : (component.rowOutput env).adapter = (component.rowInput env).adapter := by
    change (component.rowInput env).adapter = (component.rowOutput env).adapter ∧ _ at ready
    exact ready.1.symm
  have viewAdapterEq : rowView.adapter = (component.rowOutput env).adapter.toAdapterView := by
    rw [viewEq]
    rfl
  intro real
  have real' : Expression.eval env input.is_real = 1 := by
    calc
      _ = (Eval.eval env input).is_real := (AddChip.eval_isReal env input).symm
      _ = (component.rowInput env).is_real := congrArg (fun value => value.is_real) inputEq
      _ = 1 := real
  intro index _immediate indexEq
  have addr0 : (index.toNat : ZMod p) = Expression.eval env input.adapter.op_b := by
    rw [viewAdapterEq] at indexEq
    change (index.toNat : ZMod p) = (component.rowOutput env).adapter.op_b at indexEq
    rw [adapterEq, ← inputEq] at indexEq
    exact indexEq.trans (AddChip.eval_opB env input).symm
  have priorValue : Eval.eval env input.adapter.op_b_memory.prev_value =
      rowView.adapter.op_b_memory.prev_value := by
    rw [viewAdapterEq]
    change Eval.eval env input.adapter.op_b_memory.prev_value =
      (component.rowOutput env).adapter.op_b_memory.prev_value
    rw [adapterEq, ← inputEq]
    exact AddChip.eval_opBPrevValue env input
  let messageExpr : MemoryMsg (Expression (ZMod p)) :=
    ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
      input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩
  have messageEq : Eval.eval env messageExpr =
      (⟨Expression.eval env input.state.clk_high,
        Expression.eval env input.adapter.op_b_memory.access_timestamp.prev_low,
        Expression.eval env input.adapter.op_b, 0, 0,
        Eval.eval env input.adapter.op_b_memory.prev_value⟩ : MemoryMsg (ZMod p)) :=
    eval_registerMemoryMessage env _ _ _ _
  have messageMem :
      (⟨Expression.eval env input.state.clk_high,
        Expression.eval env input.adapter.op_b_memory.access_timestamp.prev_low,
        Expression.eval env input.adapter.op_b, 0, 0,
        Eval.eval env input.adapter.op_b_memory.prev_value⟩ : MemoryMsg (ZMod p)) ∈
      consumedMessages (typedInteractionValuesWith component.operations memoryChannel env) := by
    rw [← messageEq]
    simpa only [messageExpr, component] using
      AddChip.eval_opBPull_mem_componentConsumed env input rfl real'
  exact registerPullWitness_of_registerMessage _ _ _ _ _ _ messageMem index addr0 priorValue

set_option maxHeartbeats 4000000 in
/-- Add's source-C value is carried by the exact `RTypeReader` Memory pull composed into the chip. -/
theorem addChip_opCPull :
    DecodedInstructionRow.CircuitRegisterOperandPullAt
      (AddChip.circuit (p := p)) AddChip.rowView (fun input => input.is_real)
      AddChip.kind.advanceReady (fun adapter => adapter.imm_c)
      (fun adapter => adapter.op_c[0]) (fun adapter => adapter.op_c_memory.prev_value) := by
  intro data physical rowView
  dsimp only
  intro program state viewEq ready
  let component : Component (ZMod p) := ⟨AddChip.circuit⟩
  let env := Environment.fromArray physical data
  let input : Var AddChip.Inputs (ZMod p) := varFromOffset AddChip.Inputs 0
  have inputEq : Eval.eval env input = component.rowInput env :=
    eval_varFromOffset_valueFromOffset AddChip.Inputs 0 env
  have adapterEq : (component.rowOutput env).adapter = (component.rowInput env).adapter := by
    change (component.rowInput env).adapter = (component.rowOutput env).adapter ∧ _ at ready
    exact ready.1.symm
  have viewAdapterEq : rowView.adapter = (component.rowOutput env).adapter.toAdapterView := by
    rw [viewEq]
    rfl
  intro real
  have real' : Expression.eval env input.is_real = 1 := by
    calc
      _ = (Eval.eval env input).is_real := (AddChip.eval_isReal env input).symm
      _ = (component.rowInput env).is_real := congrArg (fun value => value.is_real) inputEq
      _ = 1 := real
  intro index _immediate indexEq
  have addr0 : (index.toNat : ZMod p) = Expression.eval env input.adapter.op_c := by
    rw [viewAdapterEq] at indexEq
    change (index.toNat : ZMod p) = (component.rowOutput env).adapter.op_c at indexEq
    rw [adapterEq, ← inputEq] at indexEq
    exact indexEq.trans (AddChip.eval_opC env input).symm
  have priorValue : Eval.eval env input.adapter.op_c_memory.prev_value =
      rowView.adapter.op_c_memory.prev_value := by
    rw [viewAdapterEq]
    change Eval.eval env input.adapter.op_c_memory.prev_value =
      (component.rowOutput env).adapter.op_c_memory.prev_value
    rw [adapterEq, ← inputEq]
    exact AddChip.eval_opCPrevValue env input
  let messageExpr : MemoryMsg (Expression (ZMod p)) :=
    ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
      input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩
  have messageEq : Eval.eval env messageExpr =
      (⟨Expression.eval env input.state.clk_high,
        Expression.eval env input.adapter.op_c_memory.access_timestamp.prev_low,
        Expression.eval env input.adapter.op_c, 0, 0,
        Eval.eval env input.adapter.op_c_memory.prev_value⟩ : MemoryMsg (ZMod p)) :=
    eval_registerMemoryMessage env _ _ _ _
  have messageMem :
      (⟨Expression.eval env input.state.clk_high,
        Expression.eval env input.adapter.op_c_memory.access_timestamp.prev_low,
        Expression.eval env input.adapter.op_c, 0, 0,
        Eval.eval env input.adapter.op_c_memory.prev_value⟩ : MemoryMsg (ZMod p)) ∈
      consumedMessages (typedInteractionValuesWith component.operations memoryChannel env) := by
    rw [← messageEq]
    simpa only [messageExpr, component] using
      AddChip.eval_opCPull_mem_componentConsumed env input rfl real'
  exact registerPullWitness_of_registerMessage _ _ _ _ _ _ messageMem index addr0 priorValue

/-- Add's two source-register values are carried by the exact `RTypeReader` Memory pulls composed
into the chip.  This is the template for the other reader families. -/
theorem addChip_registerOperandPullShape :
    DecodedInstructionRow.CircuitRegisterOperandPullShape
      (AddChip.circuit (p := p)) AddChip.rowView (fun input => input.is_real)
        AddChip.kind.advanceReady :=
  ⟨addChip_opBPull, addChip_opCPull⟩

/-- Descriptor-level Add instance consumed by decoded rows and, eventually, the supported-chip
registry theorem. -/
theorem addChip_registerOperandPullShape_descriptor :
    DecodedInstructionRow.RegisterOperandPullShape
      (⟨AddChip.kind, AddChip.circuit, rfl, [.ADD], .nonX0⟩ : SupportedChip p) := by
  apply DecodedInstructionRow.registerOperandPullShape_of_circuit
    AddChip.kind AddChip.circuit rfl [.ADD] .nonX0 (fun input => input.is_real)
  · intro input output
    rfl
  · exact addChip_registerOperandPullShape

end SP1Clean.Soundness
