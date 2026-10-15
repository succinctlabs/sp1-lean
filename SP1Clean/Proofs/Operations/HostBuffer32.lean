import SP1Clean.Native.Operations.HostBuffer32
import SP1Clean.Proofs.Operations.HostBuffer32.Content

/-! # Complete buffer soundness and completeness

All address arithmetic and offset selection are internal to the buffer proof. Its semantic
contract exposes the complete window, exact read keys, and returned host bytes.
-/

namespace SP1Clean.HostBuffer32

open Circuit SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_address (env : Environment (ZMod p))
    (cell : Var HostRamBytes.Inputs (ZMod p)) :
    cell.read.address.map (Expression.eval env) = (eval env cell).read.address := by
  rcases cell with ⟨⟨high, low, addr0, addr1, addr2, value⟩, lows⟩
  simp only [HostRamReadChip.Message.address, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_clock (env : Environment (ZMod p))
    (cell : Var HostRamBytes.Inputs (ZMod p)) :
    (env cell.read.clk_high, env cell.read.clk_low) =
      ((eval env cell).read.clk_high, (eval env cell).read.clk_low) := by
  rcases cell with ⟨⟨high, low, addr0, addr1, addr2, value⟩, lows⟩
  simp only [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_bytes (env : Environment (ZMod p))
    (cell : Var HostRamBytes.Inputs (ZMod p)) :
    (HostRamBytes.bytes (Expression.const (256 : ZMod p)⁻¹) cell).map (Expression.eval env) =
      HostRamBytes.bytes (256 : ZMod p)⁻¹ (eval env cell) := by
  rcases cell with ⟨⟨high, low, addr0, addr1, addr2, value⟩, lows⟩
  simp only [HostRamBytes.bytes, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_payload (env : Environment (ZMod p)) (offset : Fin 8)
    (vars : Vector (Var HostRamBytes.Inputs (ZMod p)) (cellCount offset))
    (values : Vector (HostRamBytes.Inputs (ZMod p)) (cellCount offset))
    (same : eval env vars = values) :
    (payload offset (Expression.const (256 : ZMod p)⁻¹) vars).map (Expression.eval env) =
      payload offset (256 : ZMod p)⁻¹ values := by
  ext index bound
  let cell := byteCell offset ⟨index, bound⟩
  have read := eval_vector_eq_get env vars values same cell.val cell.isLt
  have bytes := eval_bytes env vars[cell.val]
  rw [read] at bytes
  have byte := congrArg (fun word : Vector (ZMod p) 8 => word[(offset.val + index) % 8]) bytes
  simpa only [Vector.getElem_map, payload, Vector.getElem_ofFn, cell] using byte

theorem soundness (offset : Fin 8) : GeneralFormalCircuit.Soundness (Output := unit) (ZMod p)
    (main offset) (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start_core
  -- Normalize the loop separately: flattening an indexed nested row exceeds the default budget.
  change Spec input ∧ Operations.Requirements env ((main offset input_var).operations i₀)
  provable_struct_simp
  dsimp only [main, circuit_norm] at h_holds
  simp only [Operations.forAllNoOffset_append] at h_holds
  have loop := h_holds.1
  have tail := h_holds.2
  clear h_holds
  rw [forEach.forAllNoOffset] at loop
  simp only [circuit_norm, Gadgets.Equality.circuit] at tail
  have rows (index : Fin (cellCount offset)) := by
    have row := loop index
    simp only [Vector.getElem_finRange] at row
    dsimp only [Circuit.operations, Operations.forAllNoOffset] at row
    simp only [GeneralFormalCircuit.toSubcircuit_assumptions,
      GeneralFormalCircuit.toSubcircuit_soundness, FormalAssertion.toSubcircuit_assumptions,
      FormalAssertion.toSubcircuit_soundness] at row
    -- Keep clock expressions opaque while normalizing the equality subcircuit.
    generalize highEq : input_var_cells[index.val].read.clk_high = high at row
    generalize lowEq : input_var_cells[index.val].read.clk_low = low at row
    simp only [circuit_norm, HostRamBytes.circuit, Gadgets.Equality.circuit] at row
    rw [← highEq, ← lowEq] at row
    exact row
  clear loop
  have atCell (index : ℕ) (bound : index < cellCount offset) :
      eval env input_var_cells[index] = input_cells[index] :=
    eval_vector_eq_get env input_var_cells input_cells h_input.2 index bound
  have atPlain (index : ℕ) (bound : index < cellCount offset) :
      ProvableStruct.eval env input_var_cells[index] = input_cells[index] := by
    simpa only [ProvableStruct.eval_eq_eval] using atCell index bound
  have atAddress (index : ℕ) (bound : index < cellCount offset) :
      input_var_cells[index].read.address.map (Expression.eval env) = input_cells[index].read.address := by
    rw [eval_address, atCell index bound]
  have atClock (index : ℕ) (bound : index < cellCount offset) :
      (env input_var_cells[index].read.clk_high, env input_var_cells[index].read.clk_low) =
        (input_cells[index].read.clk_high, input_cells[index].read.clk_low) := by
    rw [eval_clock, atCell index bound]
  have atOffset (amount : ℕ) :
      ((wordOffset (p := p) amount).map Expression.const).map (Expression.eval env) = wordOffset amount := by
    simp only [circuit_norm, Vector.map_map, Function.comp_def, Expression.eval]
    exact Vector.map_id _
  have atBytes (index : ℕ) (bound : index < cellCount offset) :
      (HostRamBytes.bytes (Expression.const (256 : ZMod p)⁻¹) input_var_cells[index]).map
          (Expression.eval env) = HostRamBytes.bytes (256 : ZMod p)⁻¹ input_cells[index] := by
    rw [eval_bytes, atCell index bound]
  have messageAddress : input_var_message_address.map (Expression.eval env) = input_message_address :=
    by simpa only [circuit_norm] using h_input.1.2.2.1
  have messageBytes : input_var_message_bytes.map (Expression.eval env) = input_message_bytes :=
    by simpa only [circuit_norm] using h_input.1.2.2.2
  simp only [atPlain, atAddress, atClock, atOffset, atBytes, h_input.1.1, h_input.1.2.1] at rows
  simp only [atAddress, atOffset, messageAddress, messageBytes,
    eval_payload env offset _ _ h_input.2] at tail
  have base := (rows (start offset)).1.1
  have addition := tail.1 ⟨fun _ => ⟨base.1, isU64_bitVecToWord _⟩, Or.inr rfl⟩
  have checked := spec_of_cells offset
    (⟨⟨input_message_clk_high, input_message_clk_low, input_message_address, input_message_bytes⟩,
      input_cells⟩ : Inputs offset (ZMod p))
    (fun index => (rows index).1) (fun index => Prod.mk.inj (rows index).2.2)
    (fun index => by
      have step := (rows index).2.1 ⟨fun _ => ⟨base.1, isU64_bitVecToWord _⟩, Or.inr rfl⟩
      simpa only [wordOffset, toBitVec64_bitVecToWord] using (step rfl).2)
    (addition rfl).1
    (by simpa only [wordOffset, toBitVec64_bitVecToWord] using (addition rfl).2) tail.2
  refine ⟨checked, ?_⟩
  dsimp only [main, circuit_norm]
  rw [Operations.forAllNoOffset_append]
  constructor
  · rw [forEach.forAllNoOffset]
    intro index
    simp only [Vector.getElem_finRange]
    dsimp only [Circuit.operations, Operations.forAllNoOffset]
    exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, True.intro⟩
  · simp only [circuit_norm, channel]
    intro _ _
    simpa only [h_input.1.1, h_input.1.2.1, messageAddress, messageBytes] using checked.1

theorem completeness (offset : Fin 8) : GeneralFormalCircuit.Completeness (Output := unit) (ZMod p)
    (main offset) (fun input _ _ => ProverAssumptions offset input) (fun _ _ _ => True) := by
  circuit_proof_start_core
  provable_struct_simp
  refine ⟨?_, True.intro⟩
  clear h_env
  have atCell (index : ℕ) (bound : index < cellCount offset) :
      eval env.toEnvironment input_var_cells[index] = input_cells[index] :=
    eval_vector_eq_get env.toEnvironment input_var_cells input_cells h_input.2 index bound
  have atPlain (index : ℕ) (bound : index < cellCount offset) :
      ProvableStruct.eval env.toEnvironment input_var_cells[index] = input_cells[index] := by
    simpa only [ProvableStruct.eval_eq_eval] using atCell index bound
  have atAddress (index : ℕ) (bound : index < cellCount offset) :
      input_var_cells[index].read.address.map (Expression.eval env.toEnvironment) = input_cells[index].read.address := by
    rw [eval_address, atCell index bound]
  have atClock (index : ℕ) (bound : index < cellCount offset) :
      (env.toEnvironment input_var_cells[index].read.clk_high, env.toEnvironment input_var_cells[index].read.clk_low) =
        (input_cells[index].read.clk_high, input_cells[index].read.clk_low) := by
    rw [eval_clock, atCell index bound]
  have atOffset (amount : ℕ) :
      ((wordOffset (p := p) amount).map Expression.const).map (Expression.eval env.toEnvironment) = wordOffset amount := by
    simp only [circuit_norm, Vector.map_map, Function.comp_def, Expression.eval]
    exact Vector.map_id _
  have messageAddress : input_var_message_address.map (Expression.eval env.toEnvironment) = input_message_address :=
    by simpa only [circuit_norm] using h_input.1.2.2.1
  have messageBytes : input_var_message_bytes.map (Expression.eval env.toEnvironment) = input_message_bytes :=
    by simpa only [circuit_norm] using h_input.1.2.2.2
  dsimp only [main, circuit_norm]
  rw [Operations.forAllNoOffset_append]
  constructor
  · rw [forEach.forAllNoOffset]
    intro index
    simp only [Vector.getElem_finRange]
    dsimp only [Circuit.operations, Operations.forAllNoOffset]
    simp only [GeneralFormalCircuit.toSubcircuit_completeness,
      FormalAssertion.toSubcircuit_completeness]
    generalize highEq : input_var_cells[index.val].read.clk_high = high
    generalize lowEq : input_var_cells[index.val].read.clk_low = low
    simp only [circuit_norm, HostRamBytes.circuit, Gadgets.Equality.circuit]
    rw [← highEq, ← lowEq]
    simp only [atPlain, atAddress, atClock, atOffset, h_input.1.1, h_input.1.2.1]
    have cell := h_assumptions.1 index
    refine ⟨cell.1, ⟨⟨fun _ => ⟨(h_assumptions.1 (start offset)).1.1.1,
      isU64_bitVecToWord _⟩, Or.inr rfl⟩, ?_⟩, Prod.ext cell.2.1 cell.2.2.1⟩
    intro _
    refine ⟨cell.1.1.1, ?_⟩
    simpa only [wordOffset, toBitVec64_bitVecToWord] using cell.2.2.2
  · simp only [circuit_norm, Gadgets.Equality.circuit, channel]
    simp only [atAddress, atOffset, messageAddress, messageBytes,
      eval_payload env.toEnvironment offset _ _ h_input.2]
    refine ⟨⟨⟨fun _ => ⟨(h_assumptions.1 (start offset)).1.1.1,
      isU64_bitVecToWord _⟩, Or.inr rfl⟩, ?_⟩, h_assumptions.2.2.2⟩
    intro _
    refine ⟨h_assumptions.2.1, ?_⟩
    simpa only [wordOffset, toBitVec64_bitVecToWord] using h_assumptions.2.2.1

def circuit (offset : Fin 8) : GeneralFormalCircuit (ZMod p) (Inputs offset) unit where
  main := main offset
  elaborated := elaborated offset
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions offset input
  soundness := soundness offset
  completeness := completeness offset
  channelsWithRequirements := [channel.toRaw]
  requirementsChannelsLawful input n := by
    preserve_tactic_target
    refine ⟨?_, ?_, ?_⟩
    · simp only [main, circuit_norm]
    · simp only [main, circuit_norm]
    · intro env _
      rw [Operations.inChannelsOrRequirements_iff_forall_mem]
      have shallow : ((main offset input).operations n).shallowChannels = [channel.toRaw] := by
        simp only [main, circuit_norm]
      intro interaction member
      apply Or.inl
      rw [← shallow, Operations.shallowChannels_eq_interactions_map]
      exact List.mem_map.mpr ⟨interaction, member, rfl⟩

end SP1Clean.HostBuffer32
