import SP1Clean.Soundness.TypedState
import SP1Clean.Soundness.EnsembleChannels
import SP1Clean.Native.Operations.InstructionReceipt
import ToClean.Air.ComponentReplacement

/-! # Receipts reuse the registered ordinary State emissions

The neutral instruction identity selects only symbolic wiring in the original physical row.
There is no instruction evaluator, alternative decoder, or new execution inventory here.
The evaluated receipt is identified with the existing `statePushMessage` projection below.
-/

namespace SP1Clean.Soundness.OrdinaryStateReceipt

open Circuit Air.Flat Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Symbolic successor wiring for the existing instruction registry. -/
def projection : (id : InstructionChipId) →
    Receipt.Projection (ZMod p) (supportedChipFor (p := p) id).kind.Inputs StateMsg
  | .add => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .addi => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .addw => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .sub => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .subw => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .bitwise => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .lt => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .shiftLeft => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .shiftRight => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .jal => ⟨fun input _ => input.is_real,
      fun input offset => cpuStateNextMessage input.state #v[var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩] 8⟩
  | .jalr => ⟨fun input _ => input.is_real,
      fun input offset => cpuStateNextMessage input.state #v[var ⟨offset⟩ - var ⟨offset + 8⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩] 8⟩
  | .branch => ⟨fun input _ => input.is_real,
      fun input offset => cpuStateNextMessage input.state #v[var ⟨offset + 11⟩, var ⟨offset + 12⟩, var ⟨offset + 13⟩] 8⟩
  | .uType => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .loadByte => ⟨fun input _ => input.is_lb + input.is_lbu,
      fun input _ => cpuStatePushMessage input.state⟩
  | .loadHalf => ⟨fun input _ => input.is_lh + input.is_lhu,
      fun input _ => cpuStatePushMessage input.state⟩
  | .loadWord => ⟨fun input _ => input.is_lw + input.is_lwu,
      fun input _ => cpuStatePushMessage input.state⟩
  | .loadDouble => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .loadX0 => ⟨fun input _ => input.is_lb + input.is_lbu + input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld,
      fun input _ => cpuStatePushMessage input.state⟩
  | .storeByte => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .storeHalf => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .storeWord => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .storeDouble => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .mul => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .divRem => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩
  | .aluX0 => ⟨fun input _ => input.is_real,
      fun input _ => cpuStatePushMessage input.state⟩

/-- The existing circuit wrapped with its extra successor receipt. -/
def component (id : InstructionChipId) : Component (ZMod p) :=
  let chip := supportedChipFor (p := p) id
  letI := chip.kind.provableInputs
  letI := chip.kind.provableCols
  { circuit := InstructionReceipt.circuit chip.circuit (projection id) }

/-- Keep the descriptor's input representation available without unfolding the chip. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Inputs :=
  (supportedChipFor (p := p) id).kind.provableInputs
/-- Keep the descriptor's output representation available without unfolding the chip. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Cols :=
  (supportedChipFor (p := p) id).kind.provableCols

/-- Symbolic wiring agrees with the existing semantic view at every valid circuit offset. -/
def AgreesWith {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (provider : GeneralFormalCircuit (ZMod p) Input Output)
    (observation : Receipt.Projection (ZMod p) Input StateMsg)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  ∀ (input : Var Input (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)),
    Eval.eval env (observation.gate input offset) =
      (view (Eval.eval env input) (Eval.eval env (provider.output input offset))).is_real ∧
    Eval.eval env (observation.message input offset) =
      statePushOfView (view (Eval.eval env input) (Eval.eval env (provider.output input offset)))

/-- Every registered receipt uses the original activity gate and committed successor. -/
theorem projection_agrees (id : InstructionChipId) :
    let chip := supportedChipFor (p := p) id
    letI := chip.kind.provableInputs
    letI := chip.kind.provableCols
    AgreesWith chip.circuit (projection id) chip.kind.view := by
  cases id with
  | add =>
    change AgreesWith AddChip.circuit (projection .add) AddChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [AddChip.circuit, AddChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | addi =>
    change AgreesWith AddiChip.circuit (projection .addi) AddiChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [AddiChip.circuit, AddiChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | addw =>
    change AgreesWith AddwChip.circuit (projection .addw) AddwChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [AddwChip.circuit, AddwChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | sub =>
    change AgreesWith SubChip.circuit (projection .sub) SubChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [SubChip.circuit, SubChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | subw =>
    change AgreesWith SubwChip.circuit (projection .subw) SubwChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [SubwChip.circuit, SubwChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | bitwise =>
    change AgreesWith BitwiseChip.circuit (projection .bitwise) BitwiseChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [BitwiseChip.circuit, BitwiseChip.rowView, statePushOfView, stateAccess,
      cpuStatePushMessage, BitwiseChip.eval_isReal, circuit_norm]
  | lt =>
    change AgreesWith LtChip.circuit (projection .lt) LtChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [LtChip.circuit, LtChip.rowView, statePushOfView, stateAccess,
      cpuStatePushMessage, LtChip.eval_isReal, circuit_norm]
  | shiftLeft =>
    change AgreesWith ShiftLeftChip.circuit (projection .shiftLeft) ShiftLeftChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [ShiftLeftChip.circuit, ShiftLeftChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | shiftRight =>
    change AgreesWith ShiftRightChip.circuit (projection .shiftRight) ShiftRightChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [ShiftRightChip.circuit, ShiftRightChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | jal =>
    change AgreesWith JalChip.circuit (projection .jal) JalChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [JalChip.circuit, JalChip.rowView, statePushOfView, stateAccess, cpuStateNextMessage, circuit_norm]
  | jalr =>
    change AgreesWith JalrChip.circuit (projection .jalr) JalrChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [JalrChip.circuit, JalrChip.rowView, statePushOfView, stateAccess, cpuStateNextMessage, circuit_norm]
  | branch =>
    change AgreesWith BranchChip.circuit (projection .branch) BranchChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [BranchChip.circuit, BranchChip.rowView, statePushOfView, stateAccess, cpuStateNextMessage, circuit_norm]
  | uType =>
    change AgreesWith UTypeChip.circuit (projection .uType) UTypeChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [UTypeChip.circuit, UTypeChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | loadByte =>
    change AgreesWith LoadByteChip.circuit (projection .loadByte) LoadByteChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [LoadByteChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm, LoadByteChip.isReal]
  | loadHalf =>
    change AgreesWith LoadHalfChip.circuit (projection .loadHalf) LoadHalfChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [LoadHalfChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm, LoadHalfChip.isReal]
  | loadWord =>
    change AgreesWith LoadWordChip.circuit (projection .loadWord) LoadWordChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [LoadWordChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm, LoadWordChip.isReal]
  | loadDouble =>
    change AgreesWith LoadDoubleChip.circuit (projection .loadDouble) LoadDoubleChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [LoadDoubleChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | loadX0 =>
    change AgreesWith LoadX0Chip.circuit (projection .loadX0) LoadX0Chip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [LoadX0Chip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm, LoadX0Chip.isReal]
  | storeByte =>
    change AgreesWith StoreByteChip.circuit (projection .storeByte) StoreByteChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [StoreByteChip.circuit, StoreByteChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | storeHalf =>
    change AgreesWith StoreHalfChip.circuit (projection .storeHalf) StoreHalfChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [StoreHalfChip.circuit, StoreHalfChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | storeWord =>
    change AgreesWith StoreWordChip.circuit (projection .storeWord) StoreWordChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [StoreWordChip.circuit, StoreWordChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | storeDouble =>
    change AgreesWith StoreDoubleChip.circuit (projection .storeDouble) StoreDoubleChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [StoreDoubleChip.circuit, StoreDoubleChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | mul =>
    change AgreesWith MulChip.circuit (projection .mul) MulChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [MulChip.circuit, MulChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | divRem =>
    change AgreesWith DivRemChip.circuit (projection .divRem) DivRemChip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [DivRemChip.circuit, DivRemChip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]
  | aluX0 =>
    change AgreesWith AluX0Chip.circuit (projection .aluX0) AluX0Chip.rowView
    intro input offset env
    dsimp only [projection]
    simp only [AluX0Chip.circuit, AluX0Chip.rowView, statePushOfView, stateAccess, cpuStatePushMessage, circuit_norm]

/-- Existing ordinary circuits cannot already emit on the new observation channel. -/
theorem original_silent (id : InstructionChipId) :
    InstructionReceipt.channel.toRaw ∉ (supportedChipFor (p := p) id).circuit.channels := by
  have member : (supportedChipFor (p := p) id).table ∈ sp1Tables :=
    List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨id, InstructionChipId.mem_all id, rfl⟩, rfl⟩
  have inside := sp1Tables_channels_subset _ member
  intro present
  have used := inside present
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false] at used
  rcases used with used | used | used | used | used <;>
    have names := congrArg (fun channel => channel.name == "SP1OrdinaryStateReceipt") used <;>
    exact Bool.noConfusion names

omit [Fact (2 ^ 24 < p)] in
/-- Symbolic agreement identifies the observation in the original physical row. -/
theorem row_meaning {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (provider : GeneralFormalCircuit (ZMod p) Input Output)
    (observation : Receipt.Projection (ZMod p) Input StateMsg)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (agrees : AgreesWith provider observation view) (env : Environment (ZMod p)) :
    let original : Component (ZMod p) := { circuit := provider }
    Eval.eval env (observation.gate (varFromOffset Input 0) (size Input)) =
      (view (original.rowInput env) (original.rowOutput env)).is_real ∧
    Eval.eval env (observation.message (varFromOffset Input 0) (size Input)) =
      statePushOfView (view (original.rowInput env) (original.rowOutput env)) := by
  have result := agrees (varFromOffset Input 0) (size Input) env
  simpa only [Component.rowInput, Component.rowOutput, circuit_norm,
    eval_varFromOffset_valueFromOffset] using result

/-- Every physical receipt is exactly the successor of the existing decoded instruction row.
No constraints or claimed semantic observations are needed to identify the wiring. -/
theorem row_receipt (id : InstructionChipId) (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (component id).operations.interactionValuesWith InstructionReceipt.channel.toRaw
      (Environment.fromArray physical data) =
        [InstructionReceipt.channel.pushedIfValue
          ((supportedChipFor (p := p) id).decodeRow data physical).is_real
          (statePushMessage ((supportedChipFor (p := p) id).decodeRow data physical))] := by
  let chip := supportedChipFor (p := p) id
  have meaning := row_meaning chip.circuit (projection id) chip.kind.view
    (projection_agrees id) (Environment.fromArray physical data)
  rw [show (component id).operations.interactionValuesWith InstructionReceipt.channel.toRaw
      (Environment.fromArray physical data) = _ from
    Receipt.row_receipt chip.circuit InstructionReceipt.channel (fun _ _ => trivial)
      (projection id) (original_silent id) (Environment.fromArray physical data), meaning.1, meaning.2]
  rfl

/-- Receipt wrapping retains the complete original assertion system. -/
theorem constraints (id : InstructionChipId) : (component (p := p) id).operations.constraints =
    (supportedChipFor (p := p) id).table.operations.constraints :=
  Receipt.constraints _ _ _ _

/-- Receipt wrapping retains every fixed lookup. -/
theorem lookups (id : InstructionChipId) : (component (p := p) id).operations.lookups =
    (supportedChipFor (p := p) id).table.operations.lookups :=
  Receipt.lookups _ _ _ _

/-- Original row constructors still fit the exact same physical width. -/
theorem width (id : InstructionChipId) : (component (p := p) id).width =
    (supportedChipFor (p := p) id).table.width :=
  Receipt.width _ _ _ _

/-- All original ledgers are retained literally. -/
theorem interactions (id : InstructionChipId) (selected : RawChannel (ZMod p))
    (different : selected ≠ InstructionReceipt.channel.toRaw) :
    (component id).operations.interactionsWith selected =
      (supportedChipFor (p := p) id).table.operations.interactionsWith selected :=
  Receipt.interactions _ _ _ _ selected different

/-- Publish receipts on a registered component's existing rows, preserving their layout. -/
def construct (id : InstructionChipId) (original : Table (ZMod p))
    (registered : original.component = (supportedChipFor id).table) : Table (ZMod p) :=
  original.withComponent (component id) (by rw [registered]; exact width id)
    (by rw [registered]; rfl)

/-- The constructor preserves raw row validity in both directions at the same ensemble data. -/
theorem construct_constraints (id : InstructionChipId) (original : Table (ZMod p))
    (registered : original.component = (supportedChipFor id).table) (data : ProverData (ZMod p)) :
    (construct id original registered).Constraints data ↔ original.Constraints data := by
  apply Table.withComponent_constraints
  · rw [registered, constraints]
  · rw [registered, lookups]

/-- The constructed table has exactly the original physical height. -/
theorem construct_length (id : InstructionChipId) (original : Table (ZMod p))
    (registered : original.component = (supportedChipFor id).table) :
    (construct id original registered).length = original.length := rfl

/-- The full receipt ledger is decoded directly from the original arrays and shared data. -/
theorem construct_receipts (id : InstructionChipId) (original : Table (ZMod p))
    (registered : original.component = (supportedChipFor id).table) (data : ProverData (ZMod p)) :
    (construct id original registered).interactionsWith data InstructionReceipt.channel.toRaw =
      original.table.map (fun physical =>
        let row := (supportedChipFor (p := p) id).decodeRow data physical
        InstructionReceipt.channel.pushedIfValue row.is_real (statePushMessage row)) := by
  simp only [construct, Table.interactionsWith, Table.withComponent, row_receipt]
  exact List.map_eq_flatMap.symm

/-- Exact cost includes the inactive occurrence on every padding row. -/
theorem construct_receipt_count (id : InstructionChipId) (original : Table (ZMod p))
    (registered : original.component = (supportedChipFor id).table) (data : ProverData (ZMod p)) :
    ((construct id original registered).interactionsWith data InstructionReceipt.channel.toRaw).length =
      original.length := by
  rw [construct_receipts, List.length_map]

end SP1Clean.Soundness.OrdinaryStateReceipt
