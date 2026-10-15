import SP1Clean.Soundness.HostSailBoundary
import SP1Clean.Soundness.ProtectedOrdinaryReceipt

/-! # Install ordinary receipt producers in the existing mixed assembly

Only the 25 instruction components change. They retain all original row arrays, constraints,
lookups and ledgers, including each store's byte-permission requests. Complete Memory checks,
host resources and the supplied Sail frame remain installed. The resource block can contain
the ordered observation consumer; authentic endpoints and its full Byte closure are subsequent
integration obligations. This producer installation alone is not an end-to-end capstone.
-/

namespace SP1Clean.Soundness.HostOrdinaryReceipts

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance receiptClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The physical registration retains the original input representation. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Inputs :=
  (supportedChipFor (p := p) id).kind.provableInputs
/-- The physical registration retains the original output representation. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Cols :=
  (supportedChipFor (p := p) id).kind.provableCols

/-- The original registration order selects the receipt-bearing protected instruction. -/
def replace (index : ℕ) (original : Component (ZMod p)) : Component (ZMod p) :=
  if within : 7 ≤ index ∧ index < 32 then
    ProtectedOrdinaryReceipt.component
      (InstructionChipId.all[index - 7]'(by rw [InstructionChipId.all_length]; omega))
  else original

variable {image : ProgramImage} {source target : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : HostFinalMemory.UniqueNames image source target.sail.memorySnapshot others resources}

private theorem base_length :
    (HostSailBoundary.ensemble (p := p) image source target final others resources channels names).tables.length =
      69 + others.length + resources.length := by
  simp only [HostSailBoundary.ensemble, PublicVerifier.install, HostFinalMemory.ensemble,
    ClosedVerifier.install, HostFinalMemory.withReceipts, HostFinalMemory.withRegisters,
    FinalReceiptEnsemble.install, Ensemble.replaceComponent, List.length_set, HostFinalMemory.base_tables_length]

private theorem protected_component (index : Fin 25) :
    (ProtectedLocalCore.tables (p := p) image source)[7 + index.val]'(by
      rw [ProtectedLocalCore.tables_length]; omega) =
        { circuit := ProtectedOrdinaryReceipt.provider (InstructionChipId.all[index.val]'(by
          rw [InstructionChipId.all_length]; exact index.isLt)) } := by
  rw [ProtectedLocalCore.tables_getElem image source (7 + index.val) (by omega)]
  fin_cases index <;> rfl

/-- Static registration identifies the actual protected instructions below all endpoint wrappers. -/
theorem original_component (index : Fin 25) :
    (HostSailBoundary.ensemble (p := p) image source target final others resources channels names).tables[7 + index.val]'(by
      rw [base_length]
      omega) =
      { circuit := ProtectedOrdinaryReceipt.provider (InstructionChipId.all[index.val]'(by
        rw [InstructionChipId.all_length]; exact index.isLt)) } := by
  change (HostFinalMemory.ensemble image source target.sail.memorySnapshot final target.host
    others resources channels names).tables[7 + index.val]'_ = _
  simp only [HostFinalMemory.tables_eq]
  rw [List.getElem_set_ne (by omega : 4 ≠ 7 + index.val),
    List.getElem_set_ne (by omega : 3 ≠ 7 + index.val),
    List.getElem_set_ne (by have := index.isLt; omega : 57 ≠ 7 + index.val)]
  rw [List.getElem_append_left (by rw [HostFinalMemory.prefix_length]; have := index.isLt; omega)]
  simp only [HostFinalMemory.beforeChecks]
  rw [HostLocalCore.core_component image source _ ⟨7 + index.val, by omega⟩,
    if_neg (by have := index.isLt; omega : 58 ≠ 7 + index.val)]
  exact protected_component index

private theorem replacement_layout
    (index : Fin (HostSailBoundary.ensemble (p := p) image source target final others resources channels names).tables.length) :
    let original := (HostSailBoundary.ensemble image source target final others resources channels names).tables[index.val]
    let extended := replace index.val original
    extended.circuit.name = original.circuit.name ∧
      extended.width = original.width ∧ extended.fixedColumns = original.fixedColumns ∧
        ∀ rows arity, extended.proverRows rows arity = original.proverRows rows arity := by
  dsimp only
  by_cases within : 7 ≤ index.val ∧ index.val < 32
  · rw [show replace index.val _ = ProtectedOrdinaryReceipt.component
        (InstructionChipId.all[index.val - 7]'(by rw [InstructionChipId.all_length]; omega)) from dif_pos within]
    have selected := original_component (image := image) (source := source) (target := target)
      (final := final) (others := others) (resources := resources) (channels := channels) (names := names)
      ⟨index.val - 7, by omega⟩
    simp only [show 7 + (index.val - 7) = index.val by omega] at selected
    rw [selected]
    exact ⟨rfl, ProtectedOrdinaryReceipt.width _, rfl, fun _ _ => rfl⟩
  · rw [show replace index.val _ = _ from dif_neg within]
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Install the producers without moving or removing any physical table. -/
def ensemble (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p))
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : HostFinalMemory.UniqueNames image source target.sail.memorySnapshot others resources) : Ensemble (ZMod p) SP1PublicIO :=
  let base := HostSailBoundary.ensemble image source target final others resources channels names
  { base with tables := base.tables.mapIdx replace
              channels := base.channels ++ [InstructionReceipt.channel.toRaw]
              unique_names := by
                have unchanged : (base.tables.mapIdx replace).map (·.circuit.name) =
                    base.tables.map (·.circuit.name) := by
                  apply List.ext_getElem
                  · simp only [List.length_map, List.length_mapIdx]
                  · intro index left right
                    rw [List.getElem_map, List.getElem_map, List.getElem_mapIdx]
                    exact (replacement_layout (image := image) (source := source) (target := target)
                      (final := final) (others := others) (resources := resources) (channels := channels) (names := names)
                      ⟨index, by simpa only [List.length_map] using right⟩).1
                rw [unchanged]
                exact base.unique_names }

/-- Receipt publication adds no tables. -/
theorem tables_length :
    (ensemble (p := p) image source target final others resources channels names).tables.length =
      (HostSailBoundary.ensemble image source target final others resources channels names).tables.length :=
  by simp only [ensemble, List.length_mapIdx]

/-- Each instruction retains its original physical position under a typed receipt registration. -/
def slot (index : Fin 25) : TableSlot
    (ensemble (p := p) image source target final others resources channels names).tables
    (ProtectedOrdinaryReceipt.component (InstructionChipId.all[index.val]'(by
      rw [InstructionChipId.all_length]; exact index.isLt))) where
  index := ⟨7 + index.val, by rw [tables_length, base_length]; omega⟩
  component_eq := by
    simp only [ensemble, List.getElem_mapIdx, replace,
      show 7 ≤ 7 + index.val ∧ 7 + index.val < 32 by omega, and_self, ↓reduceDIte,
      Nat.add_sub_cancel_left]

/-- Read the literal receipt-bearing instruction table through its typed registration. -/
def instructionTable (index : Fin 25)
    (witness : EnsembleWitness (ensemble image source target final others resources channels names)) : Table (ZMod p) :=
  (slot index).table witness

/-- Installed receipts use the sole existing decoder on the actual physical table arrays. -/
theorem instructionTable_receipts (index : Fin 25)
    (witness : EnsembleWitness (ensemble image source target final others resources channels names)) :
    (instructionTable index witness).interactionsWith witness.data InstructionReceipt.channel.toRaw =
      (instructionTable index witness).table.map (fun physical =>
        let row := (supportedChipFor (p := p) (InstructionChipId.all[index.val]'(by
          rw [InstructionChipId.all_length]; exact index.isLt))).decodeRow witness.data physical
        InstructionReceipt.channel.pushedIfValue row.is_real (statePushMessage row)) := by
  have registered := (slot (image := image) (source := source) (target := target) (final := final)
    (others := others) (resources := resources) (channels := channels) (names := names) index).table_component witness
  change (instructionTable index witness).component = _ at registered
  simp only [Table.interactionsWith, registered, ProtectedOrdinaryReceipt.row_receipt]
  exact List.map_eq_flatMap.symm

/-- Physical cost includes every disabled padding occurrence. -/
theorem instructionTable_receipt_count (index : Fin 25)
    (witness : EnsembleWitness (ensemble image source target final others resources channels names)) :
    ((instructionTable index witness).interactionsWith witness.data InstructionReceipt.channel.toRaw).length =
      (instructionTable index witness).length := by
  rw [instructionTable_receipts, List.length_map]

private theorem component_projection
    (index : Fin (HostSailBoundary.ensemble (p := p) image source target final others resources channels names).tables.length) :
    let original := (HostSailBoundary.ensemble image source target final others resources channels names).tables[index.val]
    let extended := replace index.val original
    extended.operations.constraints = original.operations.constraints ∧
    extended.operations.lookups = original.operations.lookups ∧
    ∀ channel, channel ≠ InstructionReceipt.channel.toRaw →
      extended.operations.interactionsWith channel = original.operations.interactionsWith channel := by
  dsimp only
  by_cases within : 7 ≤ index.val ∧ index.val < 32
  · rw [show replace index.val _ = ProtectedOrdinaryReceipt.component
        (InstructionChipId.all[index.val - 7]'(by rw [InstructionChipId.all_length]; omega)) from dif_pos within]
    have selected := original_component (image := image) (source := source) (target := target)
      (final := final) (others := others) (resources := resources) (channels := channels) (names := names)
      ⟨index.val - 7, by omega⟩
    simp only [show 7 + (index.val - 7) = index.val by omega] at selected
    rw [selected]
    exact ⟨ProtectedOrdinaryReceipt.constraints _, ProtectedOrdinaryReceipt.lookups _,
      ProtectedOrdinaryReceipt.interactions _⟩
  · rw [show replace index.val _ = _ from dif_neg within]
    exact ⟨rfl, rfl, fun _ _ => rfl⟩

private theorem layout (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p))
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : HostFinalMemory.UniqueNames image source target.sail.memorySnapshot others resources)
    (index : Fin
    (HostSailBoundary.ensemble (p := p) image source target final others resources channels names).tables.length) :
    let original := (HostSailBoundary.ensemble image source target final others resources channels names).tables[index.val]
    let extended := (ensemble image source target final others resources channels names).tables[index.val]'(by
      rw [tables_length]; exact index.isLt)
    extended.circuit.name = original.circuit.name ∧
      extended.width = original.width ∧ extended.fixedColumns = original.fixedColumns ∧
        ∀ rows arity, extended.proverRows rows arity = original.proverRows rows arity := by
  dsimp only
  unfold ensemble
  dsimp only
  rw [List.getElem_mapIdx]
  exact replacement_layout index

/-- Forget only the additional receipts, retaining every physical row and public field. -/
def baseWitness (witness : EnsembleWitness (ensemble image source target final others resources channels names)) :
    EnsembleWitness (HostSailBoundary.ensemble image source target final others resources channels names) :=
  witness.projectPrefix (HostSailBoundary.ensemble image source target final others resources channels names)
    (by rw [tables_length])
    (fun index => by exact (layout image source target final others resources channels names index).2.1.symm.le) (fun index => by exact (layout image source target final others resources channels names index).2.2.1.symm)

private theorem construction_layout (index : Fin
    (ensemble (p := p) image source target final others resources channels names).tables.length) :
    let extended := (ensemble image source target final others resources channels names).tables[index.val]
    let original := (HostSailBoundary.ensemble image source target final others resources channels names).tables[index.val]'(
      Nat.lt_of_lt_of_eq index.isLt tables_length)
    extended.circuit.name = original.circuit.name ∧
      extended.width = original.width ∧ extended.fixedColumns = original.fixedColumns ∧
        ∀ rows arity, extended.proverRows rows arity = original.proverRows rows arity := by
  have facts := layout image source target final others resources channels names
    ⟨index.val, Nat.lt_of_lt_of_eq index.isLt tables_length⟩
  constructor
  · rw [facts.1]
  · exact facts.2

/-- Original arrays also construct the producer installation, with no additional witnesses. -/
def construct (witness : EnsembleWitness
    (HostSailBoundary.ensemble image source target final others resources channels names)) :
    EnsembleWitness (ensemble image source target final others resources channels names) :=
  witness.projectPrefix (ensemble image source target final others resources channels names)
    (by rw [tables_length])
    (fun index => (construction_layout index).2.1.le)
    (fun index => (construction_layout index).2.2.1)

/-- Retaining every name and input layout preserves the complete canonical data function. -/
theorem baseWitness_data (witness : EnsembleWitness
    (ensemble image source target final others resources channels names)) :
    (baseWitness witness).data = witness.data := by
  funext key arity
  unfold baseWitness
  apply witness.projectPrefix_data_of_layout
  · intro index
    exact (layout image source target final others resources channels names index).2.1.symm
  · intro index
    rw [(layout image source target final others resources channels names index).1]
  · intro index rows arity
    exact ((layout image source target final others resources channels names index).2.2.2 rows arity).symm
  · rw [← tables_length, List.drop_length]
    simp

/-- Installing receipts retains every original named input, including empty table entries. -/
theorem construct_data (witness : EnsembleWitness
    (HostSailBoundary.ensemble image source target final others resources channels names)) :
    (construct witness).data = witness.data := by
  funext key arity
  unfold construct
  apply witness.projectPrefix_data_of_layout
  · intro index
    exact (construction_layout index).2.1
  · intro index
    rw [(construction_layout index).1]
  · intro index rows arity
    exact (construction_layout index).2.2.2 rows arity
  · rw [tables_length, List.drop_length]
    simp

/-- The complete public header remains attached to the same physical instruction rows. -/
theorem baseWitness_publicInput (witness : EnsembleWitness
    (ensemble image source target final others resources channels names)) :
    (baseWitness witness).publicInput = witness.publicInput := by
  unfold baseWitness
  exact witness.projectPrefix_publicInput _ _ _

/-- Projection retains all local checks, including the supplied Memory and Sail target checks. -/
theorem baseWitness_constraints
    (witness : EnsembleWitness (ensemble image source target final others resources channels names))
    (checked : witness.Constraints) : (baseWitness witness).Constraints := by
  apply witness.projectPrefix_constraints_of _ _ _ ?_ checked
  intro index row width valid
  rw [← (layout image source target final others resources channels names index).2.1, ← width, Array.extract_size]
  change ((HostSailBoundary.ensemble image source target final others resources channels names).tables[index.val]).operations.ConstraintsHold
    (Environment.fromArray row (baseWitness witness).data)
  rw [baseWitness_data]
  simpa only [ensemble, List.getElem_mapIdx, Operations.ConstraintsHold,
    (component_projection index).1, (component_projection index).2.1] using valid

/-- Constructing producer rows needs only the original local checks. -/
theorem construct_constraints (witness : EnsembleWitness
    (HostSailBoundary.ensemble image source target final others resources channels names))
    (checked : witness.Constraints) : (construct witness).Constraints := by
  unfold construct
  apply witness.projectPrefix_constraints_of
    (target := ensemble image source target final others resources channels names) _ _ _ ?_ checked
  intro index row width valid
  let original : Fin (HostSailBoundary.ensemble image source target final others resources channels names).tables.length :=
    ⟨index.val, Nat.lt_of_lt_of_eq index.isLt tables_length⟩
  rw [(layout image source target final others resources channels names original).2.1, ← width, Array.extract_size]
  change ((ensemble image source target final others resources channels names).tables[index.val]).operations.ConstraintsHold
    (Environment.fromArray row (construct witness).data)
  rw [construct_data]
  have projection := component_projection original
  dsimp only [original] at projection
  simpa only [ensemble, List.getElem_mapIdx, Operations.ConstraintsHold,
    projection.1, projection.2.1] using valid

/-- Complete ledgers on every original channel are unchanged, including WritePermission. -/
theorem baseWitness_interactions
    (witness : EnsembleWitness (ensemble image source target final others resources channels names))
    (channel : RawChannel (ZMod p)) (different : channel ≠ InstructionReceipt.channel.toRaw) :
    (baseWitness witness).interactionsWith channel = witness.interactionsWith channel := by
  unfold baseWitness
  apply witness.projectPrefix_interactions
    (target := HostSailBoundary.ensemble image source target final others resources channels names)
    _ _ _ rfl channel ?_ ?_
  · intro index row width
    rw [← (layout image source target final others resources channels names index).2.1, ← width, Array.extract_size]
    simp only [ensemble, List.getElem_mapIdx, Operations.interactionValuesWith,
      (component_projection index).2.2 channel different]
    exact List.map_congr_left fun _ _ => AbstractInteraction.eval_congr rfl
  · rw [← tables_length, witness.same_length, List.drop_length, List.flatMap_nil]

/-- Each unchanged-channel balance and its occurrence bound transports independently. -/
theorem baseWitness_balancedChannel
    (witness : EnsembleWitness (ensemble image source target final others resources channels names))
    (channel : RawChannel (ZMod p)) (different : channel ≠ InstructionReceipt.channel.toRaw)
    (balanced : witness.BalancedChannel channel) : (baseWitness witness).BalancedChannel channel := by
  change BalancedInteractions ((baseWitness witness).interactionsWith channel)
  rw [baseWitness_interactions witness channel different]
  exact balanced

/-- Full-assembly guarantees pass to the old physical view at the same canonical data. -/
theorem baseWitness_channelGuarantees
    (witness : EnsembleWitness (ensemble image source target final others resources channels names))
    (channel : RawChannel (ZMod p)) (different : channel ≠ InstructionReceipt.channel.toRaw)
    (guarantees : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data channel) :
    ∀ table ∈ (baseWitness witness).tables, table.ChannelGuarantees (baseWitness witness).data channel := by
  apply witness.projectPrefix_channelGuarantees_of _ _ _ channel ?_ guarantees
  intro index row width valid
  rw [← (layout image source target final others resources channels names index).2.1, ← width, Array.extract_size]
  change ((HostSailBoundary.ensemble image source target final others resources channels names).tables[index.val]).operations.ChannelGuarantees
    channel (Environment.fromArray row (baseWitness witness).data)
  rw [baseWitness_data]
  apply Operations.channelGuarantees_of_interactionsWith_subset _ _ _ ?_ _ valid
  simpa only [ensemble, List.getElem_mapIdx, (component_projection index).2.2 channel different] using
    (List.Subset.refl _)


/-- Data-only construction preserves all original channel occurrences as well as local checks. -/
theorem construct_interactions (witness : EnsembleWitness
    (HostSailBoundary.ensemble image source target final others resources channels names))
    (channel : RawChannel (ZMod p)) (different : channel ≠ InstructionReceipt.channel.toRaw) :
    (construct witness).interactionsWith channel = witness.interactionsWith channel := by
  unfold construct
  apply witness.projectPrefix_interactions
    (target := ensemble image source target final others resources channels names)
    _ _ _ rfl channel ?_ ?_
  · intro index row width
    let original : Fin (HostSailBoundary.ensemble image source target final others resources channels names).tables.length :=
      ⟨index.val, Nat.lt_of_lt_of_eq index.isLt tables_length⟩
    rw [(layout image source target final others resources channels names original).2.1, ← width, Array.extract_size]
    have projection := (component_projection original).2.2 channel different
    dsimp only [original] at projection
    simp only [ensemble, List.getElem_mapIdx, Operations.interactionValuesWith, projection]
    exact List.map_congr_left fun _ _ => AbstractInteraction.eval_congr rfl
  · rw [tables_length, witness.same_length, List.drop_length, List.flatMap_nil]

end SP1Clean.Soundness.HostOrdinaryReceipts
