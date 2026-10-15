import SP1Clean.Soundness.OrderedMemoryEnsemble
import ToClean.Air.ChannelClosure
import ToClean.Air.ComponentOutput
import SP1Clean.Proofs.Chips.OrderedFinalProvider

/-! # Native final-memory inventory

Final register and RAM rows share a private control channel with fixed endpoints. Every physical
provider row pulls one canonical Memory record. The shared inventory proof excludes repeated
locations across both tables. Connecting this inventory to the timed machine establishes that
these are the final values; that claim is not a local finalizer assumption.
-/

namespace SP1Clean.Soundness.FinalMemoryEnsemble

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

open SP1Clean.OrderedFinalProvider

def registerView : TransitionView (OrderedBoundary.channel (p := p) channelName) :=
  OrderedMemoryEnsemble.providerView channelName (by decide) MemoryBoundary.FinalSpec
    FinalRegisterProvider.circuit (fun _ _ _ valid => valid.1) (fun _ valid => valid) (by
      simp [GeneralFormalCircuit.channels, FinalRegisterProvider.circuit, circuit_norm,
        OrderedBoundary.channel, channelName, memoryChannel])

def ramView : TransitionView (OrderedBoundary.channel (p := p) channelName) :=
  OrderedMemoryEnsemble.providerView channelName (by decide) MemoryBoundary.RamFinalSpec
    FinalRamProvider.circuit (fun _ _ _ valid => valid.1) (fun _ valid => valid.1) (by
      simp [GeneralFormalCircuit.channels, FinalRamProvider.circuit, circuit_norm,
        OrderedBoundary.channel, channelName, memoryChannel, byteChannel])

inductive TableId where
  | registers | ram | terminal
deriving DecidableEq

def viewFor : TableId → TransitionView (OrderedBoundary.channel (p := p) channelName)
  | .registers => registerView
  | .ram => ramView
  | .terminal => OrderedMemoryEnsemble.terminalView channelName (by decide)

/-- Final rows use only Byte, Memory, and their own private ordering channel. -/
theorem view_channels_subset (id : TableId) :
    (viewFor (p := p) id).component.circuit.channels ⊆
      [byteChannel.toRaw, memoryChannel.toRaw, (OrderedBoundary.channel channelName).toRaw] := by
  cases id
  · change [byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw,
      byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
      memoryChannel.toRaw, (OrderedBoundary.channel channelName).toRaw] ⊆ _
    simp
  · change [byteChannel.toRaw, byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw,
      byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
      memoryChannel.toRaw, (OrderedBoundary.channel channelName).toRaw] ⊆ _
    simp
  · change [byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw,
      (OrderedBoundary.channel channelName).toRaw] ⊆ _
    simp

/-- Finalizer semantics require only raw constraints and Byte guarantees, before Memory grounding. -/
theorem view_spec (id : TableId) (env : Environment (ZMod p))
    (constraints : (viewFor id).component.operations.ConstraintsHold env)
    (byte : (viewFor id).component.operations.ChannelGuarantees byteChannel.toRaw env) :
    (viewFor id).component.Spec env := by
  have assumptions : (viewFor (p := p) id).component.CircuitAssumptions env := by cases id <;> trivial
  have channels : (viewFor (p := p) id).component.circuit.channelsWithGuarantees ⊆
      [byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw] := by
    cases id
    · change [byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw] ⊆ _
      simp
    · change [byteChannel.toRaw, byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw] ⊆ _
      simp
    · exact List.Subset.refl _
  apply (Component.weakSoundness assumptions constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ ((viewFor id).component.inChannelsOrGuarantees env)]
  intro channel member
  rcases List.mem_cons.mp (channels member) with rfl | member
  · exact byte
  · obtain rfl := List.mem_singleton.mp member
    exact Operations.channelGuarantees_of_trivial _ (by simp [OrderedBoundary.channel, Channel.toRaw]) _ _

def recordFor (id : TableId) (env : Environment (ZMod p)) : Option (MemoryMsg (ZMod p)) :=
  match id with
  | .registers => some (({ circuit := registerCircuit } : Component (ZMod p)).rowOutput env)
  | .ram => some (({ circuit := ramCircuit } : Component (ZMod p)).rowOutput env)
  | .terminal => none

/-- Finalizer contracts read only committed cells. Dropping unrelated tables changes canonical
data, but does not change the meaning of these three components' decoded rows. -/
theorem view_spec_setData (id : TableId) (row : Array (ZMod p))
    (data data' : ProverData (ZMod p))
    (valid : (viewFor id).component.Spec (Environment.fromArray row data)) :
    (viewFor id).component.Spec (Environment.fromArray row data') := by
  have input : (viewFor id).component.rowInput (Environment.fromArray row data') =
      (viewFor id).component.rowInput (Environment.fromArray row data) :=
    ProvableType.valueFromOffset_congr _ 0 (fun _ _ => rfl)
  have output : (viewFor id).component.rowOutput (Environment.fromArray row data') =
      (viewFor id).component.rowOutput (Environment.fromArray row data) :=
    Component.rowOutput_congr _ rfl
  unfold Component.Spec at valid ⊢
  rw [input, output]
  cases id <;> exact valid

def inventory : OrderedMemoryEnsemble.Inventory channelName (MemoryBoundary.FinalSpec (p := p)) where
  Index := TableId
  tableIds := [.registers, .ram, .terminal]
  viewFor := viewFor
  recordFor := recordFor
  strict := by
    intro id env valid
    cases id with
    | registers => exact valid.2.1.2.2
    | ram => exact valid.2.1.2.2
    | terminal => exact valid.2
  recordFor_spec := by
    intro id env valid record found
    cases id with
    | registers =>
      obtain rfl := Option.some.inj found
      exact ⟨valid.1, valid.2.2⟩
    | ram =>
      obtain rfl := Option.some.inj found
      exact ⟨valid.1.1, valid.2.2⟩
    | terminal => contradiction

/-- The two finalizers and their ordering terminal have distinct canonical names. -/
theorem inventory_unique_names :
    ((inventory (p := p)).views.map (·.component.circuit.name)).Nodup := by
  change [
    (registerView (p := p)).component.circuit.name, ramView.component.circuit.name,
    (OrderedMemoryEnsemble.terminalView channelName (by decide)).component.circuit.name].Nodup
  simp [registerView, ramView,
    OrderedMemoryEnsemble.providerView, OrderedMemoryEnsemble.terminalView,
    OrderedMemoryProvider.circuit, OrderedBoundaryEnd.circuit,
    FinalRegisterProvider.circuit, FinalRamProvider.circuit, channelName]
  decide

def ensemble (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p)))
    (names : (((inventory (p := p)).views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup) :=
  inventory.ensemble auxiliary channels names

variable {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
variable {names : (((inventory (p := p)).views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup}

def records (witness : EnsembleWitness (ensemble auxiliary channels names)) := inventory.records witness

/-- The shared decoder reads the original output of each physical register and RAM row;
the ordering terminal contributes no Memory record. -/
theorem records_eq (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    records witness =
      (witness.tables[0]'(by rw [← witness.same_length]; simp [ensemble,
        OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
        OrderedMemoryEnsemble.Inventory.views, inventory])).table.map
          (fun row => ({ circuit := registerCircuit } : Component (ZMod p)).rowOutput
            (Environment.fromArray row witness.data)) ++
      (witness.tables[1]'(by rw [← witness.same_length]; simp [ensemble,
        OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
        OrderedMemoryEnsemble.Inventory.views, inventory])).table.map
          (fun row => ({ circuit := ramCircuit } : Component (ZMod p)).rowOutput
            (Environment.fromArray row witness.data)) := by
  have length : 3 ≤ witness.tables.length := by
    rw [← witness.same_length]
    simp [ensemble, OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
      OrderedMemoryEnsemble.Inventory.views, inventory]
  have front : witness.tables.take 3 = [witness.tables[0], witness.tables[1], witness.tables[2]] := by
    rw [List.take_succ_eq_append_getElem (by omega : 2 < witness.tables.length),
      List.take_succ_eq_append_getElem (by omega : 1 < witness.tables.length),
      List.take_succ_eq_append_getElem (by omega : 0 < witness.tables.length)]
    rfl
  change ((TransitionView.readIndexedRows [TableId.registers, .ram, .terminal]
    (witness.tables.take 3) witness.data).filterMap fun row => recordFor row.1 row.2) = _
  rw [front]
  simp only [TransitionView.readIndexedRows, List.zip_cons_cons, List.zip_nil_right,
    List.flatMap_cons, List.flatMap_nil, List.filterMap_append, List.filterMap_map,
    Function.comp_def, recordFor, List.filterMap_eq_map', List.filterMap_none,
    List.append_nil]

theorem records_valid (witness : EnsembleWitness (ensemble auxiliary channels names))
    (valid : witness.Spec) : ∀ record ∈ records witness, MemoryBoundary.FinalSpec record :=
  inventory.records_valid witness valid

theorem records_locations_nodup (witness : EnsembleWitness (ensemble auxiliary channels names))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel channelName).toRaw ∉ component.circuit.channels)
    (valid : witness.Spec) (balanced : witness.BalancedChannels) :
    ((records witness).map MemoryMsg.locOf).Nodup :=
  inventory.records_locations_nodup witness privateChannel valid balanced

/-- The finite record decoder agrees exactly with each table's physical Memory interactions. -/
theorem recordFor_interactions (id : TableId) (env : Environment (ZMod p)) :
    (viewFor id).component.operations.interactionValuesWith memoryChannel.toRaw env =
      ((recordFor id env).toList).map (memoryChannel.emittedValue (-1)) := by
  cases id with
  | registers =>
    simp only [viewFor, registerView, OrderedMemoryEnsemble.providerView,
        Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
        OrderedMemoryProvider.circuit]
    rw [OrderedMemoryProvider.main_memory_interactions]
    simp only [FinalRegisterProvider.circuit]
    rw [FinalRegisterProvider.main_memory_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_emitted]
    simp only [recordFor, Option.toList_some, List.map_cons, List.map_nil, Component.rowOutput, Component.rowInputVar,
      OrderedFinalProvider.registerCircuit, OrderedMemoryProvider.circuit, FinalRegisterProvider.circuit,
      OrderedMemoryProvider.elaborated, FinalRegisterProvider.elaborated, circuit_norm]
  | ram =>
    simp only [viewFor, ramView, OrderedMemoryEnsemble.providerView,
        Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
        OrderedMemoryProvider.circuit]
    rw [OrderedMemoryProvider.main_memory_interactions]
    simp only [FinalRamProvider.circuit]
    rw [FinalRamProvider.main_memory_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_emitted]
    simp only [recordFor, Option.toList_some, List.map_cons, List.map_nil, Component.rowOutput, Component.rowInputVar,
      OrderedFinalProvider.ramCircuit, OrderedMemoryProvider.circuit, FinalRamProvider.circuit,
      OrderedMemoryProvider.elaborated, FinalRamProvider.elaborated, circuit_norm]
  | terminal =>
    exact OrderedMemoryEnsemble.terminalView_memory_interactions _ (by decide) env

/-- The physical boundary tables emit precisely the decoded records, with unit multiplicity. -/
theorem memory_interactions_eq (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    (witness.tables.take (inventory (p := p)).views.length).flatMap (·.interactionsWith witness.data memoryChannel.toRaw) =
      (records witness).map (memoryChannel.emittedValue (-1)) := by
  exact inventory.memory_interactions_eq witness (memoryChannel.emittedValue (-1)) recordFor_interactions

/-- The decoder depends only on the two finalizer row arrays.
Different physical proof views may retain different suffixes or verifier interfaces. -/
theorem records_congr_rows {otherAuxiliary : List (Component (ZMod p))}
    {otherChannels : List (RawChannel (ZMod p))}
    {otherNames : (((inventory (p := p)).views.map (·.component) ++ otherAuxiliary).map (·.circuit.name)).Nodup}
    (first : EnsembleWitness (ensemble auxiliary channels names))
    (second : EnsembleWitness (ensemble otherAuxiliary otherChannels otherNames))
    (rows : (first.tables.take 2).map (·.table) = (second.tables.take 2).map (·.table)) :
    records first = records second := by
  have firstBound : 2 ≤ first.tables.length := by
    rw [← first.same_length]
    simp [ensemble, OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
      OrderedMemoryEnsemble.Inventory.views, inventory]
  have secondBound : 2 ≤ second.tables.length := by
    rw [← second.same_length]
    simp [ensemble, OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
      OrderedMemoryEnsemble.Inventory.views, inventory]
  have arrays (index : Fin 2) :
      (first.tables[index.val]'(by omega)).table = (second.tables[index.val]'(by omega)).table := by
    have same := congrArg (fun arrays => arrays[index.val]?) rows
    simpa only [List.getElem?_map, List.getElem?_take, if_pos index.isLt,
      List.getElem?_eq_getElem (by omega : index.val < first.tables.length),
      List.getElem?_eq_getElem (by omega : index.val < second.tables.length),
      Option.map_some, Option.some.injEq] using same
  simp only [records_eq, arrays ⟨0, by decide⟩, arrays ⟨1, by decide⟩]
  congr 1 <;> apply List.map_congr_left <;> intro row _ <;>
    exact Component.rowOutput_congr _ rfl

end SP1Clean.Soundness.FinalMemoryEnsemble
