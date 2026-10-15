import SP1Clean.Soundness.OrderedBoundaryEnsemble
import SP1Clean.Proofs.Chips.OrderedMemoryProvider
import SP1Clean.Native.Operations.OrderedBoundaryEnd
import ToMathlib.ListFilterMap

/-! # Ordered native memory inventories

Initialization and finalization share fixed endpoints, physical transition views, and the same
location-uniqueness argument. An inventory registers its actual components and record decoder once;
its local correctness fields are proofs about those components, not assumptions on a witness.
-/

namespace SP1Clean.Soundness.OrderedMemoryEnsemble

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def startKey : Word (ZMod p) := #v[0, 0, 0, 0]
def endKey : Word (ZMod p) := #v[1, 0, 0, 1]

omit [Fact (2 ^ 17 < p)] in
theorem startKey_toNat : Word.toNat (startKey (p := p)) = 0 := by
  simp [startKey, Word.toNat]

omit [Fact (2 ^ 17 < p)] in
theorem endKey_toNat : Word.toNat (endKey (p := p)) = 2 ^ 48 + 1 := by
  have : Fact (1 < p) := ⟨(Fact.out (p := p.Prime)).one_lt⟩
  norm_num [endKey, Word.toNat, ZMod.val_one]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_previous {Payload : TypeMap} [ProvableType Payload]
    (env : Environment (ZMod p)) (input : Var (OrderedMemoryProvider.Inputs Payload) (ZMod p)) :
    Eval.eval env input.link.previous = (Eval.eval env input).link.previous := by
  rcases input with ⟨payload, previous, current, comparison⟩
  simp only [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_current {Payload : TypeMap} [ProvableType Payload]
    (env : Environment (ZMod p)) (input : Var (OrderedMemoryProvider.Inputs Payload) (ZMod p)) :
    Eval.eval env input.link.current = (Eval.eval env input).link.current := by
  rcases input with ⟨payload, previous, current, comparison⟩
  simp only [circuit_norm]

def providerView {Payload : TypeMap} [ProvableType Payload] (name : String) (distinct : name ≠ "SP1Byte")
    (recordSpec : MemoryMsg (ZMod p) → Prop)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (binds : ∀ input output data, provider.Spec input output data → recordSpec output)
    (canonical : ∀ record, recordSpec record → MemoryBoundary.CanonicalSpec record)
    (privateChannel : (OrderedBoundary.channel name).toRaw ∉ provider.channels) :
    TransitionView (OrderedBoundary.channel (p := p) name) where
  component := { circuit := OrderedMemoryProvider.circuit name recordSpec provider binds canonical }
  edge env :=
    let input := valueFromOffset (OrderedMemoryProvider.Inputs Payload) 0 env
    (input.link.previous, input.link.current)
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations, OrderedMemoryProvider.circuit]
    rw [OrderedMemoryProvider.main_interactions _ distinct provider privateChannel]
    simp only [List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
      eval_previous, eval_current, ProvableType.eval_varFromOffset]
    rfl

omit [Fact (2 ^ 17 < p)] in
private theorem eval_terminal_previous (env : Environment (ZMod p))
    (input : Var OrderedBoundary.TerminalInputs (ZMod p)) :
    Eval.eval env input.previous = (Eval.eval env input).previous := by
  rcases input with ⟨previous, comparison⟩
  simp only [circuit_norm]

def terminalView (name : String) (distinct : name ≠ "SP1Byte") :
    TransitionView (OrderedBoundary.channel (p := p) name) where
  component := { circuit := OrderedBoundaryEnd.circuit name endKey }
  edge env := ((valueFromOffset OrderedBoundary.TerminalInputs 0 env).previous, endKey)
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations, OrderedBoundaryEnd.circuit]
    change ((OrderedBoundaryEnd.main name endKey
      (varFromOffset OrderedBoundary.TerminalInputs 0)).operations
      (size OrderedBoundary.TerminalInputs)).interactionValuesWith _ env = _
    rw [OrderedBoundaryEnd.interactionValues _ distinct]
    simp only [eval_terminal_previous, ProvableType.eval_varFromOffset]
    rfl

theorem terminalView_memory_interactions (name : String) (distinct : name ≠ "SP1Byte")
    (env : Environment (ZMod p)) :
    (terminalView name distinct).component.operations.interactionValuesWith memoryChannel.toRaw env = [] := by
  have empty := InteractionRecovery.interactionsWith_main_eq_nil
    (OrderedBoundaryEnd.circuit name (endKey (p := p))).base memoryChannel.toRaw
    (varFromOffset OrderedBoundary.TerminalInputs 0) (size OrderedBoundary.TerminalInputs) (by
      simp [OrderedBoundaryEnd.circuit, circuit_norm, OrderedBoundary.channel, memoryChannel, byteChannel])
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
    Component.rowOperations, terminalView, OrderedBoundaryEnd.circuit] at empty ⊢
  rw [empty]
  rfl

/-- Static proof-bearing registry of providers and their terminal component. -/
structure Inventory (name : String) (recordSpec : MemoryMsg (ZMod p) → Prop) where
  Index : Type
  tableIds : List Index
  viewFor : Index → TransitionView (OrderedBoundary.channel (p := p) name)
  recordFor : Index → Environment (ZMod p) → Option (MemoryMsg (ZMod p))
  strict : ∀ id env, (viewFor id).component.Spec env →
    Word.toNat ((viewFor id).edge env).1 < Word.toNat ((viewFor id).edge env).2
  recordFor_spec : ∀ id env, (viewFor id).component.Spec env →
    ∀ record, recordFor id env = some record → recordSpec record ∧
      Word.toNat ((viewFor id).edge env).2 = (MemoryMsg.locOf record).busAddress + 1

namespace Inventory

variable {name : String} {recordSpec : MemoryMsg (ZMod p) → Prop}

def views (inventory : Inventory name recordSpec) := inventory.tableIds.map inventory.viewFor

def ensemble (inventory : Inventory name recordSpec) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : ((inventory.views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup) :
    Ensemble (ZMod p) unit :=
  OrderedBoundaryEnsemble.ensemble name startKey endKey inventory.views auxiliary channels names

variable (inventory : Inventory name recordSpec) {auxiliary : List (Component (ZMod p))}
variable {channels : List (RawChannel (ZMod p))}
variable {names : ((inventory.views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup}

def indexedRows (witness : EnsembleWitness (inventory.ensemble auxiliary channels names)) :=
  TransitionView.readIndexedRows inventory.tableIds (witness.tables.take inventory.views.length) witness.data

def records (witness : EnsembleWitness (inventory.ensemble auxiliary channels names)) : List (MemoryMsg (ZMod p)) :=
  (inventory.indexedRows witness).filterMap fun row => inventory.recordFor row.1 row.2

omit [Fact (2 ^ 17 < p)] in
/-- The decoded record inventory is the actual Memory ledger whenever each registered component
has the stated single-record effect. This transport assumes no constraints or semantic facts. -/
theorem memory_interactions_eq (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (effect : MemoryMsg (ZMod p) → Interaction (ZMod p))
    (realizes : ∀ id env, (inventory.viewFor id).component.operations.interactionValuesWith memoryChannel.toRaw env =
      ((inventory.recordFor id env).toList).map effect) :
    (witness.tables.take inventory.views.length).flatMap (·.interactionsWith witness.data memoryChannel.toRaw) =
      (inventory.records witness).map effect := by
  have aligned := OrderedBoundaryEnsemble.tables_aligned witness
  change List.Forall₂ _ (inventory.tableIds.map inventory.viewFor) _ at aligned
  rw [List.forall₂_map_left_iff] at aligned
  rw [TransitionView.readIndexedRows_interactions inventory.tableIds
    (fun id => (inventory.viewFor id).component) _ witness.data _ aligned]
  simp only [realizes, records, indexedRows, List.filterMap_eq_flatMap_toList, List.map_flatMap]

omit [Fact (2 ^ 17 < p)] in
theorem indexedRows_spec_of_tables (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (valid : ∀ table ∈ witness.tables.take inventory.views.length, table.Spec witness.data) :
    ∀ row ∈ inventory.indexedRows witness, (inventory.viewFor row.1).component.Spec row.2 := by
  apply TransitionView.readIndexedRows_spec inventory.tableIds inventory.viewFor _ witness.data
  · exact OrderedBoundaryEnsemble.tables_aligned witness
  · exact valid

omit [Fact (2 ^ 17 < p)] in
theorem records_valid_of_tables (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (valid : ∀ table ∈ witness.tables.take inventory.views.length, table.Spec witness.data) :
    ∀ record ∈ inventory.records witness, recordSpec record := by
  intro record member
  obtain ⟨row, member, found⟩ := List.mem_filterMap.mp member
  exact (inventory.recordFor_spec row.1 row.2
    (inventory.indexedRows_spec_of_tables witness valid row member) record found).1

omit [Fact (2 ^ 17 < p)] in
/-- Actual Clean balance forces distinct canonical locations throughout the inventory. -/
theorem records_locations_nodup_of_tables (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel name).toRaw ∉ component.circuit.channels)
    (valid : ∀ table ∈ witness.tables.take inventory.views.length, table.Spec witness.data)
    (balanced : witness.BalancedChannel (OrderedBoundary.channel name).toRaw) :
    ((inventory.records witness).map MemoryMsg.locOf).Nodup := by
  have unique := OrderedBoundaryEnsemble.keys_nodup_of_tables witness privateChannel (by
    intro view member env spec
    obtain ⟨id, _, rfl⟩ := List.mem_map.mp member
    exact inventory.strict id env spec) valid balanced
  have indexed := TransitionView.readIndexedRows_keys_nodup inventory.tableIds inventory.viewFor _ witness.data Word.toNat
    inventory.views rfl unique
  have decoded := List.nodup_filterMap_of_nodup_map (inventory.indexedRows witness)
    (fun row => Word.toNat ((inventory.viewFor row.1).edge row.2).2)
    (fun row => (inventory.recordFor row.1 row.2).map MemoryMsg.locOf)
    (fun loc => loc.busAddress + 1) indexed (by
      intro row member loc found
      obtain ⟨record, decodedRecord, rfl⟩ := Option.map_eq_some_iff.mp found
      exact (inventory.recordFor_spec row.1 row.2
        (inventory.indexedRows_spec_of_tables witness valid row member) record decodedRecord).2)
  simpa only [records, List.map_filterMap, Function.comp_def] using decoded

omit [Fact (2 ^ 17 < p)] in
theorem indexedRows_spec (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (valid : witness.Spec) :
    ∀ row ∈ inventory.indexedRows witness, (inventory.viewFor row.1).component.Spec row.2 :=
  inventory.indexedRows_spec_of_tables witness (fun table member =>
    valid.2 table (List.mem_of_mem_take member))

omit [Fact (2 ^ 17 < p)] in
theorem records_valid (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (valid : witness.Spec) : ∀ record ∈ inventory.records witness, recordSpec record :=
  inventory.records_valid_of_tables witness (fun table member =>
    valid.2 table (List.mem_of_mem_take member))

omit [Fact (2 ^ 17 < p)] in
theorem records_locations_nodup (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel name).toRaw ∉ component.circuit.channels)
    (valid : witness.Spec) (balanced : witness.BalancedChannels) :
    ((inventory.records witness).map MemoryMsg.locOf).Nodup :=
  inventory.records_locations_nodup_of_tables witness privateChannel
    (fun table member => valid.2 table (List.mem_of_mem_take member))
    (balanced _ (List.mem_cons_self ..))

end Inventory
end SP1Clean.Soundness.OrderedMemoryEnsemble
