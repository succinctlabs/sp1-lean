import SP1Clean.Native.Operations.FinalMemoryReceipt
import ToClean.Air.ComponentReplacement
import ToClean.Air.Footprint
import ToClean.Circuit.InteractionRecovery

/-! # Publishing the physical final inventory

A typed slot identifies the original finalizer before installing its receipt. The wrapper retains
its name, complete rows, input layout and constraints, and adds one unit receipt per physical row.
Projection therefore preserves canonical data and every old channel when the receipt is fresh.

This is an installation adapter, not an endpoint theorem. The enclosing assembly must install
receipt consumers and include their Byte demand in its channel-closure proof.
-/

namespace SP1Clean.Soundness.FinalReceiptEnsemble

open Circuit Air.Flat Channels

variable {p : ℕ} [Fact p.Prime]
  {PublicIO Input : TypeMap} [ProvableType PublicIO] [ProvableType Input]

/-- Publish one full record at an existing finalizer's registered physical position. -/
def install (ens : Ensemble (ZMod p) PublicIO) (ram : Bool)
    (provider : GeneralFormalCircuit (ZMod p) Input MemoryMsg)
    (source : TableSlot ens.tables { circuit := provider }) : Ensemble (ZMod p) PublicIO :=
  { ens.replaceComponent source { circuit := FinalMemoryReceipt.circuit ram provider } rfl with
    channels := ens.channels ++ [(FinalMemoryValue.channel ram).toRaw] }

variable {ens : Ensemble (ZMod p) PublicIO} {ram : Bool}
  {provider : GeneralFormalCircuit (ZMod p) Input MemoryMsg}
  {source : TableSlot ens.tables { circuit := provider }}

/-- The receipt-bearing component occupies exactly the original slot. -/
def slot : TableSlot (install ens ram provider source).tables
    { circuit := FinalMemoryReceipt.circuit ram provider } where
  index := ⟨source.index.val, by simpa only [install, Ensemble.replaceComponent, List.length_set] using source.index.isLt⟩
  component_eq := List.getElem_set_self (by simpa only [install, Ensemble.replaceComponent, List.length_set] using source.index.isLt)

variable (witness : EnsembleWitness (install ens ram provider source))

theorem bound : source.index.val < witness.tables.length := by
  rw [← witness.same_length]
  simpa only [install, Ensemble.replaceComponent, List.length_set] using source.index.isLt

/-- Read the receipt-producing physical table without rebuilding its rows. -/
def table : Table (ZMod p) := slot.table witness

theorem table_component : (table witness).component = { circuit := FinalMemoryReceipt.circuit ram provider } :=
  slot.table_component witness

/-- Forget the receipt while retaining every physical row and the public input. -/
def project : EnsembleWitness ens :=
  EnsembleWitness.ofTables ens
    (witness.tables.set source.index.val ((table witness).withComponent { circuit := provider }
      (by rw [table_component]; rfl) (by rw [table_component])))
    witness.publicInput (by
      rw [List.map_set, Table.withComponent_component, witness.tables_map_component]
      change (ens.tables.set source.index.val _).set source.index.val { circuit := provider } = ens.tables
      rw [List.set_set]
      simpa only [source.component_eq] using List.set_getElem_self source.index.isLt)

/-- The wrapper's name and derived input entries agree at every arity. -/
@[simp] theorem project_data : (project witness).data = witness.data := by
  apply deriveProverData_set witness.tables ⟨source.index.val, bound witness⟩
  · change provider.name = (table witness).component.circuit.name
    rw [table_component]
    rfl
  · intro arity
    change ({ circuit := provider } : Component (ZMod p)).proverRows (table witness).table arity =
      (table witness).component.proverRows (table witness).table arity
    rw [table_component]
    rfl

@[simp] theorem project_publicInput : (project witness).publicInput = witness.publicInput := rfl

/-- Only the selected table's component changes. -/
theorem project_tables : (project witness).tables =
    witness.tables.set source.index.val ((table witness).withComponent { circuit := provider }
      (by rw [table_component]; rfl) (by rw [table_component])) := rfl

/-- Reuse the original rows when installing the receipt; the typed slot supplies the layout. -/
def lift (witness : EnsembleWitness ens) : EnsembleWitness (install ens ram provider source) :=
  EnsembleWitness.ofTables (install ens ram provider source)
    (witness.tables.set source.index.val ((source.table witness).withComponent
      { circuit := FinalMemoryReceipt.circuit ram provider }
      (by rw [source.table_component]; rfl) (by rw [source.table_component])))
    witness.publicInput (by rw [List.map_set, Table.withComponent_component, witness.tables_map_component]; rfl)

@[simp] theorem lift_data (witness : EnsembleWitness ens) :
    (lift (source := source) (ram := ram) witness).data = witness.data := by
  apply deriveProverData_set witness.tables ⟨source.index.val, by rw [← witness.same_length]; exact source.index.isLt⟩
  · change (FinalMemoryReceipt.circuit ram provider).name = (source.table witness).component.circuit.name
    rw [source.table_component]
    rfl
  · intro arity
    change ({ circuit := FinalMemoryReceipt.circuit ram provider } : Component (ZMod p)).proverRows
      (source.table witness).table arity = (source.table witness).component.proverRows (source.table witness).table arity
    rw [source.table_component]
    rfl

/-- Constructing and forgetting a receipt returns the complete original physical inventory. -/
theorem project_lift_tables (witness : EnsembleWitness ens) :
    (project (lift (source := source) (ram := ram) witness)).tables = witness.tables := by
  have undo : (table (lift (source := source) (ram := ram) witness)).withComponent
      { circuit := provider } (by rw [table_component]; rfl) (by rw [table_component]) =
      source.table witness := by
    rw [Table.ext_iff]
    constructor
    · exact (source.table_component witness).symm
    · have lifted : table (lift (source := source) (ram := ram) witness) =
          (source.table witness).withComponent { circuit := FinalMemoryReceipt.circuit ram provider }
            (by rw [source.table_component]; rfl) (by rw [source.table_component]) :=
        List.getElem_set_self (by simpa only [List.length_set, ← witness.same_length] using source.index.isLt)
      have rows := congrArg (fun physical : Table (ZMod p) => physical.table) lifted
      simpa only [Table.withComponent_rows] using rows
  change (witness.tables.set source.index.val _).set source.index.val _ = witness.tables
  rw [List.set_set, undo]
  exact List.set_getElem_self _

/-- Receipt publication preserves both assertions and lookups on every row. -/
theorem project_constraints : (project witness).Constraints ↔ witness.Constraints := by
  have selected := Table.withComponent_constraints (table witness) { circuit := provider }
    (by rw [table_component]; rfl) (by rw [table_component]) witness.data
    (by rw [table_component, FinalMemoryReceipt.constraints])
    (by rw [table_component, FinalMemoryReceipt.lookups])
  simp only [EnsembleWitness.constraints_iff, project_data]
  constructor
  · intro tables physical member
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp member
    rw [project_tables] at tables
    by_cases equal : j = source.index.val
    · subst j
      apply selected.mp
      exact tables _ (List.mem_iff_getElem.mpr ⟨source.index.val, by simpa using bound witness,
        List.getElem_set_self (by simpa using bound witness)⟩)
    · exact tables _ (List.mem_iff_getElem.mpr ⟨j, by simpa using hj,
        List.getElem_set_ne (Ne.symm equal) _⟩)
  · intro tables physical member
    rw [project_tables] at member
    rcases List.mem_or_eq_of_mem_set member with old | rfl
    · exact tables physical old
    · exact selected.mpr (tables _ (List.getElem_mem _))

/-- Existing generated rows need no additional semantic premise to publish receipts. -/
theorem lift_constraints (witness : EnsembleWitness ens) (checked : witness.Constraints) :
    (lift (source := source) (ram := ram) witness).Constraints := by
  apply (project_constraints (lift witness)).mp
  rw [EnsembleWitness.constraints_iff, project_data, lift_data, project_lift_tables]
  exact checked

/-- All original arrays survive projection, including repeated rows. -/
theorem project_rows : (project witness).tables.map (·.table) = witness.tables.map (·.table) := by
  rw [project_tables, List.map_set]
  change (witness.tables.map (·.table)).set source.index.val
    (witness.tables[source.index.val]'(bound witness)).table = _
  rw [← List.getElem_map (l := witness.tables) (i := source.index.val) (f := fun physical => physical.table),
    List.set_getElem_self]
  simpa only [List.length_map] using bound witness

/-- Receipt publication changes no physical table height. -/
theorem project_tableHeights : (project witness).tableHeights = witness.tableHeights := by
  change ((project witness).tables.map Table.length) = witness.tables.map Table.length
  rw [project_tables, List.map_set]
  change (witness.tables.map Table.length).set source.index.val
    (witness.tables[source.index.val]'(bound witness)).length = _
  rw [← List.getElem_map (l := witness.tables) (i := source.index.val) (f := Table.length),
    List.set_getElem_self]
  simpa only [List.length_map] using bound witness

/-- Every occurrence on other channels survives, including zero-multiplicity occurrences. -/
theorem project_interactions (channel : RawChannel (ZMod p))
    (different : channel ≠ (FinalMemoryValue.channel ram).toRaw) :
    (project witness).interactionsWith channel = witness.interactionsWith channel := by
  have row := Table.withComponent_interactions (table witness) { circuit := provider }
    (by rw [table_component]; rfl) (by rw [table_component]) witness.data channel
    (by rw [table_component, FinalMemoryReceipt.interactions ram provider channel different])
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.verifierInteractionsWith,
    EnsembleWitness.tableContext, TableContext.interactionsWith, project_data, project_publicInput]
  change ens.verifierOperations.interactionValuesWith channel _ ++
      (witness.tables.set source.index.val _).flatMap (·.interactionsWith witness.data channel) =
    ens.verifierOperations.interactionValuesWith channel _ ++
      witness.tables.flatMap (·.interactionsWith witness.data channel)
  congr 1
  rw [List.flatMap, List.map_set, row]
  change ((witness.tables.map (fun physical => physical.interactionsWith witness.data channel)).set source.index.val
    ((witness.tables[source.index.val]'(bound witness)).interactionsWith witness.data channel)).flatten = _
  rw [← List.getElem_map (l := witness.tables) (i := source.index.val)
    (f := fun physical : Table (ZMod p) => physical.interactionsWith witness.data channel), List.set_getElem_self]
  · rfl
  · simpa only [List.length_map] using bound witness

/-- Original guarantees survive projection at its identical canonical data. -/
theorem project_channelGuarantees (channel : RawChannel (ZMod p))
    (different : channel ≠ (FinalMemoryValue.channel ram).toRaw)
    (guarantees : ∀ physical ∈ witness.tables, physical.ChannelGuarantees witness.data channel) :
    ∀ physical ∈ (project witness).tables, physical.ChannelGuarantees (project witness).data channel := by
  simp only [project_data]
  intro physical member
  rw [project_tables] at member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact guarantees physical old
  · apply Table.withComponent_channelGuarantees_of
    · intro env valid
      apply Operations.channelGuarantees_of_interactionsWith_subset _ _ _ ?_ env valid
      rw [table_component, FinalMemoryReceipt.interactions ram provider channel different]
      exact List.Subset.refl _
    · exact guarantees _ (List.getElem_mem _)

/-- A fresh receipt channel leaves all original channel balances unchanged. -/
theorem project_balanced (fresh : (FinalMemoryValue.channel ram).toRaw ∉ ens.channels)
    (balanced : witness.BalancedChannels) : (project witness).BalancedChannels := by
  intro channel member
  change BalancedInteractions ((project witness).interactionsWith channel)
  rw [project_interactions witness channel (by rintro rfl; exact fresh member)]
  exact balanced channel (List.mem_append_left _ member)

/-- The inventory is decoded from the original provider output on the literal physical rows. -/
def records  : List (MemoryMsg (ZMod p)) :=
  (table witness).table.map fun row => ({ circuit := provider } : Component (ZMod p)).rowOutput
    (Environment.fromArray row witness.data)

/-- If the original provider is silent on the receipt channel, every finalizer row publishes
exactly one of its complete original records. -/
theorem table_receipts
    (silent : (FinalMemoryValue.channel ram).toRaw ∉ provider.channels) :
    (table witness).interactionsWith witness.data (FinalMemoryValue.channel ram).toRaw =
      (records witness).map (FinalMemoryValue.channel ram).pushedValue := by
  have row (env : Environment (ZMod p)) :
      ({ circuit := FinalMemoryReceipt.circuit ram provider } : Component (ZMod p)).operations.interactionValuesWith
        (FinalMemoryValue.channel ram).toRaw env =
      [(FinalMemoryValue.channel ram).pushedValue (({ circuit := provider } : Component (ZMod p)).rowOutput env)] := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    rw [FinalMemoryReceipt.receipt_interactions]
    rw [InteractionRecovery.interactionsWith_main_eq_nil provider.base _ _ _ silent]
    simp only [List.nil_append, List.map_cons, List.map_nil, Channel.eval_pushed]
    rfl
  simp only [Table.interactionsWith, table_component, row, records, List.map_map]
  exact List.map_eq_flatMap.symm

/-- The receipt channel costs exactly one physical occurrence per finalizer row. -/
theorem table_receipts_length
    (silent : (FinalMemoryValue.channel ram).toRaw ∉ provider.channels) :
    ((table witness).interactionsWith witness.data (FinalMemoryValue.channel ram).toRaw).length =
      (table witness).length := by
  rw [table_receipts witness silent, List.length_map]
  exact List.length_map _

end SP1Clean.Soundness.FinalReceiptEnsemble
