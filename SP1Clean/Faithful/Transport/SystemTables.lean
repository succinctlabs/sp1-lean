import SP1Clean.Faithful.CoreAIR
import SP1Clean.Faithful.MemoryBumpChip
import SP1Clean.Faithful.StateBumpChip
import SP1Clean.Faithful.Transport.Table
import ToClean.Air.TableBuild

/-! # Exact Core system tables transported to native Clean tables

The exact-v6.4 Core relation and the native supported-machine relation both contain the two
canonicalization tables `MemoryBump` and `StateBump`.  Their whole-table faithfulness anchors were
previously leaf theorems: they compared one reconstructed row at a time, but no definition assembled
those rows into the actual `Air.Flat.Table`s consumed by `sp1Ensemble`.

This module supplies that missing constructive transport.  Given the exact heterogeneous rows, it
builds the two native physical tables, proves every native constraint from the exact per-row
assertion conjunct, and preserves the complete projected interaction list.  No semantic premise is
introduced: both tables have width-zero preprocessing, and their existing whole-table anchors cover
their complete assertion and interaction systems.

The other exact system tables are deliberately not hidden here.  Program/Byte/Range redistribution
needs per-row preprocessing semantics plus separate authentication/coverage, while MemoryLocal/Global
and the separate memory-boundary cluster need a redistribution theorem rather than a row-for-row codec.  Those are
distinct contracts; the two bump tables below are the exact row-for-row portion that can already be
closed unconditionally from `CoreAIR.Current.Relation`.
-/

set_option autoImplicit false

namespace SP1Clean.Faithful.Transport

open Circuit
open Air.Flat (Component Table)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## One-table transports -/

/-- Reconstruct the native physical `MemoryBump` row from one exact Rust row. -/
def transportMemoryBumpRow
    (row : CoreAIR.Current.Row p .memoryBump) : Array (ZMod p) :=
  Faithful.memoryBumpPhysicalRow (Faithful.memoryBumpDeconfigure row.main)

/-- Reconstruct the native physical `StateBump` row from one exact Rust row. -/
def transportStateBumpRow
    (row : CoreAIR.Current.Row p .stateBump) : Array (ZMod p) :=
  Faithful.stateBumpPhysicalRow (Faithful.stateBumpDeconfigure row.main)

/-- The exact `MemoryBump` rows, installed as the native `MemoryBumpChip` table. -/
def transportMemoryBumpTable (rows : List (CoreAIR.Current.Row p .memoryBump))
    (data : ProverData (ZMod p)) : Table (ZMod p) where
  component := ⟨MemoryBumpChip.circuit⟩
  width := (⟨MemoryBumpChip.circuit⟩ : Component (ZMod p)).width
  table := rows.map transportMemoryBumpRow
  data := data
  uniform_width := by
    intro nativeRow hrow
    obtain ⟨row, -, rfl⟩ := List.mem_map.mp hrow
    exact Faithful.memoryBumpPhysicalRow_size row.main

/-- The exact `StateBump` rows, installed as the native `StateBumpChip` table. -/
def transportStateBumpTable (rows : List (CoreAIR.Current.Row p .stateBump))
    (data : ProverData (ZMod p)) : Table (ZMod p) where
  component := ⟨StateBumpChip.circuit⟩
  width := (⟨StateBumpChip.circuit⟩ : Component (ZMod p)).width
  table := rows.map transportStateBumpRow
  data := data
  uniform_width := by
    intro nativeRow hrow
    obtain ⟨row, -, rfl⟩ := List.mem_map.mp hrow
    exact Faithful.stateBumpPhysicalRow_size row.main

@[simp] theorem transportMemoryBumpTable_component
    (rows : List (CoreAIR.Current.Row p .memoryBump)) (data : ProverData (ZMod p)) :
    (transportMemoryBumpTable rows data).component = ⟨MemoryBumpChip.circuit⟩ := rfl

@[simp] theorem transportStateBumpTable_component
    (rows : List (CoreAIR.Current.Row p .stateBump)) (data : ProverData (ZMod p)) :
    (transportStateBumpTable rows data).component = ⟨StateBumpChip.circuit⟩ := rfl

@[simp] theorem transportMemoryBumpTable_data
    (rows : List (CoreAIR.Current.Row p .memoryBump)) (data : ProverData (ZMod p)) :
    (transportMemoryBumpTable rows data).data = data := rfl

@[simp] theorem transportStateBumpTable_data
    (rows : List (CoreAIR.Current.Row p .stateBump)) (data : ProverData (ZMod p)) :
    (transportStateBumpTable rows data).data = data := rfl

@[simp] theorem transportMemoryBumpTable_length
    (rows : List (CoreAIR.Current.Row p .memoryBump)) (data : ProverData (ZMod p)) :
    (transportMemoryBumpTable rows data).length = rows.length :=
  List.length_map ..

@[simp] theorem transportStateBumpTable_length
    (rows : List (CoreAIR.Current.Row p .stateBump)) (data : ProverData (ZMod p)) :
    (transportStateBumpTable rows data).length = rows.length :=
  List.length_map ..

/-- Exact `MemoryBump` row assertions imply all constraints of the reconstructed native table. -/
theorem transportMemoryBumpTable_constraints
    (publicValues : SP1PublicValues (ZMod p))
    (rows : List (CoreAIR.Current.Row p .memoryBump)) (data : ProverData (ZMod p))
    (valid : ∀ row ∈ rows,
      List.Forall (· = 0) (CoreAIR.Current.assertions publicValues .memoryBump row)) :
    (transportMemoryBumpTable rows data).Constraints := by
  intro nativeRow hrow
  obtain ⟨row, hmem, rfl⟩ := List.mem_map.mp hrow
  change (⟨MemoryBumpChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold
    (Faithful.memoryBumpEnvironment row.main data)
  apply (Faithful.memoryBumpChipConstraintsConstructive
    row.preprocessed publicValues.toBaseVector row.main data).mp
  exact valid row hmem

/-- Exact `StateBump` row assertions imply all constraints of the reconstructed native table. -/
theorem transportStateBumpTable_constraints
    (publicValues : SP1PublicValues (ZMod p))
    (rows : List (CoreAIR.Current.Row p .stateBump)) (data : ProverData (ZMod p))
    (valid : ∀ row ∈ rows,
      List.Forall (· = 0) (CoreAIR.Current.assertions publicValues .stateBump row)) :
    (transportStateBumpTable rows data).Constraints := by
  intro nativeRow hrow
  obtain ⟨row, hmem, rfl⟩ := List.mem_map.mp hrow
  change (⟨StateBumpChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold
    (Faithful.stateBumpEnvironment row.main data)
  apply (Faithful.stateBumpChipConstraintsConstructive
    row.preprocessed publicValues.toBaseVector row.main data).mp
  exact valid row hmem

/-! ## Interaction preservation -/

/-- `MemoryBump` transport preserves the complete interaction list, row order included. -/
theorem transportMemoryBumpTable_accesses
    (publicValues : SP1PublicValues (ZMod p))
    (rows : List (CoreAIR.Current.Row p .memoryBump)) (data : ProverData (ZMod p)) :
    tableNativeAccesses (transportMemoryBumpTable rows data) =
      rows.flatMap fun row =>
        (CoreAIR.Current.interactions publicValues .memoryBump row).map
          Extracted.Interaction.toAccess := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [tableNativeAccesses, transportMemoryBumpTable, List.map_cons, List.flatMap_cons]
    change
      Faithful.nativeAccesses (Faithful.memoryBumpEnvironment row.main data)
          (⟨MemoryBumpChip.circuit (p := p)⟩ : Component (ZMod p)).operations ++
        tableNativeAccesses (transportMemoryBumpTable rest data) =
      (CoreAIR.Current.interactions publicValues .memoryBump row).map
          Extracted.Interaction.toAccess ++
        (rest.flatMap fun row =>
          (CoreAIR.Current.interactions publicValues .memoryBump row).map
            Extracted.Interaction.toAccess)
    rw [Faithful.memoryBumpChipInteractionsConstructive
      row.preprocessed publicValues.toBaseVector row.main data, ih]
    rfl

/-- `StateBump` transport preserves the complete interaction list, row order included. -/
theorem transportStateBumpTable_accesses
    (publicValues : SP1PublicValues (ZMod p))
    (rows : List (CoreAIR.Current.Row p .stateBump)) (data : ProverData (ZMod p)) :
    tableNativeAccesses (transportStateBumpTable rows data) =
      rows.flatMap fun row =>
        (CoreAIR.Current.interactions publicValues .stateBump row).map
          Extracted.Interaction.toAccess := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [tableNativeAccesses, transportStateBumpTable, List.map_cons, List.flatMap_cons]
    change
      Faithful.nativeAccesses (Faithful.stateBumpEnvironment row.main data)
          (⟨StateBumpChip.circuit (p := p)⟩ : Component (ZMod p)).operations ++
        tableNativeAccesses (transportStateBumpTable rest data) =
      (CoreAIR.Current.interactions publicValues .stateBump row).map
          Extracted.Interaction.toAccess ++
        (rest.flatMap fun row =>
          (CoreAIR.Current.interactions publicValues .stateBump row).map
            Extracted.Interaction.toAccess)
    rw [Faithful.stateBumpChipInteractionsConstructive
      row.preprocessed publicValues.toBaseVector row.main data, ih]
    rfl

/-! ## The exact execution witness supplies the premises -/

/-- The two exact system tables transported in their native ensemble order: MemoryBump first,
StateBump second (positions 51 and 52 of the fifty-three-table ensemble). -/
def extractedBumpTables (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) : List (Table (ZMod p)) :=
  [ transportMemoryBumpTable (witness.trace.rows .memoryBump) data,
    transportStateBumpTable (witness.trace.rows .stateBump) data ]

/-- The transported segment has exactly the two native bump components, in ensemble order. -/
theorem extractedBumpTables_components
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) (data : ProverData (ZMod p)) :
    (extractedBumpTables witness data).map (·.component) =
      [⟨MemoryBumpChip.circuit⟩, ⟨StateBumpChip.circuit⟩] := rfl

/-- Both transported tables share the caller-selected committed prover data. -/
theorem extractedBumpTables_data
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) (data : ProverData (ZMod p)) :
    ∀ table ∈ extractedBumpTables witness data, table.data = data := by
  intro table hmem
  simp only [extractedBumpTables, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> rfl

/-- **Closed exact-system transport.** A valid exact execution-cluster witness supplies all native
constraints for both bump tables; there is no additional semantic or preprocessing premise. -/
theorem extractedBumpTables_constraints {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p))
    (valid : CoreAIR.Current.Relation binds .execution statement witness) :
    ∀ table ∈ extractedBumpTables witness data, table.Constraints := by
  have rowValid : ∀ table row, row ∈ witness.trace.rows table →
      List.Forall (· = 0) (CoreAIR.Current.assertions statement.publicValues table row) :=
    valid.2.2.1
  intro table hmem
  simp only [extractedBumpTables, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact transportMemoryBumpTable_constraints statement.publicValues _ data
      (fun row hrow => rowValid .memoryBump row hrow)
  · exact transportStateBumpTable_constraints statement.publicValues _ data
      (fun row hrow => rowValid .stateBump row hrow)

/-- The complete native access list of the transported bump segment is exactly the projected exact
Rust access list of those two tables.  This is the segment-level balance-preservation statement
needed when the whole execution cluster is assembled. -/
theorem extractedBumpTables_accesses {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) :
    (extractedBumpTables witness data).flatMap tableNativeAccesses =
      ((witness.trace.rows .memoryBump).flatMap fun row =>
          (CoreAIR.Current.interactions statement.publicValues .memoryBump row).map
            Extracted.Interaction.toAccess) ++
        ((witness.trace.rows .stateBump).flatMap fun row =>
          (CoreAIR.Current.interactions statement.publicValues .stateBump row).map
            Extracted.Interaction.toAccess) := by
  simp only [extractedBumpTables, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [transportMemoryBumpTable_accesses, transportStateBumpTable_accesses]

end SP1Clean.Faithful.Transport
