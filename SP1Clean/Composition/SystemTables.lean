import SP1Clean.Faithful.CoreAIR
import SP1Clean.Faithful.MemoryBumpChip
import SP1Clean.Faithful.StateBumpChip
import SP1Clean.Composition.Table
import SP1Clean.Proofs.Chips.HaltChip.Witgen
import SP1Clean.Proofs.Chips.SyscallInstrsChip.Witgen
import ToClean.Air.TableBuild

/-! # Exact Core system rows transported to native tables

The retained v6.4 MemoryBump and StateBump faithfulness anchors supply native constraints and the
complete interaction lists of the reconstructed physical rows. Their constructors are independent
of prover data; every theorem states its evaluation data explicitly.

The conditional legacy transport also supplies one padding HALT row and an empty SyscallInstrs
table. These are temporary limits of that transport, not the native library's host-call domain.
The syscall cluster must be transported or its live comparison consumers replaced before this
migration evidence can be retired. Provider redistribution and boundary authentication are separate.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

open SP1Clean.Faithful

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
def transportMemoryBumpTable (rows : List (CoreAIR.Current.Row p .memoryBump)) : Table (ZMod p) where
  component := { circuit := MemoryBumpChip.circuit }
  table := rows.map transportMemoryBumpRow
  uniform_width := by
    intro nativeRow hrow
    obtain ⟨row, -, rfl⟩ := List.mem_map.mp hrow
    exact Faithful.memoryBumpPhysicalRow_size row.main

/-- The exact `StateBump` rows, installed as the native `StateBumpChip` table. -/
def transportStateBumpTable (rows : List (CoreAIR.Current.Row p .stateBump)) : Table (ZMod p) where
  component := { circuit := StateBumpChip.circuit }
  table := rows.map transportStateBumpRow
  uniform_width := by
    intro nativeRow hrow
    obtain ⟨row, -, rfl⟩ := List.mem_map.mp hrow
    exact Faithful.stateBumpPhysicalRow_size row.main

@[simp] theorem transportMemoryBumpTable_component
    (rows : List (CoreAIR.Current.Row p .memoryBump)) :
    (transportMemoryBumpTable rows).component = { circuit := MemoryBumpChip.circuit } := rfl

@[simp] theorem transportStateBumpTable_component
    (rows : List (CoreAIR.Current.Row p .stateBump)) :
    (transportStateBumpTable rows).component = { circuit := StateBumpChip.circuit } := rfl

@[simp] theorem transportMemoryBumpTable_length
    (rows : List (CoreAIR.Current.Row p .memoryBump)) :
    (transportMemoryBumpTable rows).length = rows.length :=
  List.length_map ..

@[simp] theorem transportStateBumpTable_length
    (rows : List (CoreAIR.Current.Row p .stateBump)) :
    (transportStateBumpTable rows).length = rows.length :=
  List.length_map ..

/-- Exact `MemoryBump` row assertions imply all constraints of the reconstructed native table. -/
theorem transportMemoryBumpTable_constraints
    (publicValues : SP1PublicValues (ZMod p))
    (rows : List (CoreAIR.Current.Row p .memoryBump)) (data : ProverData (ZMod p))
    (valid : ∀ row ∈ rows,
      List.Forall (· = 0) (CoreAIR.Current.assertions publicValues .memoryBump row)) :
    (transportMemoryBumpTable rows).Constraints data := by
  intro nativeRow hrow
  obtain ⟨row, hmem, rfl⟩ := List.mem_map.mp hrow
  change ({ circuit := MemoryBumpChip.circuit (p := p) } : Component (ZMod p)).operations.ConstraintsHold
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
    (transportStateBumpTable rows).Constraints data := by
  intro nativeRow hrow
  obtain ⟨row, hmem, rfl⟩ := List.mem_map.mp hrow
  change ({ circuit := StateBumpChip.circuit (p := p) } : Component (ZMod p)).operations.ConstraintsHold
    (Faithful.stateBumpEnvironment row.main data)
  apply (Faithful.stateBumpChipConstraintsConstructive
    row.preprocessed publicValues.toBaseVector row.main data).mp
  exact valid row hmem

/-! ## Interaction preservation -/

/-- `MemoryBump` transport preserves the complete interaction list, row order included. -/
theorem transportMemoryBumpTable_accesses
    (publicValues : SP1PublicValues (ZMod p))
    (rows : List (CoreAIR.Current.Row p .memoryBump)) (data : ProverData (ZMod p)) :
    tableNativeAccesses (transportMemoryBumpTable rows) data =
      rows.flatMap fun row =>
        (CoreAIR.Current.interactions publicValues .memoryBump row).map
          Extracted.Interaction.toAccess := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [tableNativeAccesses, transportMemoryBumpTable, List.map_cons, List.flatMap_cons]
    change
      Faithful.nativeAccesses (Faithful.memoryBumpEnvironment row.main data)
          ({ circuit := MemoryBumpChip.circuit (p := p) } : Component (ZMod p)).operations ++
        tableNativeAccesses (transportMemoryBumpTable rest) data =
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
    tableNativeAccesses (transportStateBumpTable rows) data =
      rows.flatMap fun row =>
        (CoreAIR.Current.interactions publicValues .stateBump row).map
          Extracted.Interaction.toAccess := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [tableNativeAccesses, transportStateBumpTable, List.map_cons, List.flatMap_cons]
    change
      Faithful.nativeAccesses (Faithful.stateBumpEnvironment row.main data)
          ({ circuit := StateBumpChip.circuit (p := p) } : Component (ZMod p)).operations ++
        tableNativeAccesses (transportStateBumpTable rest) data =
      (CoreAIR.Current.interactions publicValues .stateBump row).map
          Extracted.Interaction.toAccess ++
        (rest.flatMap fun row =>
          (CoreAIR.Current.interactions publicValues .stateBump row).map
            Extracted.Interaction.toAccess)
    rw [Faithful.stateBumpChipInteractionsConstructive
      row.preprocessed publicValues.toBaseVector row.main data, ih]
    rfl

/-! ## The exact execution witness supplies the premises -/

/-- The exact v6.4.0 cluster has no Halt table (its syscall path runs through `SyscallInstrs` +
the global syscall tables, outside the transported profile), so the exact→native transport
supplies the native ensemble's mandatory one-padding-row Halt table directly. Its `⟨0⟩` Exit push
balances the boundary verifier's ungated `⟨exit_code⟩` pull, which is what restricts this
conditional transport to shards committing `exit_code = 0` — halting shards rejoin when the
syscall cluster itself is transported (roadmap Track 3). -/
def extractedHaltTable (data : ProverData (ZMod p)) : Table (ZMod p) :=
  Table.build HaltChip.component (HaltChip.haltTraceInputs []) data (ProverHint.empty (ZMod p))

/-- The exact-side `SyscallInstrs` table: no rows.

The transport does not carry SP1's `SyscallInstrs` matrix — that is a separate piece of work — so
this manufactures the empty table the native ensemble's position 54 expects. An empty table is
exactly as strong a claim as it looks: it composes the two halves for the *other* fifty-four
positions and asserts nothing about SP1's syscall rows. -/
def extractedSyscallInstrsTable (data : ProverData (ZMod p)) : Table (ZMod p) :=
  Table.build SyscallInstrsChip.component (SyscallInstrsChip.syscallInstrsTraceInputs []) data
    (ProverHint.empty (ZMod p))

/-- The empty `SyscallInstrs` table contributes no accesses, so it disturbs no balance. -/
@[simp] theorem extractedSyscallInstrsTable_accesses (data : ProverData (ZMod p)) :
    tableNativeAccesses (extractedSyscallInstrsTable (p := p) data) data = [] := by
  rfl

/-- The four exact-side system tables transported in their native ensemble order: MemoryBump
first, StateBump second, the manufactured padding Halt table third, and the empty `SyscallInstrs`
table last (positions 51–54 of the fifty-five-table ensemble). -/
def extractedBumpTables (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) : List (Table (ZMod p)) :=
  [ transportMemoryBumpTable (witness.trace.rows .memoryBump),
    transportStateBumpTable (witness.trace.rows .stateBump),
    extractedHaltTable data,
    extractedSyscallInstrsTable data ]

/-- The transported segment has exactly the four native system components, in ensemble order. -/
theorem extractedBumpTables_components
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) (data : ProverData (ZMod p)) :
    (extractedBumpTables witness data).map (·.component) =
      [{ circuit := MemoryBumpChip.circuit }, { circuit := StateBumpChip.circuit },
       { circuit := HaltChip.circuit }, { circuit := SyscallInstrsChip.circuit }] := rfl

/-- **Closed exact-system transport.** A valid exact execution-cluster witness supplies all native
constraints for both bump tables; there is no additional semantic or preprocessing premise. -/
theorem extractedBumpTables_constraints {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p))
    (valid : CoreAIR.Current.Relation binds .execution statement witness) :
    ∀ table ∈ extractedBumpTables witness data, table.Constraints data := by
  have rowValid : ∀ table row, row ∈ witness.trace.rows table →
      List.Forall (· = 0) (CoreAIR.Current.assertions statement.publicValues table row) :=
    fun _ _ rowMem => (CoreAIR.Current.system binds).localValid_of_relationFor valid rowMem
  intro table hmem
  simp only [extractedBumpTables, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact transportMemoryBumpTable_constraints statement.publicValues _ data
      (fun row hrow => rowValid .memoryBump row hrow)
  · exact transportStateBumpTable_constraints statement.publicValues _ data
      (fun row hrow => rowValid .stateBump row hrow)
  · exact HaltChip.traceTable_constraints _ _ _ (HaltChip.haltTraceInputs_spec [])
  · exact SyscallInstrsChip.traceTable_constraints [] _ _

/-- The complete native access list of the transported bump segment is exactly the projected exact
Rust access list of those two tables, followed by the manufactured padding Halt table's own native
accesses (the exact cluster has no Halt table to compare against).  This is the segment-level
balance-preservation statement needed when the whole execution cluster is assembled. -/
theorem extractedBumpTables_accesses {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) :
    (extractedBumpTables witness data).flatMap (tableNativeAccesses · data) =
      ((witness.trace.rows .memoryBump).flatMap fun row =>
          (CoreAIR.Current.interactions statement.publicValues .memoryBump row).map
            Extracted.Interaction.toAccess) ++
        (((witness.trace.rows .stateBump).flatMap fun row =>
          (CoreAIR.Current.interactions statement.publicValues .stateBump row).map
            Extracted.Interaction.toAccess) ++
          tableNativeAccesses (extractedHaltTable data) data) := by
  simp only [extractedBumpTables, List.flatMap_cons, List.flatMap_nil,
    extractedSyscallInstrsTable_accesses, List.append_nil]
  rw [transportMemoryBumpTable_accesses, transportStateBumpTable_accesses]

end SP1Clean.Composition
