import SP1Clean.Proofs.Completeness.Providers
import SP1Clean.FormalModel.TraceGen.Bump
import SP1Clean.Proofs.Chips.AddChip.Complete
import SP1Clean.Proofs.Chips.AddiChip.Complete
import SP1Clean.Proofs.Chips.AddwChip.Complete
import SP1Clean.Proofs.Chips.SubChip.Complete
import SP1Clean.Proofs.Chips.SubwChip.Complete
import SP1Clean.Proofs.Chips.BitwiseChip.Complete
import SP1Clean.Proofs.Chips.LtChip.Complete
import SP1Clean.Proofs.Chips.ShiftLeftChip.Complete
import SP1Clean.Proofs.Chips.ShiftRightChip.Complete
import SP1Clean.Proofs.Chips.JalChip.Complete
import SP1Clean.Proofs.Chips.JalrChip.Complete
import SP1Clean.Proofs.Chips.BranchChip.Complete
import SP1Clean.Proofs.Chips.UTypeChip.Complete
import SP1Clean.Proofs.Chips.LoadByteChip.Complete
import SP1Clean.Proofs.Chips.LoadHalfChip.Complete
import SP1Clean.Proofs.Chips.LoadWordChip.Complete
import SP1Clean.Proofs.Chips.LoadDoubleChip.Complete
import SP1Clean.Proofs.Chips.LoadX0Chip.Complete
import SP1Clean.Proofs.Chips.StoreByteChip.Complete
import SP1Clean.Proofs.Chips.StoreHalfChip.Complete
import SP1Clean.Proofs.Chips.StoreWordChip.Complete
import SP1Clean.Proofs.Chips.StoreDoubleChip.Complete
import SP1Clean.Proofs.Chips.MulChip.Complete
import SP1Clean.Proofs.Chips.DivRemChip.Complete
import SP1Clean.Proofs.Chips.AluX0Chip.Complete
import ToClean.Air.EnsembleBuild

/-! # Assembling one shard's AIR witness from a generated trace

The join of the two completeness layers below it: the twenty-five per-chip
`Proofs/Chips/<Chip>/Complete.lean` files and the 28 provider tables plus verifier row of
`Proofs/Completeness/Providers.lean`. Each of those says *one* table built from semantic
occurrences satisfies its constraints and channel guarantees. This file says the 53 of them,
assembled in the ensemble's own order with one shared committed `ProverData`, form a Clean
`EnsembleWitness` for `sp1Ensemble` — and that its `Constraints` hold.

## What a `SupportedCoreTraceWitness` is

Exactly the data a trace generator emits: one registry-indexed list of execution events per
instruction chip, one registry-indexed list of occurrences per provider/boundary table, the shared
committed prover data and hint, and the shard's public clock/pc endpoints. It is a *flat data
record*, not an execution: whether the events describe a real Sail chain is stated by the relation
in `Soundness/AIRCompleteness.lean`, not here.

## Two explicit construction choices

* **The native trace is unpadded.** Every instruction builder that accepts a padding count receives
  zero. Physical power-of-two shape belongs to the exact-Core adapter rather than the semantic
  Clean ensemble witness.
* **Provider multiplicity is part of each semantic occurrence.** Byte/Range/Program entries may be
  unit-count occurrences, aggregated equal keys, or zero-count padding; memory-boundary entries
  carry an explicit boolean selector. No local witness silently replaces the generator's choice.

## Where the layering lands

The trace record lives here rather than on the `FormalModel/` audit surface because the provider
occurrence types (`TraceGen.ByteEntry` and friends) do — for the reason
`Proofs/Completeness/Providers.lean` documents: the provider `Inputs` types are declared inside
`Proofs/Chips/`, so a `FormalModel`-resident trace model would invert the layering.
-/

/-! ## Completeness-side realizations of the neutral table identities

The Model-layer identity modules intentionally know nothing about trace-generation records.  This
higher layer supplies the dependent payload and validity families used by the generated witness.
-/

namespace SP1Clean.InstructionChipId

open SP1Clean.TraceGen

/-- Semantic event type routed to one instruction table. -/
def Event : InstructionChipId → Type
  | .add => RTypeEvent
  | .addi => ITypeEvent
  | .addw => ALUTypeEvent
  | .sub => RTypeEvent
  | .subw => RTypeEvent
  | .bitwise => ALUTypeEvent
  | .lt => ALUTypeEvent
  | .shiftLeft => ALUTypeEvent
  | .shiftRight => ALUTypeEvent
  | .jal => JTypeEvent
  | .jalr => ITypeEvent
  | .branch => ITypeEvent
  | .uType => JTypeEvent
  | .loadByte => MemoryEvent
  | .loadHalf => MemoryEvent
  | .loadWord => MemoryEvent
  | .loadDouble => MemoryEvent
  | .loadX0 => MemoryEvent
  | .storeByte => MemoryEvent
  | .storeHalf => MemoryEvent
  | .storeWord => MemoryEvent
  | .storeDouble => MemoryEvent
  | .mul => RTypeEvent
  | .divRem => RTypeEvent
  | .aluX0 => ALUTypeEvent

/-- Routing and semantic side condition required by one instruction table's trace builder. -/
def Valid : (id : InstructionChipId) → id.Event → Prop
  | .add, e => e.WellFormed
  | .addi, e => e.WellFormed
  | .addw, e => e.WellFormed
  | .sub, e => e.WellFormed
  | .subw, e => e.WellFormed
  | .bitwise, e => e.WellFormed ∧ e.IsBitwise
  | .lt, e => e.WellFormed ∧ e.IsLt
  | .shiftLeft, e => e.WellFormed ∧ e.IsShiftLeft
  | .shiftRight, e => e.WellFormed ∧ e.IsShiftRight
  | .jal, e => e.WellFormedJal ∧ e.JalTargets
  | .jalr, e => e.WellFormedJalr ∧ e.JalrTargets
  | .branch, e => e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets
  | .uType, e => e.WellFormedUType ∧ e.UTypeImm
  | .loadByte, e => e.WellFormed ∧ (e.opcode = 29 ∨ e.opcode = 32)
  | .loadHalf, e => e.WellFormed ∧ e.Aligned 2
  | .loadWord, e => e.WellFormed ∧ e.Aligned 4
  | .loadDouble, e => e.WellFormed ∧ e.Aligned 8
  | .loadX0, e => e.WellFormedX0 ∧ e.IsLoad
  | .storeByte, e => e.WellFormedStore
  | .storeHalf, e => e.WellFormedStore ∧ e.Aligned 2
  | .storeWord, e => e.WellFormedStore ∧ e.Aligned 4
  | .storeDouble, e => e.WellFormedStore ∧ e.Aligned 8
  | .mul, e => e.WellFormed ∧ e.IsMul
  | .divRem, e => e.WellFormed ∧ e.IsDivRem
  | .aluX0, e => e.WellFormedX0

end SP1Clean.InstructionChipId

namespace SP1Clean.ProviderTableId

open SP1Clean.TraceGen

/-- Semantic occurrence type routed to one provider, boundary, or bump table. -/
def Occurrence : ProviderTableId → Type
  | .byte _ => ByteEntry
  | .range _ => RangeEntry
  | .program => RomEntry
  | .memoryInit => MemRecordEntry
  | .memoryFinalize => MemRecordEntry
  | .memoryBump => MemoryBumpEvent
  | .stateBump => StateBumpEvent
  -- The deterministic compiler emits no real halt rows yet; `Empty` makes that type-level (the
  -- 2.4b tranche replaces it with the semantic halt event). The halt table itself is never empty:
  -- `HaltChip.haltTraceInputs [] = [paddingInputs]`, whose `⟨0⟩` Exit push balances the verifier.
  | .halt => Empty

/-- Side condition required by one provider table's trace builder. -/
def Valid : (id : ProviderTableId) → id.Occurrence → Prop
  | .byte _, e => e.WellFormed
  | .range width, e => e.WellFormed width.val
  | .program, e => e.WellFormed
  | .memoryInit, e => e.WellFormedInit
  | .memoryFinalize, _ => True
  | .memoryBump, e => e.WellFormed
  | .stateBump, e => e.WellFormed
  | .halt, e => e.elim

end SP1Clean.ProviderTableId

namespace SP1Clean.Soundness

open Circuit
open Air.Flat (Component Table EnsembleWitness)
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance traceAssemblyFieldBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-! ## The generated trace -/

/--
**One shard's generated trace**, indexed by the two neutral registries that fix
`sp1Ensemble`'s table order.

`instructionEvents id` carries the typed semantic events routed to instruction table `id`;
`providerOccurrences id` carries what consumers ask provider/boundary table `id` to justify.
`data` is the one committed `ProverData` every table shares (Clean's
`EnsembleWitness.same_data`), `hint` the prover hint the unhinted tables witness at, and `boundary`
is the shard's public input in the one representation consumed by the verifier table.  In
particular, the trace does not retain a second natural-number copy of the four endpoints.
-/
structure SupportedCoreTraceWitness (p : ℕ) [Fact p.Prime] [Fact (2 ^ 25 < p)] where
  instructionEvents : (id : InstructionChipId) → List id.Event
  providerOccurrences : (id : ProviderTableId) → List id.Occurrence
  -- Shared prover state and the public boundary.
  data : ProverData (ZMod p)
  hint : ProverHint (ZMod p)
  boundary : SP1PublicIO (ZMod p)

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/--
**A generated trace is well-formed** when every event or occurrence it emits satisfies the side
condition selected by the same registry identity — the exact premise of that table's
`traceTable_constraints` theorem.

Nothing here is a range fact about a *witnessed* cell: those are the circuits' own business, and
witness generation supplies them. What a generator owes is that the semantic content it routed to
a table belongs there — an `AND` event to the bitwise chip, an aligned address to the word-load
chip, a byte-sized operand pair to a byte provider.
-/
structure WellFormed : Prop where
  instruction : ∀ id e, e ∈ trace.instructionEvents id → id.Valid e
  provider : ∀ id e, e ∈ trace.providerOccurrences id → id.Valid e
  boundary : trace.boundary.LimbBounds

/-! ## The 53 tables -/

/-- The shard's public boundary row, stored exactly as the verifier reads it. -/
def publicValues : SP1PublicIO (ZMod p) := trace.boundary

/--
**The 53 built tables**, in `sp1Ensemble.tables` order: the twenty-five instruction chips of
`sp1Tables`, then the 28 entries of `sp1ProviderTables`.

Seven of them go through `Table.buildHinted` rather than `Table.build` — the chips whose witness
generation reads a per-row prover hint (the flag one-hots of Bitwise/Lt/the shifts/Mul/DivRem, the
comparison selector of Branch). Their builders pair each event with the hint that event's own row
is witnessed at; everything else shares the trace's single `hint`.
-/
def rangeTables : List (Table (ZMod p)) :=
  RangeChip.allWidths.map fun width =>
    Table.build (RangeChip.componentFor width)
      (RangeChip.traceInputs (trace.providerOccurrences (.range width))) trace.data trace.hint

/-- Build the instruction table selected by one stable instruction-chip identity.  This is the
completeness-side realization of `InstructionChipId`: the identity fixes both the semantic event
field read from the trace and whether witness generation uses a shared or per-row hint. -/
def instructionTableFor : InstructionChipId → Table (ZMod p)
  | .add => Table.build AddChip.component
      (AddChip.traceInputs (trace.instructionEvents .add) 0) trace.data trace.hint
  | .addi => Table.build AddiChip.component
      (AddiChip.traceInputs (trace.instructionEvents .addi) 0) trace.data trace.hint
  | .addw => Table.build AddwChip.component
      (AddwChip.traceInputs (trace.instructionEvents .addw) 0) trace.data trace.hint
  | .sub => Table.build SubChip.component
      (SubChip.traceInputs (trace.instructionEvents .sub) 0) trace.data trace.hint
  | .subw => Table.build SubwChip.component
      (SubwChip.traceInputs (trace.instructionEvents .subw) 0) trace.data trace.hint
  | .bitwise => Table.buildHinted BitwiseChip.component
      (BitwiseChip.traceInputs (trace.instructionEvents .bitwise) 0) trace.data
  | .lt => Table.buildHinted LtChip.component
      (LtChip.traceInputs (trace.instructionEvents .lt) 0) trace.data
  | .shiftLeft => Table.buildHinted ShiftLeftChip.component
      (ShiftLeftChip.traceInputs (trace.instructionEvents .shiftLeft) 0) trace.data
  | .shiftRight => Table.buildHinted ShiftRightChip.component
      (ShiftRightChip.traceInputs (trace.instructionEvents .shiftRight) 0) trace.data
  | .jal => Table.build JalChip.component
      (JalChip.traceInputs (trace.instructionEvents .jal) 0) trace.data trace.hint
  | .jalr => Table.build JalrChip.component
      (JalrChip.traceInputs (trace.instructionEvents .jalr) 0) trace.data trace.hint
  | .branch => Table.buildHinted BranchChip.component
      (BranchChip.traceInputs (trace.instructionEvents .branch) 0) trace.data
  | .uType => Table.build UTypeChip.component
      (UTypeChip.traceInputs (trace.instructionEvents .uType) 0) trace.data trace.hint
  | .loadByte => Table.build LoadByteChip.component
      (LoadByteChip.traceInputs (trace.instructionEvents .loadByte)) trace.data trace.hint
  | .loadHalf => Table.build LoadHalfChip.component
      (LoadHalfChip.traceInputs (trace.instructionEvents .loadHalf)) trace.data trace.hint
  | .loadWord => Table.build LoadWordChip.component
      (LoadWordChip.traceInputs (trace.instructionEvents .loadWord)) trace.data trace.hint
  | .loadDouble => Table.build LoadDoubleChip.component
      (LoadDoubleChip.traceInputs (trace.instructionEvents .loadDouble)) trace.data trace.hint
  | .loadX0 => Table.build LoadX0Chip.component
      (LoadX0Chip.traceInputs (trace.instructionEvents .loadX0)) trace.data trace.hint
  | .storeByte => Table.build StoreByteChip.component
      (StoreByteChip.traceInputs (trace.instructionEvents .storeByte)) trace.data trace.hint
  | .storeHalf => Table.build StoreHalfChip.component
      (StoreHalfChip.traceInputs (trace.instructionEvents .storeHalf)) trace.data trace.hint
  | .storeWord => Table.build StoreWordChip.component
      (StoreWordChip.traceInputs (trace.instructionEvents .storeWord)) trace.data trace.hint
  | .storeDouble => Table.build StoreDoubleChip.component
      (StoreDoubleChip.traceInputs (trace.instructionEvents .storeDouble)) trace.data trace.hint
  | .mul => Table.buildHinted MulChip.component
      (MulChip.traceInputs (trace.instructionEvents .mul) 0) trace.data
  | .divRem => Table.buildHinted DivRemChip.component
      (DivRemChip.traceInputs (trace.instructionEvents .divRem) 0) trace.data
  | .aluX0 => Table.build AluX0Chip.component
      (AluX0Chip.traceInputs (trace.instructionEvents .aluX0) 0) trace.data trace.hint

/-- The twenty-five built instruction tables, in the one physical order fixed by the neutral
instruction registry. -/
def instructionTables : List (Table (ZMod p)) :=
  InstructionChipId.all.map trace.instructionTableFor

/-- Pointwise positional agreement between the completeness builder and the circuit-bearing
supported-machine registry. -/
@[simp] theorem instructionTableFor_component (id : InstructionChipId) :
    (trace.instructionTableFor id).component = (supportedChipFor (p := p) id).table := by
  cases id <;> rfl

/-- Every instruction table carries the trace's shared committed prover data. -/
@[simp] theorem instructionTableFor_data (id : InstructionChipId) :
    (trace.instructionTableFor id).data = trace.data := by
  cases id <;> rfl

/-- Pointwise instruction-table completeness.  This is the sole proof that dispatches on all
twenty-five instruction identities; list-level assembly below only reasons through `List.map`. -/
theorem instructionTableFor_constraints (wf : trace.WellFormed) (id : InstructionChipId) :
    (trace.instructionTableFor id).Constraints := by
  cases id with
  | add => exact AddChip.traceTable_constraints _ _ _ _ (wf.instruction .add)
  | addi => exact AddiChip.traceTable_constraints _ _ _ _ (wf.instruction .addi)
  | addw => exact AddwChip.traceTable_constraints _ _ _ _ (wf.instruction .addw)
  | sub => exact SubChip.traceTable_constraints _ _ _ _ (wf.instruction .sub)
  | subw => exact SubwChip.traceTable_constraints _ _ _ _ (wf.instruction .subw)
  | bitwise => exact BitwiseChip.traceTable_constraints _ _ _ (wf.instruction .bitwise)
  | lt => exact LtChip.traceTable_constraints _ _ _ (wf.instruction .lt)
  | shiftLeft => exact ShiftLeftChip.traceTable_constraints _ _ _ (wf.instruction .shiftLeft)
  | shiftRight => exact ShiftRightChip.traceTable_constraints _ _ _ (wf.instruction .shiftRight)
  | jal => exact JalChip.traceTable_constraints _ _ _ _ (wf.instruction .jal)
  | jalr => exact JalrChip.traceTable_constraints _ _ _ _ (wf.instruction .jalr)
  | branch => exact BranchChip.traceTable_constraints _ _ _ (wf.instruction .branch)
  | uType => exact UTypeChip.traceTable_constraints _ _ _ _ (wf.instruction .uType)
  | loadByte => exact LoadByteChip.traceTable_constraints _ _ _ (wf.instruction .loadByte)
  | loadHalf => exact LoadHalfChip.traceTable_constraints _ _ _ (wf.instruction .loadHalf)
  | loadWord => exact LoadWordChip.traceTable_constraints _ _ _ (wf.instruction .loadWord)
  | loadDouble => exact LoadDoubleChip.traceTable_constraints _ _ _ (wf.instruction .loadDouble)
  | loadX0 => exact LoadX0Chip.traceTable_constraints _ _ _ (wf.instruction .loadX0)
  | storeByte => exact StoreByteChip.traceTable_constraints _ _ _ (wf.instruction .storeByte)
  | storeHalf => exact StoreHalfChip.traceTable_constraints _ _ _ (wf.instruction .storeHalf)
  | storeWord => exact StoreWordChip.traceTable_constraints _ _ _ (wf.instruction .storeWord)
  | storeDouble => exact StoreDoubleChip.traceTable_constraints _ _ _ (wf.instruction .storeDouble)
  | mul => exact MulChip.traceTable_constraints _ _ _ (wf.instruction .mul)
  | divRem => exact DivRemChip.traceTable_constraints _ _ _ (wf.instruction .divRem)
  | aluX0 => exact AluX0Chip.traceTable_constraints _ _ _ _ (wf.instruction .aluX0)

/-- The completeness registry projects to the soundness registry component for component. -/
theorem instructionTables_map_component :
    trace.instructionTables.map (·.component) = sp1Tables := by
  simp only [instructionTables, sp1Tables, supportedChips, List.map_map]
  exact List.map_congr_left fun id _ => trace.instructionTableFor_component id

/-- Shared-data law lifted pointwise through the instruction registry. -/
theorem instructionTables_data :
    ∀ table ∈ trace.instructionTables, table.data = trace.data := by
  intro table tableMem
  rw [instructionTables] at tableMem
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp tableMem
  exact trace.instructionTableFor_data id

/-- Constraint completeness lifted pointwise through the instruction registry. -/
theorem instructionTables_constraints (wf : trace.WellFormed) :
    ∀ table ∈ trace.instructionTables, table.Constraints := by
  intro table tableMem
  rw [instructionTables] at tableMem
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp tableMem
  exact trace.instructionTableFor_constraints wf id

/-- Build the provider or boundary table selected by one stable provider identity.  This is the
completeness-side realization of `ProviderTableId`; it stays distinct from
`Soundness.providerTableFor`, whose codomain is a circuit component rather than a built witness
table. -/
def providerTableFor : ProviderTableId → Table (ZMod p)
  | .byte .u8Range => Table.build ByteChip.U8Range.component
      (ByteChip.U8Range.traceInputs (trace.providerOccurrences (.byte .u8Range)))
        trace.data trace.hint
  | .byte .msb => Table.build ByteChip.MSB.component
      (ByteChip.MSB.traceInputs (trace.providerOccurrences (.byte .msb))) trace.data trace.hint
  | .byte .andByte => Table.build ByteChip.AndByte.component
      (ByteChip.AndByte.traceInputs (trace.providerOccurrences (.byte .andByte)))
        trace.data trace.hint
  | .byte .orByte => Table.build ByteChip.OrByte.component
      (ByteChip.OrByte.traceInputs (trace.providerOccurrences (.byte .orByte)))
        trace.data trace.hint
  | .byte .xorByte => Table.build ByteChip.XorByte.component
      (ByteChip.XorByte.traceInputs (trace.providerOccurrences (.byte .xorByte)))
        trace.data trace.hint
  | .byte .ltu => Table.build ByteChip.Ltu.component
      (ByteChip.Ltu.traceInputs (trace.providerOccurrences (.byte .ltu))) trace.data trace.hint
  | .range width => Table.build (RangeChip.componentFor width)
      (RangeChip.traceInputs (trace.providerOccurrences (.range width))) trace.data trace.hint
  | .program => Table.build ProgramProviderChip.component
      (ProgramProviderChip.traceInputs (trace.providerOccurrences .program)) trace.data trace.hint
  | .memoryInit => Table.build MemoryProviderChip.component
      (MemoryProviderChip.traceInputs (trace.providerOccurrences .memoryInit))
        trace.data trace.hint
  | .memoryFinalize => Table.build MemoryFinalizeChip.component
      (MemoryFinalizeChip.traceInputs (trace.providerOccurrences .memoryFinalize))
        trace.data trace.hint
  | .memoryBump => Table.build MemoryBumpChip.component
      (memoryBumpTraceInputs (trace.providerOccurrences .memoryBump)) trace.data trace.hint
  | .stateBump => Table.build StateBumpChip.component
      (stateBumpTraceInputs (trace.providerOccurrences .stateBump)) trace.data trace.hint
  | .halt => Table.build HaltChip.component
      (HaltChip.haltTraceInputs (trace.providerOccurrences .halt)) trace.data trace.hint

/-- The twenty-nine built provider and boundary tables, in the one physical order fixed by the
neutral provider registry. -/
def providerTables : List (Table (ZMod p)) :=
  ProviderTableId.all.map trace.providerTableFor

/-- Pointwise positional agreement between the completeness provider builder and the
circuit-bearing soundness registry. -/
@[simp] theorem providerTableFor_component (id : ProviderTableId) :
    (trace.providerTableFor id).component =
      SP1Clean.Soundness.providerTableFor (p := p) id := by
  cases id with
  | byte provider => cases provider <;> rfl
  | range width => rfl
  | program => rfl
  | memoryInit => rfl
  | memoryFinalize => rfl
  | memoryBump => rfl
  | stateBump => rfl
  | halt => rfl

/-- Every provider table carries the trace's shared committed prover data. -/
@[simp] theorem providerTableFor_data (id : ProviderTableId) :
    (trace.providerTableFor id).data = trace.data := by
  cases id with
  | byte provider => cases provider <;> rfl
  | range width => rfl
  | program => rfl
  | memoryInit => rfl
  | memoryFinalize => rfl
  | memoryBump => rfl
  | stateBump => rfl
  | halt => rfl

/-- Pointwise provider-table completeness. This is the sole proof that dispatches on all provider
identities; list-level assembly below only reasons through `List.map`. -/
theorem providerTableFor_constraints (wf : trace.WellFormed) (id : ProviderTableId) :
    (trace.providerTableFor id).Constraints := by
  cases id with
  | byte provider =>
      cases provider with
      | u8Range =>
          exact ByteChip.U8Range.traceTable_constraints _ _ _
            (wf.provider (.byte .u8Range))
      | msb => exact ByteChip.MSB.traceTable_constraints _ _ _ (wf.provider (.byte .msb))
      | andByte =>
          exact ByteChip.AndByte.traceTable_constraints _ _ _
            (wf.provider (.byte .andByte))
      | orByte =>
          exact ByteChip.OrByte.traceTable_constraints _ _ _ (wf.provider (.byte .orByte))
      | xorByte =>
          exact ByteChip.XorByte.traceTable_constraints _ _ _
            (wf.provider (.byte .xorByte))
      | ltu => exact ByteChip.Ltu.traceTable_constraints _ _ _ (wf.provider (.byte .ltu))
  | range width =>
      exact RangeChip.traceTable_constraints _ (Nat.le_of_lt_succ width.isLt) _ _ _
        (wf.provider (.range width))
  | program =>
      exact ProgramProviderChip.traceTable_constraints _ _ _ (wf.provider .program)
  | memoryInit =>
      exact MemoryProviderChip.traceTable_constraints _ _ _ (wf.provider .memoryInit)
  | memoryFinalize => exact MemoryFinalizeChip.traceTable_constraints _ _ _
  | memoryBump =>
      exact MemoryBumpChip.traceTable_constraints _ _ _
        (memoryBumpTraceInputs_spec (wf.provider .memoryBump))
  | stateBump =>
      exact StateBumpChip.traceTable_constraints _ _ _
        (stateBumpTraceInputs_spec (wf.provider .stateBump))
  | halt =>
      exact HaltChip.traceTable_constraints _ _ _
        (HaltChip.haltTraceInputs_spec (trace.providerOccurrences .halt))

/-- The full 54-table assembly is the instruction registry followed by the provider segment. -/
def tables : List (Table (ZMod p)) :=
  trace.instructionTables ++ trace.providerTables

/-- The provider segment projects to the ensemble's provider components in physical order. -/
theorem providerTables_map_component :
    trace.providerTables.map (·.component) = sp1ProviderTables := by
  simp only [providerTables, sp1ProviderTables, List.map_map]
  exact List.map_congr_left fun id _ => trace.providerTableFor_component id

/-- Every provider table carries the trace's shared committed prover data. -/
theorem providerTables_data : ∀ table ∈ trace.providerTables, table.data = trace.data := by
  intro table tableMem
  rw [providerTables] at tableMem
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp tableMem
  exact trace.providerTableFor_data id

/-- Every well-formed provider occurrence segment builds constraint-satisfying tables. -/
theorem providerTables_constraints (wf : trace.WellFormed) :
    ∀ table ∈ trace.providerTables, table.Constraints := by
  intro table tableMem
  rw [providerTables] at tableMem
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp tableMem
  exact trace.providerTableFor_constraints wf id

/-- **The assembled tables are the ensemble's tables**, component for component and in order. One
`rfl`: every completeness-side `component` is by definition the wrapper `sp1Tables` /
`sp1ProviderTables` build, and `Table.build`/`Table.buildHinted` record the component they were
given. -/
theorem tables_map_component :
    (trace.tables.map (·.component)) = (sp1Ensemble (p := p)).tables := by
  rw [tables, List.map_append, instructionTables_map_component,
    providerTables_map_component, sp1Ensemble_tables]

/-- Every assembled table carries the trace's shared committed prover data — Clean's
`EnsembleWitness.same_data`. -/
theorem tables_data : ∀ table ∈ trace.tables, table.data = trace.data := by
  intro table hmem
  rw [tables] at hmem
  rcases List.mem_append.mp hmem with instructionMem | providerMem
  · exact trace.instructionTables_data table instructionMem
  · exact trace.providerTables_data table providerMem

/-! ## The assembled witness -/

/-- **The shard's AIR witness.** The 53 built tables in ensemble order, the shared committed
prover data, and the public boundary row the verifier checks. -/
def witness : EnsembleWitness (sp1Ensemble (p := p)) :=
  EnsembleWitness.ofTables _ trace.tables trace.data trace.publicValues
    trace.tables_map_component trace.tables_data

@[simp] theorem witness_publicInput : trace.witness.publicInput = trace.publicValues := rfl
@[simp] theorem witness_data : trace.witness.data = trace.data := rfl
@[simp] theorem witness_tables : trace.witness.tables = trace.tables := rfl

/-- The assembled witness's verifier row is the built boundary table — the bridge that lets
`verifierTable_constraints` serve Clean's hand-written verifier row. -/
theorem witness_verifierTable :
    trace.witness.verifierTable =
      Table.build (verifierComponent (p := p)) [trace.publicValues] trace.data trace.hint :=
  Air.Flat.verifierTable_eq_build _ _

/-! ## Constraints -/

/--
**The assembled witness satisfies the ensemble's constraint system.**

Every one of the 54 tables — twenty-five instruction chips, 28 provider/boundary
tables, and the verifier row — has every `assertZero` of its whole flattened circuit evaluate to
zero on every generated row, and no static lookup left unchecked. Each conjunct is one citation of
the corresponding `traceTable_constraints`, so the arithmetic content (gadget carries, byte
decompositions, division evidence, the reader glue) is exactly the content those theorems carry.
-/
theorem witness_constraints (wf : trace.WellFormed) : trace.witness.Constraints := by
  have hall : trace.witness.allTables = trace.witness.verifierTable :: trace.tables := rfl
  rw [EnsembleWitness.Constraints, hall]
  intro table tableMem
  rcases List.mem_cons.mp tableMem with rfl | tableMem
  · rw [witness_verifierTable]
    exact verifierTable_constraints _ _ _ fun _ hpi => by
      rw [List.mem_singleton.mp hpi]
      exact wf.boundary
  · rw [tables] at tableMem
    rcases List.mem_append.mp tableMem with instructionMem | providerMem
    · exact trace.instructionTables_constraints wf table instructionMem
    · exact trace.providerTables_constraints wf table providerMem

end SupportedCoreTraceWitness

end SP1Clean.Soundness
