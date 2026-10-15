import SP1Clean.Proofs.Completeness.Providers
import SP1Clean.Soundness.EnsembleChannels
import SP1Clean.Soundness.EnsembleLookups
import SP1Clean.FormalModel.TraceGen.Bump
import SP1Clean.Proofs.Chips.SyscallInstrsChip.Witgen
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

/-! # Assembling a shard's physical AIR witness

The semantic trace selects events for 25 instruction tables and occurrences for 30 provider
and boundary tables. Their completeness theorems build the 55 physical tables in the ensemble's
registry order. Clean derives committed prover data from those tables; `generationData` and
`hint` are inputs to row generation, not an independently supplied commitment.

The inventory's constraints depend only on row cells and fixed lookups, so they hold at the
canonical committed data even when it differs from the generation input. Channel guarantees,
program bindings and agreement with a Sail execution remain separate obligations.

Instruction traces are unpadded; power-of-two shape belongs to the exact-Core adapter. Provider
multiplicities remain explicit, preserving repeated keys, zero-count entries and boolean memory
selectors. The trace record lives beside the completeness proofs because its provider occurrence
types depend on chip input types.
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

/-- Semantic occurrence type routed to one provider, boundary, or bump table. Reducible so a
`List id.Occurrence` is the concrete entry list at implicit transparency, where the closure
proofs' rewrites identify the two. -/
@[reducible] def Occurrence : ProviderTableId → Type
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
  -- The compiler emits no syscall rows yet either, but for a different reason than `halt`: the
  -- syscall table is genuinely *empty* rather than one padding row, because its Exit push is
  -- positively gated and needs no anti-gated companion to balance the verifier.
  | .syscallInstrs => Empty

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
  | .syscallInstrs, e => e.elim

end SP1Clean.ProviderTableId

namespace SP1Clean.Soundness

open Circuit
open Air.Flat (Component Table EnsembleWitness)
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance traceAssemblyFieldBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-! ## The generated trace -/

/-- Semantic events and provider occurrences routed by the ensemble's two registries.
`generationData` and `hint` feed the table builders. `boundary` is the public verifier input;
committed data is derived from the resulting physical tables by `SupportedCoreTraceWitness.data`.
Whether these events form a Sail execution is stated separately by the completeness relation. -/
structure SupportedCoreTraceWitness (p : ℕ) [Fact p.Prime] [Fact (2 ^ 25 < p)] where
  instructionEvents : (id : InstructionChipId) → List id.Event
  providerOccurrences : (id : ProviderTableId) → List id.Occurrence
  /-- Prover data supplied to the circuit witness builders. -/
  generationData : ProverData (ZMod p)
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

Instruction selectors are ordinary inputs. Their builders use `Table.build` and do not read
prover hints. Provider builders retain their explicit generation data and shared hint.
-/
def rangeTables : List (Table (ZMod p)) :=
  RangeChip.allWidths.map fun width =>
    Table.build (RangeChip.componentFor width)
      (RangeChip.traceInputs (trace.providerOccurrences (.range width))) trace.generationData trace.hint

/-- Build the instruction table selected by one stable instruction-chip identity.  This is the
completeness-side realization of `InstructionChipId`: the identity fixes both the semantic event
field read from the trace and whether witness generation uses a shared or per-row hint. -/
def instructionTableFor : InstructionChipId → Table (ZMod p)
  | .add => Table.build AddChip.component
      (AddChip.traceInputs (trace.instructionEvents .add) 0) trace.generationData trace.hint
  | .addi => Table.build AddiChip.component
      (AddiChip.traceInputs (trace.instructionEvents .addi) 0) trace.generationData trace.hint
  | .addw => Table.build AddwChip.component
      (AddwChip.traceInputs (trace.instructionEvents .addw) 0) trace.generationData trace.hint
  | .sub => Table.build SubChip.component
      (SubChip.traceInputs (trace.instructionEvents .sub) 0) trace.generationData trace.hint
  | .subw => Table.build SubwChip.component
      (SubwChip.traceInputs (trace.instructionEvents .subw) 0) trace.generationData trace.hint
  | .bitwise => Table.build BitwiseChip.component
      (BitwiseChip.traceInputs (trace.instructionEvents .bitwise) 0) trace.generationData
      (ProverHint.empty _)
  | .lt => Table.build LtChip.component
      (LtChip.traceInputs (trace.instructionEvents .lt) 0) trace.generationData
      (ProverHint.empty _)
  | .shiftLeft => Table.build ShiftLeftChip.component
      (ShiftLeftChip.traceInputs (trace.instructionEvents .shiftLeft) 0) trace.generationData
      (ProverHint.empty _)
  | .shiftRight => Table.build ShiftRightChip.component
      (ShiftRightChip.traceInputs (trace.instructionEvents .shiftRight) 0) trace.generationData
      (ProverHint.empty _)
  | .jal => Table.build JalChip.component
      (JalChip.traceInputs (trace.instructionEvents .jal) 0) trace.generationData trace.hint
  | .jalr => Table.build JalrChip.component
      (JalrChip.traceInputs (trace.instructionEvents .jalr) 0) trace.generationData trace.hint
  | .branch => Table.build BranchChip.component
      (BranchChip.traceInputs (trace.instructionEvents .branch) 0) trace.generationData
      (ProverHint.empty _)
  | .uType => Table.build UTypeChip.component
      (UTypeChip.traceInputs (trace.instructionEvents .uType) 0) trace.generationData trace.hint
  | .loadByte => Table.build LoadByteChip.component
      (LoadByteChip.traceInputs (trace.instructionEvents .loadByte)) trace.generationData trace.hint
  | .loadHalf => Table.build LoadHalfChip.component
      (LoadHalfChip.traceInputs (trace.instructionEvents .loadHalf)) trace.generationData trace.hint
  | .loadWord => Table.build LoadWordChip.component
      (LoadWordChip.traceInputs (trace.instructionEvents .loadWord)) trace.generationData trace.hint
  | .loadDouble => Table.build LoadDoubleChip.component
      (LoadDoubleChip.traceInputs (trace.instructionEvents .loadDouble)) trace.generationData trace.hint
  | .loadX0 => Table.build LoadX0Chip.component
      (LoadX0Chip.traceInputs (trace.instructionEvents .loadX0)) trace.generationData trace.hint
  | .storeByte => Table.build StoreByteChip.component
      (StoreByteChip.traceInputs (trace.instructionEvents .storeByte)) trace.generationData trace.hint
  | .storeHalf => Table.build StoreHalfChip.component
      (StoreHalfChip.traceInputs (trace.instructionEvents .storeHalf)) trace.generationData trace.hint
  | .storeWord => Table.build StoreWordChip.component
      (StoreWordChip.traceInputs (trace.instructionEvents .storeWord)) trace.generationData trace.hint
  | .storeDouble => Table.build StoreDoubleChip.component
      (StoreDoubleChip.traceInputs (trace.instructionEvents .storeDouble)) trace.generationData trace.hint
  | .mul => Table.build MulChip.component
      (MulChip.traceInputs (trace.instructionEvents .mul) 0) trace.generationData
      (ProverHint.empty _)
  | .divRem => Table.build DivRemChip.component
      (DivRemChip.traceInputs (trace.instructionEvents .divRem) 0) trace.generationData
      (ProverHint.empty _)
  | .aluX0 => Table.build AluX0Chip.component
      (AluX0Chip.traceInputs (trace.instructionEvents .aluX0) 0) trace.generationData trace.hint

/-- The twenty-five built instruction tables, in the one physical order fixed by the neutral
instruction registry. -/
def instructionTables : List (Table (ZMod p)) :=
  InstructionChipId.all.map trace.instructionTableFor

/-- Pointwise positional agreement between the completeness builder and the circuit-bearing
supported-machine registry. -/
@[simp] theorem instructionTableFor_component (id : InstructionChipId) :
    (trace.instructionTableFor id).component = (supportedChipFor (p := p) id).table := by
  cases id <;> rfl

/-- Pointwise instruction-table completeness.  This is the sole proof that dispatches on all
twenty-five instruction identities; list-level assembly below only reasons through `List.map`. -/
theorem instructionTableFor_constraints (wf : trace.WellFormed) (id : InstructionChipId) :
    (trace.instructionTableFor id).Constraints trace.generationData := by
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

/-- Constraint completeness lifted pointwise through the instruction registry. -/
theorem instructionTables_constraints (wf : trace.WellFormed) :
    ∀ table ∈ trace.instructionTables, table.Constraints trace.generationData := by
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
        trace.generationData trace.hint
  | .byte .msb => Table.build ByteChip.MSB.component
      (ByteChip.MSB.traceInputs (trace.providerOccurrences (.byte .msb))) trace.generationData trace.hint
  | .byte .andByte => Table.build ByteChip.AndByte.component
      (ByteChip.AndByte.traceInputs (trace.providerOccurrences (.byte .andByte)))
        trace.generationData trace.hint
  | .byte .orByte => Table.build ByteChip.OrByte.component
      (ByteChip.OrByte.traceInputs (trace.providerOccurrences (.byte .orByte)))
        trace.generationData trace.hint
  | .byte .xorByte => Table.build ByteChip.XorByte.component
      (ByteChip.XorByte.traceInputs (trace.providerOccurrences (.byte .xorByte)))
        trace.generationData trace.hint
  | .byte .ltu => Table.build ByteChip.Ltu.component
      (ByteChip.Ltu.traceInputs (trace.providerOccurrences (.byte .ltu))) trace.generationData trace.hint
  | .range width => Table.build (RangeChip.componentFor width)
      (RangeChip.traceInputs (trace.providerOccurrences (.range width))) trace.generationData trace.hint
  | .program => Table.build ProgramProviderChip.component
      (ProgramProviderChip.traceInputs (trace.providerOccurrences .program)) trace.generationData trace.hint
  | .memoryInit => Table.build MemoryProviderChip.component
      (MemoryProviderChip.traceInputs (trace.providerOccurrences .memoryInit))
        trace.generationData trace.hint
  | .memoryFinalize => Table.build MemoryFinalizeChip.component
      (MemoryFinalizeChip.traceInputs (trace.providerOccurrences .memoryFinalize))
        trace.generationData trace.hint
  | .memoryBump => Table.build MemoryBumpChip.component
      (memoryBumpTraceInputs (trace.providerOccurrences .memoryBump)) trace.generationData trace.hint
  | .stateBump => Table.build StateBumpChip.component
      (stateBumpTraceInputs (trace.providerOccurrences .stateBump)) trace.generationData trace.hint
  | .halt => Table.build HaltChip.component
      (HaltChip.haltTraceInputs (trace.providerOccurrences .halt)) trace.generationData trace.hint
  | .syscallInstrs => Table.build SyscallInstrsChip.component
      (SyscallInstrsChip.syscallInstrsTraceInputs (trace.providerOccurrences .syscallInstrs))
        trace.generationData trace.hint

/-- The thirty built provider and boundary tables, in the one physical order fixed by the
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
  | syscallInstrs => rfl

/-- Pointwise provider-table completeness. This is the sole proof that dispatches on all provider
identities; list-level assembly below only reasons through `List.map`. -/
theorem providerTableFor_constraints (wf : trace.WellFormed) (id : ProviderTableId) :
    (trace.providerTableFor id).Constraints trace.generationData := by
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
  | syscallInstrs =>
      exact SyscallInstrsChip.traceTable_constraints (trace.providerOccurrences .syscallInstrs) _ _

/-- The full 55-table assembly is the instruction registry followed by the provider segment. -/
def tables : List (Table (ZMod p)) :=
  trace.instructionTables ++ trace.providerTables

/-- Committed data is derived from complete physical table inputs, using Clean's canonical map. -/
def data : ProverData (ZMod p) := Air.Flat.deriveProverData trace.tables

/-- The provider segment projects to the ensemble's provider components in physical order. -/
theorem providerTables_map_component :
    trace.providerTables.map (·.component) = sp1ProviderTables := by
  simp only [providerTables, sp1ProviderTables, List.map_map]
  exact List.map_congr_left fun id _ => trace.providerTableFor_component id

/-- Every well-formed provider occurrence segment builds constraint-satisfying tables. -/
theorem providerTables_constraints (wf : trace.WellFormed) :
    ∀ table ∈ trace.providerTables, table.Constraints trace.generationData := by
  intro table tableMem
  rw [providerTables] at tableMem
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp tableMem
  exact trace.providerTableFor_constraints wf id

/-- **The assembled tables are the ensemble's tables**, component for component and in order. One
`rfl`: every completeness-side `component` is by definition the wrapper `sp1Tables` /
`sp1ProviderTables` build, and `Table.build` record the component they were
given. -/
theorem tables_map_component :
    (trace.tables.map (·.component)) = (sp1Ensemble (p := p)).tables := by
  rw [tables, List.map_append, instructionTables_map_component,
    providerTables_map_component, sp1Ensemble_tables]

/-! ## The assembled witness -/

/-- The physical tables in registry order and the public verifier input. -/
def witness : EnsembleWitness (sp1Ensemble (p := p)) :=
  EnsembleWitness.ofTables _ trace.tables trace.publicValues trace.tables_map_component

@[simp] theorem witness_publicInput : trace.witness.publicInput = trace.publicValues := rfl
@[simp] theorem witness_data : trace.witness.data = trace.data := rfl
@[simp] theorem witness_tables : trace.witness.tables = trace.tables := rfl

/-! ## Constraints -/

/-- **The compiler's syscall table has no rows**, in the positional shape the two non-core buses'
silence lemmas ask for. `syscallInstrsTraceInputs` is `[]` by construction (`List Empty` in, empty
list out), so this is a property of *this compiler's trace* rather than of the chip — the chip
genuinely speaks on seven buses. It is exactly what stops holding when the compiler learns to emit
syscall rows. -/
theorem witness_syscallTable_nil :
    ∀ t : Air.Flat.Table (ZMod p),
      trace.witness.tables[syscallTablePosition]? = some t → t.table = [] := by
  intro t ht
  have hpos : trace.witness.tables[syscallTablePosition]?
      = some (trace.providerTableFor .syscallInstrs) := rfl
  rw [hpos] at ht
  rw [← Option.some.inj ht]
  exact SyscallInstrsChip.traceTable_table _ _ _

/-- Every generated row satisfies the physical constraints at the data derived from all tables.
The public verifier's assertions are channel obligations, proved separately from this theorem. -/
theorem witness_constraints (wf : trace.WellFormed) : trace.witness.Constraints := by
  intro table member row rowMem
  apply sp1Table_constraints_setData table.component
    (EnsembleWitness.mem_component_of_mem (witness := trace.witness) member)
    (data := trace.generationData)
  change table ∈ trace.tables at member
  rw [tables] at member
  rcases List.mem_append.mp member with instructionMem | providerMem
  · exact trace.instructionTables_constraints wf table instructionMem row rowMem
  · exact trace.providerTables_constraints wf table providerMem row rowMem

end SupportedCoreTraceWitness

end SP1Clean.Soundness
