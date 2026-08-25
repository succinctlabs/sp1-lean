import SP1Clean.Proofs.Completeness.Providers
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

Exactly the data a trace generator emits: per instruction chip the list of execution events routed
to it and how many zero rows pad it to a power-of-two height, per provider table the list of
occurrences its consumers looked up, the two memory-boundary record lists, the two system-table row
lists, the shared committed prover data and hint, and the shard's public clock/pc endpoints. It is
a *flat data record*, not an execution: whether the events describe a real Sail chain is stated by
the relation in `Soundness/AIRCompleteness.lean`, not here.

## Two explicit construction choices

* **The memory-family trace API remains event-only.** Its shared address contract now admits the
  literal zero row when `is_real = 0`, but these nine builders do not yet take a padding-height
  parameter. Their tables are therefore still built at exactly the event count.
* **Provider multiplicity is part of each semantic entry.** Byte/Range/Program entries may be
  unit-count occurrences, aggregated equal keys, or zero-count padding; memory-boundary entries
  carry an explicit boolean selector. No local witness silently replaces the generator's choice.

## Where the layering lands

The trace record lives here rather than on the `FormalModel/` audit surface because the provider
occurrence types (`TraceGen.ByteEntry` and friends) do — for the reason
`Proofs/Completeness/Providers.lean` documents: the provider `Inputs` types are declared inside
`Proofs/Chips/`, so a `FormalModel`-resident trace model would invert the layering.
-/

namespace SP1Clean.Soundness

open Circuit
open Air.Flat (Component Table EnsembleWitness)
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance traceAssemblyFieldBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-! ## The generated trace -/

/--
**One shard's generated trace**, table by table, in `sp1Ensemble`'s own order.

The twenty-five instruction fields carry execution events (the typed records of
`FormalModel/TraceGen/Events.lean`); the provider fields carry occurrences — what some
chip's byte/range/program/memory pull asked the provider to justify. `data` is the one committed
`ProverData` every table shares (Clean's `EnsembleWitness.same_data`), `hint` the prover hint the
unhinted tables witness at, and the four naturals are the shard's public clock and pc endpoints.
-/
structure SupportedCoreTraceWitness (p : ℕ) [Fact p.Prime] [Fact (2 ^ 25 < p)] where
  -- Instruction chips, positions 0–24.
  addEvents : List RTypeEvent
  addPadding : ℕ
  addiEvents : List ITypeEvent
  addiPadding : ℕ
  addwEvents : List ALUTypeEvent
  addwPadding : ℕ
  subEvents : List RTypeEvent
  subPadding : ℕ
  subwEvents : List RTypeEvent
  subwPadding : ℕ
  bitwiseEvents : List ALUTypeEvent
  bitwisePadding : ℕ
  ltEvents : List ALUTypeEvent
  ltPadding : ℕ
  shiftLeftEvents : List ALUTypeEvent
  shiftLeftPadding : ℕ
  shiftRightEvents : List ALUTypeEvent
  shiftRightPadding : ℕ
  jalEvents : List JTypeEvent
  jalPadding : ℕ
  jalrEvents : List ITypeEvent
  jalrPadding : ℕ
  branchEvents : List ITypeEvent
  branchPadding : ℕ
  uTypeEvents : List JTypeEvent
  uTypePadding : ℕ
  /-- The nine memory-family table builders currently take no padding height, so a generated table
  is exactly as tall as its event list. Their shared address subcontracts now admit zero padding;
  a full memory-chip zero-row inhabitance theorem remains outside this assembly layer. Threading
  a height through this trace record is a separate builder/API step. -/
  loadByteEvents : List MemoryEvent
  loadHalfEvents : List MemoryEvent
  loadWordEvents : List MemoryEvent
  loadDoubleEvents : List MemoryEvent
  loadX0Events : List MemoryEvent
  storeByteEvents : List MemoryEvent
  storeHalfEvents : List MemoryEvent
  storeWordEvents : List MemoryEvent
  storeDoubleEvents : List MemoryEvent
  mulEvents : List RTypeEvent
  mulPadding : ℕ
  divRemEvents : List RTypeEvent
  divRemPadding : ℕ
  aluX0Events : List ALUTypeEvent
  aluX0Padding : ℕ
  -- Provider and boundary tables, positions 25–52.
  u8RangeEntries : List ByteEntry
  msbEntries : List ByteEntry
  andByteEntries : List ByteEntry
  orByteEntries : List ByteEntry
  xorByteEntries : List ByteEntry
  ltuEntries : List ByteEntry
  /-- Range-provider occurrences indexed by the complete preprocessed width profile `0, …, 16`. -/
  rangeEntries : RangeChip.Width → List RangeEntry
  romEntries : List RomEntry
  memoryInitEntries : List MemRecordEntry
  memoryFinalizeEntries : List MemRecordEntry
  memoryBumpRows : List (MemoryBumpChip.Inputs (ZMod p))
  stateBumpRows : List (StateBumpChip.Inputs (ZMod p))
  -- Shared prover state and the public boundary.
  data : ProverData (ZMod p)
  hint : ProverHint (ZMod p)
  initClk : ℕ
  initPc : ℕ
  finalClk : ℕ
  finalPc : ℕ

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/--
**A generated trace is well-formed** when every occurrence it emits satisfies the side condition
the table that consumes it needs — one field per table, each the exact premise of that table's
`traceTable_constraints` theorem.

Nothing here is a range fact about a *witnessed* cell: those are the circuits' own business, and
witness generation supplies them. What a generator owes is that the semantic content it routed to
a table belongs there — an `AND` event to the bitwise chip, an aligned address to the word-load
chip, a byte-sized operand pair to a byte provider.
-/
structure WellFormed : Prop where
  add : ∀ e ∈ trace.addEvents, e.WellFormed
  addi : ∀ e ∈ trace.addiEvents, e.WellFormed
  addw : ∀ e ∈ trace.addwEvents, e.WellFormed
  sub : ∀ e ∈ trace.subEvents, e.WellFormed
  subw : ∀ e ∈ trace.subwEvents, e.WellFormed
  bitwise : ∀ e ∈ trace.bitwiseEvents, e.WellFormed ∧ e.IsBitwise
  lt : ∀ e ∈ trace.ltEvents, e.WellFormed ∧ e.IsLt
  shiftLeft : ∀ e ∈ trace.shiftLeftEvents, e.WellFormed ∧ e.IsShiftLeft
  shiftRight : ∀ e ∈ trace.shiftRightEvents, e.WellFormed ∧ e.IsShiftRight
  jal : ∀ e ∈ trace.jalEvents, e.WellFormedJal ∧ e.JalTargets
  jalr : ∀ e ∈ trace.jalrEvents, e.WellFormed ∧ e.JalrTargets
  branch : ∀ e ∈ trace.branchEvents, e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets
  uType : ∀ e ∈ trace.uTypeEvents, e.WellFormedUType ∧ e.UTypeImm
  loadByte : ∀ e ∈ trace.loadByteEvents, e.WellFormed ∧ (e.opcode = 29 ∨ e.opcode = 32)
  loadHalf : ∀ e ∈ trace.loadHalfEvents, e.WellFormed ∧ e.Aligned 2
  loadWord : ∀ e ∈ trace.loadWordEvents, e.WellFormed ∧ e.Aligned 4
  loadDouble : ∀ e ∈ trace.loadDoubleEvents, e.WellFormed ∧ e.Aligned 8
  loadX0 : ∀ e ∈ trace.loadX0Events, e.WellFormedX0 ∧ e.IsLoad
  storeByte : ∀ e ∈ trace.storeByteEvents, e.WellFormedStore
  storeHalf : ∀ e ∈ trace.storeHalfEvents, e.WellFormedStore ∧ e.Aligned 2
  storeWord : ∀ e ∈ trace.storeWordEvents, e.WellFormedStore ∧ e.Aligned 4
  storeDouble : ∀ e ∈ trace.storeDoubleEvents, e.WellFormedStore ∧ e.Aligned 8
  mul : ∀ e ∈ trace.mulEvents, e.WellFormed ∧ e.IsMul
  divRem : ∀ e ∈ trace.divRemEvents, e.WellFormed ∧ e.IsDivRem
  aluX0 : ∀ e ∈ trace.aluX0Events, e.WellFormedX0
  u8Range : ∀ e ∈ trace.u8RangeEntries, e.WellFormed
  msb : ∀ e ∈ trace.msbEntries, e.WellFormed
  andByte : ∀ e ∈ trace.andByteEntries, e.WellFormed
  orByte : ∀ e ∈ trace.orByteEntries, e.WellFormed
  xorByte : ∀ e ∈ trace.xorByteEntries, e.WellFormed
  ltu : ∀ e ∈ trace.ltuEntries, e.WellFormed
  range : ∀ width e, e ∈ trace.rangeEntries width → e.WellFormed width.val
  rom : ∀ e ∈ trace.romEntries, e.WellFormed
  memoryInit : ∀ e ∈ trace.memoryInitEntries, e.WellFormedInit
  memoryBump : ∀ r ∈ trace.memoryBumpRows, MemoryBumpChip.Spec r
  stateBump : ∀ r ∈ trace.stateBumpRows, StateBumpChip.Spec r

/-! ## The 53 tables -/

/-- The shard's public boundary row: the four endpoints, limbed exactly as the verifier reads
them. -/
def publicValues : SP1PublicIO (ZMod p) :=
  boundaryInputs trace.initClk trace.initPc trace.finalClk trace.finalPc

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
      (RangeChip.traceInputs (trace.rangeEntries width)) trace.data trace.hint

def tables : List (Table (ZMod p)) :=
  [ Table.build AddChip.component (AddChip.traceInputs trace.addEvents trace.addPadding)
      trace.data trace.hint,
    Table.build AddiChip.component (AddiChip.traceInputs trace.addiEvents trace.addiPadding)
      trace.data trace.hint,
    Table.build AddwChip.component (AddwChip.traceInputs trace.addwEvents trace.addwPadding)
      trace.data trace.hint,
    Table.build SubChip.component (SubChip.traceInputs trace.subEvents trace.subPadding)
      trace.data trace.hint,
    Table.build SubwChip.component (SubwChip.traceInputs trace.subwEvents trace.subwPadding)
      trace.data trace.hint,
    Table.buildHinted BitwiseChip.component
      (BitwiseChip.traceInputs trace.bitwiseEvents trace.bitwisePadding) trace.data,
    Table.buildHinted LtChip.component (LtChip.traceInputs trace.ltEvents trace.ltPadding)
      trace.data,
    Table.buildHinted ShiftLeftChip.component
      (ShiftLeftChip.traceInputs trace.shiftLeftEvents trace.shiftLeftPadding) trace.data,
    Table.buildHinted ShiftRightChip.component
      (ShiftRightChip.traceInputs trace.shiftRightEvents trace.shiftRightPadding) trace.data,
    Table.build JalChip.component (JalChip.traceInputs trace.jalEvents trace.jalPadding)
      trace.data trace.hint,
    Table.build JalrChip.component (JalrChip.traceInputs trace.jalrEvents trace.jalrPadding)
      trace.data trace.hint,
    Table.buildHinted BranchChip.component
      (BranchChip.traceInputs trace.branchEvents trace.branchPadding) trace.data,
    Table.build UTypeChip.component (UTypeChip.traceInputs trace.uTypeEvents trace.uTypePadding)
      trace.data trace.hint,
    Table.build LoadByteChip.component (LoadByteChip.traceInputs trace.loadByteEvents)
      trace.data trace.hint,
    Table.build LoadHalfChip.component (LoadHalfChip.traceInputs trace.loadHalfEvents)
      trace.data trace.hint,
    Table.build LoadWordChip.component (LoadWordChip.traceInputs trace.loadWordEvents)
      trace.data trace.hint,
    Table.build LoadDoubleChip.component (LoadDoubleChip.traceInputs trace.loadDoubleEvents)
      trace.data trace.hint,
    Table.build LoadX0Chip.component (LoadX0Chip.traceInputs trace.loadX0Events)
      trace.data trace.hint,
    Table.build StoreByteChip.component (StoreByteChip.traceInputs trace.storeByteEvents)
      trace.data trace.hint,
    Table.build StoreHalfChip.component (StoreHalfChip.traceInputs trace.storeHalfEvents)
      trace.data trace.hint,
    Table.build StoreWordChip.component (StoreWordChip.traceInputs trace.storeWordEvents)
      trace.data trace.hint,
    Table.build StoreDoubleChip.component (StoreDoubleChip.traceInputs trace.storeDoubleEvents)
      trace.data trace.hint,
    Table.buildHinted MulChip.component (MulChip.traceInputs trace.mulEvents trace.mulPadding)
      trace.data,
    Table.buildHinted DivRemChip.component
      (DivRemChip.traceInputs trace.divRemEvents trace.divRemPadding) trace.data,
    Table.build AluX0Chip.component (AluX0Chip.traceInputs trace.aluX0Events trace.aluX0Padding)
      trace.data trace.hint,
    Table.build ByteChip.U8Range.component (ByteChip.U8Range.traceInputs trace.u8RangeEntries)
      trace.data trace.hint,
    Table.build ByteChip.MSB.component (ByteChip.MSB.traceInputs trace.msbEntries)
      trace.data trace.hint,
    Table.build ByteChip.AndByte.component (ByteChip.AndByte.traceInputs trace.andByteEntries)
      trace.data trace.hint,
    Table.build ByteChip.OrByte.component (ByteChip.OrByte.traceInputs trace.orByteEntries)
      trace.data trace.hint,
    Table.build ByteChip.XorByte.component (ByteChip.XorByte.traceInputs trace.xorByteEntries)
      trace.data trace.hint,
    Table.build ByteChip.Ltu.component (ByteChip.Ltu.traceInputs trace.ltuEntries)
      trace.data trace.hint
    ] ++ trace.rangeTables ++ [Table.build ProgramProviderChip.component
      (ProgramProviderChip.traceInputs trace.romEntries) trace.data trace.hint,
    Table.build MemoryProviderChip.component
      (MemoryProviderChip.traceInputs trace.memoryInitEntries) trace.data trace.hint,
    Table.build MemoryFinalizeChip.component
      (MemoryFinalizeChip.traceInputs trace.memoryFinalizeEntries) trace.data trace.hint,
    Table.build MemoryBumpChip.component trace.memoryBumpRows trace.data trace.hint,
    Table.build StateBumpChip.component trace.stateBumpRows trace.data trace.hint ]

/-- **The assembled tables are the ensemble's tables**, component for component and in order. One
`rfl`: every completeness-side `component` is by definition the wrapper `sp1Tables` /
`sp1ProviderTables` build, and `Table.build`/`Table.buildHinted` record the component they were
given. -/
theorem tables_map_component :
    (trace.tables.map (·.component)) = (sp1Ensemble (p := p)).tables := by
  have instructionComponents :
      (trace.tables.take instructionTableCount).map (·.component) = sp1Tables := rfl
  have providerComponents :
      (trace.tables.drop instructionTableCount).map (·.component) = sp1ProviderTables := rfl
  rw [sp1Ensemble_tables, ← instructionComponents, ← providerComponents,
    ← List.map_append, List.take_append_drop]

/-- Every assembled table carries the trace's shared committed prover data — Clean's
`EnsembleWitness.same_data`. -/
theorem tables_data : ∀ table ∈ trace.tables, table.data = trace.data := by
  intro table hmem
  rw [tables] at hmem
  rcases List.mem_append.mp hmem with prefixOrRangeMem | tailMem
  rcases List.mem_append.mp prefixOrRangeMem with prefixMem | rangeMem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at prefixMem
    rcases prefixMem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl
  · simp only [rangeTables] at rangeMem
    obtain ⟨width, _, tableEq⟩ := List.mem_map.mp rangeMem
    subst table
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at tailMem
    rcases tailMem with h | h | h | h | h <;> rw [h] <;> rfl

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
      rw [List.mem_singleton.mp hpi]; exact boundaryInputs_limbBounds _ _ _ _
  · rw [tables] at tableMem
    rcases List.mem_append.mp tableMem with prefixOrRangeMem | tailMem
    rcases List.mem_append.mp prefixOrRangeMem with prefixMem | rangeMem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at prefixMem
      rcases prefixMem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · subst table; exact AddChip.traceTable_constraints _ _ _ _ wf.add
      · subst table; exact AddiChip.traceTable_constraints _ _ _ _ wf.addi
      · subst table; exact AddwChip.traceTable_constraints _ _ _ _ wf.addw
      · subst table; exact SubChip.traceTable_constraints _ _ _ _ wf.sub
      · subst table; exact SubwChip.traceTable_constraints _ _ _ _ wf.subw
      · subst table; exact BitwiseChip.traceTable_constraints _ _ _ wf.bitwise
      · subst table; exact LtChip.traceTable_constraints _ _ _ wf.lt
      · subst table; exact ShiftLeftChip.traceTable_constraints _ _ _ wf.shiftLeft
      · subst table; exact ShiftRightChip.traceTable_constraints _ _ _ wf.shiftRight
      · subst table; exact JalChip.traceTable_constraints _ _ _ _ wf.jal
      · subst table; exact JalrChip.traceTable_constraints _ _ _ _ wf.jalr
      · subst table; exact BranchChip.traceTable_constraints _ _ _ wf.branch
      · subst table; exact UTypeChip.traceTable_constraints _ _ _ _ wf.uType
      · subst table; exact LoadByteChip.traceTable_constraints _ _ _ wf.loadByte
      · subst table; exact LoadHalfChip.traceTable_constraints _ _ _ wf.loadHalf
      · subst table; exact LoadWordChip.traceTable_constraints _ _ _ wf.loadWord
      · subst table; exact LoadDoubleChip.traceTable_constraints _ _ _ wf.loadDouble
      · subst table; exact LoadX0Chip.traceTable_constraints _ _ _ wf.loadX0
      · subst table; exact StoreByteChip.traceTable_constraints _ _ _ wf.storeByte
      · subst table; exact StoreHalfChip.traceTable_constraints _ _ _ wf.storeHalf
      · subst table; exact StoreWordChip.traceTable_constraints _ _ _ wf.storeWord
      · subst table; exact StoreDoubleChip.traceTable_constraints _ _ _ wf.storeDouble
      · subst table; exact MulChip.traceTable_constraints _ _ _ wf.mul
      · subst table; exact DivRemChip.traceTable_constraints _ _ _ wf.divRem
      · subst table; exact AluX0Chip.traceTable_constraints _ _ _ _ wf.aluX0
      · subst table; exact ByteChip.U8Range.traceTable_constraints _ _ _ wf.u8Range
      · subst table; exact ByteChip.MSB.traceTable_constraints _ _ _ wf.msb
      · subst table; exact ByteChip.AndByte.traceTable_constraints _ _ _ wf.andByte
      · subst table; exact ByteChip.OrByte.traceTable_constraints _ _ _ wf.orByte
      · subst table; exact ByteChip.XorByte.traceTable_constraints _ _ _ wf.xorByte
      · subst table; exact ByteChip.Ltu.traceTable_constraints _ _ _ wf.ltu
    · simp only [rangeTables] at rangeMem
      obtain ⟨width, _, tableEq⟩ := List.mem_map.mp rangeMem
      subst table
      exact RangeChip.traceTable_constraints _ (Nat.le_of_lt_succ width.isLt) _ _ _
        (wf.range width)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at tailMem
      rcases tailMem with h | h | h | h | h
      · subst table; exact ProgramProviderChip.traceTable_constraints _ _ _ wf.rom
      · subst table; exact MemoryProviderChip.traceTable_constraints _ _ _ wf.memoryInit
      · subst table; exact MemoryFinalizeChip.traceTable_constraints _ _ _
      · subst table; exact MemoryBumpChip.traceTable_constraints _ _ _ wf.memoryBump
      · subst table; exact StateBumpChip.traceTable_constraints _ _ _ wf.stateBump

end SupportedCoreTraceWitness

end SP1Clean.Soundness
