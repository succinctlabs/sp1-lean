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
`Proofs/Chips/<Chip>/Complete.lean` files and the fifteen provider tables plus verifier row of
`Proofs/Completeness/Providers.lean`. Each of those says *one* table built from semantic
occurrences satisfies its constraints and channel guarantees. This file says the forty of them,
assembled in the ensemble's own order with one shared committed `ProverData`, form a Clean
`EnsembleWitness` for `sp1Ensemble` — and that its `Constraints` hold.

## What a `SupportedCoreTraceWitness` is

Exactly the data a trace generator emits: per instruction chip the list of execution events routed
to it and how many zero rows pad it to a power-of-two height, per provider table the list of
occurrences its consumers looked up, the two memory-boundary record lists, the two system-table row
lists, the shared committed prover data and hint, and the shard's public clock/pc endpoints. It is
a *flat data record*, not an execution: whether the events describe a real Sail chain is stated by
the relation in `Soundness/AIRCompleteness.lean`, not here.

## Two honest asymmetries, both inherited

* **The memory family takes no padding.** `LoadByteChip`…`StoreDoubleChip` have no satisfiable
  zero row (their address gadget forces a real address), so their tables are built at exactly the
  event count. Every other instruction chip carries an explicit padding height.
* **Provider tables are built at exactly the occurrence count.** Every provider generates its
  multiplicity with a *constant* witness IR, so a built row always pushes at multiplicity one;
  there is no bus-neutral padding row to append. See the limitations section of
  `docs/verification-report.md`.

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
`FormalModel/TraceGen/Events.lean`); the fifteen provider fields carry occurrences — what some
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
  /-- The nine memory-family tables take no padding height: their rows have no satisfiable zero
  row, so a generated table is exactly as tall as its event list. -/
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
  -- Provider and boundary tables, positions 25–39.
  u8RangeEntries : List ByteEntry
  msbEntries : List ByteEntry
  andByteEntries : List ByteEntry
  orByteEntries : List ByteEntry
  xorByteEntries : List ByteEntry
  ltuEntries : List ByteEntry
  range8Entries : List RangeEntry
  range13Entries : List RangeEntry
  range14Entries : List RangeEntry
  range16Entries : List RangeEntry
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
  addw : ∀ e ∈ trace.addwEvents, e.WellFormed ∧ e.immC = 0
  sub : ∀ e ∈ trace.subEvents, e.WellFormed
  subw : ∀ e ∈ trace.subwEvents, e.WellFormed
  bitwise : ∀ e ∈ trace.bitwiseEvents, e.WellFormed ∧ e.IsBitwise ∧ e.immC = 0
  lt : ∀ e ∈ trace.ltEvents, e.WellFormed ∧ e.IsLt ∧ e.immC = 0
  shiftLeft : ∀ e ∈ trace.shiftLeftEvents, e.WellFormed ∧ e.IsShiftLeft ∧ e.immC = 0
  shiftRight : ∀ e ∈ trace.shiftRightEvents, e.WellFormed ∧ e.IsShiftRight ∧ e.immC = 0
  jal : ∀ e ∈ trace.jalEvents, e.WellFormed ∧ e.JalTargets
  jalr : ∀ e ∈ trace.jalrEvents, e.WellFormed ∧ e.JalrTargets
  branch : ∀ e ∈ trace.branchEvents, e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets
  uType : ∀ e ∈ trace.uTypeEvents, e.WellFormed ∧ e.UTypeImm
  loadByte : ∀ e ∈ trace.loadByteEvents, e.WellFormed ∧ e.opcode = 29
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
  range8 : ∀ e ∈ trace.range8Entries, e.WellFormed 8
  range13 : ∀ e ∈ trace.range13Entries, e.WellFormed 13
  range14 : ∀ e ∈ trace.range14Entries, e.WellFormed 14
  range16 : ∀ e ∈ trace.range16Entries, e.WellFormed 16
  rom : ∀ e ∈ trace.romEntries, e.WellFormed
  memoryInit : ∀ e ∈ trace.memoryInitEntries, e.WellFormedInit
  memoryBump : ∀ r ∈ trace.memoryBumpRows, MemoryBumpChip.Spec r
  stateBump : ∀ r ∈ trace.stateBumpRows, StateBumpChip.Spec r

/-! ## The forty tables -/

/-- The shard's public boundary row: the four endpoints, limbed exactly as the verifier reads
them. -/
def publicValues : SP1PublicIO (ZMod p) :=
  boundaryInputs trace.initClk trace.initPc trace.finalClk trace.finalPc

/--
**The forty built tables**, in `sp1Ensemble.tables` order: the twenty-five instruction chips of
`sp1Tables`, then the fifteen entries of `sp1ProviderTables`.

Nine of them go through `Table.buildHinted` rather than `Table.build` — the chips whose witness
generation reads a per-row prover hint (the flag one-hots of Bitwise/Lt/the shifts/Mul/DivRem, the
comparison selector of Branch). Their builders pair each event with the hint that event's own row
is witnessed at; everything else shares the trace's single `hint`.
-/
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
      trace.data trace.hint,
    Table.build (RangeChip.component 8 (RangeChip.two_pow_lt (by norm_num)))
      (RangeChip.traceInputs trace.range8Entries) trace.data trace.hint,
    Table.build (RangeChip.component 13 (RangeChip.two_pow_lt (by norm_num)))
      (RangeChip.traceInputs trace.range13Entries) trace.data trace.hint,
    Table.build (RangeChip.component 14 (RangeChip.two_pow_lt (by norm_num)))
      (RangeChip.traceInputs trace.range14Entries) trace.data trace.hint,
    Table.build (RangeChip.component 16 (RangeChip.two_pow_lt (by norm_num)))
      (RangeChip.traceInputs trace.range16Entries) trace.data trace.hint,
    Table.build ProgramProviderChip.component
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
    (trace.tables.map (·.component)) = (sp1Ensemble (p := p)).tables := rfl

/-- Every assembled table carries the trace's shared committed prover data — Clean's
`EnsembleWitness.same_data`. -/
theorem tables_data : ∀ table ∈ trace.tables, table.data = trace.data := by
  intro table hmem
  simp only [tables, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl

/-! ## The assembled witness -/

/-- **The shard's AIR witness.** The forty built tables in ensemble order, the shared committed
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

Every one of the forty-one tables — twenty-five instruction chips, fifteen provider/boundary
tables, and the verifier row — has every `assertZero` of its whole flattened circuit evaluate to
zero on every generated row, and no static lookup left unchecked. Each conjunct is one citation of
the corresponding `traceTable_constraints`, so the arithmetic content (gadget carries, byte
decompositions, division evidence, the reader glue) is exactly the content those theorems carry.
-/
theorem witness_constraints (wf : trace.WellFormed) : trace.witness.Constraints := by
  have hall : trace.witness.allTables = trace.witness.verifierTable :: trace.tables := rfl
  rw [EnsembleWitness.Constraints, hall]
  simp only [tables, List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, nofun⟩
  · rw [witness_verifierTable]
    exact verifierTable_constraints _ _ _ fun _ hpi => by
      rw [List.mem_singleton.mp hpi]; exact boundaryInputs_limbBounds _ _ _ _
  · exact AddChip.traceTable_constraints _ _ _ _ wf.add
  · exact AddiChip.traceTable_constraints _ _ _ _ wf.addi
  · exact AddwChip.traceTable_constraints _ _ _ _ wf.addw
  · exact SubChip.traceTable_constraints _ _ _ _ wf.sub
  · exact SubwChip.traceTable_constraints _ _ _ _ wf.subw
  · exact BitwiseChip.traceTable_constraints _ _ _ wf.bitwise
  · exact LtChip.traceTable_constraints _ _ _ wf.lt
  · exact ShiftLeftChip.traceTable_constraints _ _ _ wf.shiftLeft
  · exact ShiftRightChip.traceTable_constraints _ _ _ wf.shiftRight
  · exact JalChip.traceTable_constraints _ _ _ _ wf.jal
  · exact JalrChip.traceTable_constraints _ _ _ _ wf.jalr
  · exact BranchChip.traceTable_constraints _ _ _ wf.branch
  · exact UTypeChip.traceTable_constraints _ _ _ _ wf.uType
  · exact LoadByteChip.traceTable_constraints _ _ _ wf.loadByte
  · exact LoadHalfChip.traceTable_constraints _ _ _ wf.loadHalf
  · exact LoadWordChip.traceTable_constraints _ _ _ wf.loadWord
  · exact LoadDoubleChip.traceTable_constraints _ _ _ wf.loadDouble
  · exact LoadX0Chip.traceTable_constraints _ _ _ wf.loadX0
  · exact StoreByteChip.traceTable_constraints _ _ _ wf.storeByte
  · exact StoreHalfChip.traceTable_constraints _ _ _ wf.storeHalf
  · exact StoreWordChip.traceTable_constraints _ _ _ wf.storeWord
  · exact StoreDoubleChip.traceTable_constraints _ _ _ wf.storeDouble
  · exact MulChip.traceTable_constraints _ _ _ wf.mul
  · exact DivRemChip.traceTable_constraints _ _ _ wf.divRem
  · exact AluX0Chip.traceTable_constraints _ _ _ _ wf.aluX0
  · exact ByteChip.U8Range.traceTable_constraints _ _ _ wf.u8Range
  · exact ByteChip.MSB.traceTable_constraints _ _ _ wf.msb
  · exact ByteChip.AndByte.traceTable_constraints _ _ _ wf.andByte
  · exact ByteChip.OrByte.traceTable_constraints _ _ _ wf.orByte
  · exact ByteChip.XorByte.traceTable_constraints _ _ _ wf.xorByte
  · exact ByteChip.Ltu.traceTable_constraints _ _ _ wf.ltu
  · exact RangeChip.traceTable_constraints _ (by norm_num) _ _ _ wf.range8
  · exact RangeChip.traceTable_constraints _ (by norm_num) _ _ _ wf.range13
  · exact RangeChip.traceTable_constraints _ (by norm_num) _ _ _ wf.range14
  · exact RangeChip.traceTable_constraints _ (by norm_num) _ _ _ wf.range16
  · exact ProgramProviderChip.traceTable_constraints _ _ _ wf.rom
  · exact MemoryProviderChip.traceTable_constraints _ _ _ wf.memoryInit
  · exact MemoryFinalizeChip.traceTable_constraints _ _ _
  · exact MemoryBumpChip.traceTable_constraints _ _ _ wf.memoryBump
  · exact StateBumpChip.traceTable_constraints _ _ _ wf.stateBump

end SupportedCoreTraceWitness

end SP1Clean.Soundness
