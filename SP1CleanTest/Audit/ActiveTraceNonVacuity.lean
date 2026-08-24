import SP1CleanTest.Audit.TraceNonVacuity

/-! # Active whole-ensemble trace non-vacuity

The boundary-only completeness anchor proves the relation's hypotheses can be satisfied, but it
does not exercise an instruction table.  This file closes that gap with the smallest real shard:
one circuit-built `JAL x0, 0` row at the committed self-loop, its matching Program provider row, the
initial/final x0 Memory frontier, and exactly the Byte-provider occurrences pulled by the verifier
and JAL row.

The semantic event and provider lists are deliberately hand-assembled in a
`SupportedCoreTraceWitness`; this file is not claiming a verified full trace generator.  Its physical
tables, however, are assembled through each circuit's own witness builder, and
`supported_core_native_complete` checks every resulting row before yielding the native AIR relation
consumed by soundness.  The explicit active-row counts prevent this regression from silently
collapsing back to the boundary-only case.
-/

namespace SP1Clean.Audit.ActiveTraceNonVacuity

open Air.Flat Circuit
open SP1Clean SP1Clean.TraceGen SP1Clean.TraceGenTests SP1Clean.Soundness
open SP1Clean.Execution
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel)
open SP1Clean.Ledger (SignedMults pushedMessages pulledMessages)
open SP1Clean.Audit.JointNonVacuity
open SP1Clean.Audit.TraceNonVacuity (anchorHint)

/-! ## One real decoded instruction -/

/-- The executor event for the committed self-loop.  Its sole register access is x0's prior record
at clock `0`; the JAL row touches it at micro-time `1 + 4 = 5` and writes the architectural zero
back. -/
def activeEvent : JTypeEvent where
  clk := 1
  pc := 65536
  opcode := 46
  opA := 0
  immB := 0
  immC := 0
  prevA := 0
  prevTsA := 0

theorem activeEvent_wellFormed : activeEvent.WellFormedJal := by
  simp only [activeEvent]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_,
    by norm_num⟩
  intro _
  rfl

theorem activeEvent_targets : activeEvent.JalTargets := by
  norm_num [activeEvent, JTypeEvent.JalTargets, JTypeEvent.jalTarget]

/-! ## Exact provider occurrences -/

/-- Four U8 occurrences: two public clock-pair checks and JAL's two clock checks. -/
def activeU8Entries : List ByteEntry :=
  [⟨0, 0, 1⟩, ⟨0, 0, 1⟩, ⟨0, 0, 1⟩, ⟨0, 0, 1⟩]

/-- JAL's `((clk_low - 1) / 8) < 2^13` occurrence. -/
def activeRange13Entries : List TraceGen.RangeEntry := [⟨0, 1⟩]

/-- JAL's aligned target-low-limb quotient. -/
def activeRange14Entries : List TraceGen.RangeEntry := [⟨0, 1⟩]

/-- Unit-count 16-bit occurrences, already aggregated only by list repetition so every interaction
still has signed-bit multiplicity: nine zeroes, four ones, then the final clock `9` and the
register timestamp difference `4`. -/
def activeRange16Entries : List TraceGen.RangeEntry :=
  [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩,
   ⟨0, 1⟩, ⟨0, 1⟩,
   ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩,
   ⟨9, 1⟩, ⟨4, 1⟩]

def activeWidth13 : RangeChip.Width := ⟨13, by norm_num⟩
def activeWidth14 : RangeChip.Width := ⟨14, by norm_num⟩
def activeWidth16 : RangeChip.Width := ⟨16, by norm_num⟩

/-- The three widths used by this JAL shard; every other member of the complete `0..16`
provider family receives an empty occurrence list. -/
def activeRangeEntries (width : RangeChip.Width) : List TraceGen.RangeEntry :=
  if width = activeWidth13 then activeRange13Entries
  else if width = activeWidth14 then activeRange14Entries
  else if width = activeWidth16 then activeRange16Entries
  else []

/-- The exact J-type Program message emitted by `JAL x0, 0`. -/
def activeRomEntry : RomEntry :=
  ⟨65536, 46, 0, 0, 0, 1, 1, 1, 1⟩

/-- Genesis and finalize records for the only touched Memory location, x0. -/
def activeMemoryInit : MemRecordEntry := ⟨0, 0, 0, true⟩
def activeMemoryFinalize : MemRecordEntry := ⟨0, 0, 5, true⟩

/-! ## The hand-assembled trace source -/

/-- A hand-assembled semantic source for one active JAL row, no padding, the exact provider
occurrences above, and public endpoints matching the row's State pull/push (`clk 1 → 9`, self-loop
pc). `SupportedCoreTraceWitness.tables` turns these records into physical circuit-built rows. -/
def activeTrace : SupportedCoreTraceWitness SP1Prime where
  addEvents := []; addPadding := 0
  addiEvents := []; addiPadding := 0
  addwEvents := []; addwPadding := 0
  subEvents := []; subPadding := 0
  subwEvents := []; subwPadding := 0
  bitwiseEvents := []; bitwisePadding := 0
  ltEvents := []; ltPadding := 0
  shiftLeftEvents := []; shiftLeftPadding := 0
  shiftRightEvents := []; shiftRightPadding := 0
  jalEvents := [activeEvent]; jalPadding := 0
  jalrEvents := []; jalrPadding := 0
  branchEvents := []; branchPadding := 0
  uTypeEvents := []; uTypePadding := 0
  loadByteEvents := []
  loadHalfEvents := []
  loadWordEvents := []
  loadDoubleEvents := []
  loadX0Events := []
  storeByteEvents := []
  storeHalfEvents := []
  storeWordEvents := []
  storeDoubleEvents := []
  mulEvents := []; mulPadding := 0
  divRemEvents := []; divRemPadding := 0
  aluX0Events := []; aluX0Padding := 0
  u8RangeEntries := activeU8Entries
  msbEntries := []
  andByteEntries := []
  orByteEntries := []
  xorByteEntries := []
  ltuEntries := []
  rangeEntries := activeRangeEntries
  romEntries := [activeRomEntry]
  memoryInitEntries := [activeMemoryInit]
  memoryFinalizeEntries := [activeMemoryFinalize]
  memoryBumpEvents := []
  stateBumpEvents := []
  data := anchorData
  hint := anchorHint
  initClk := 1
  initPc := 65536
  finalClk := 9
  finalPc := 65536

/-- The public statement proved by the active shard. -/
def activeStatement : SupportedCoreStatement SP1Prime :=
  ⟨anchorProgram, activeTrace.publicValues⟩

/-- The hand-assembled instruction-event count is exactly one. -/
theorem active_instruction_count :
    activeTrace.addEvents.length + activeTrace.addiEvents.length +
      activeTrace.addwEvents.length + activeTrace.subEvents.length +
      activeTrace.subwEvents.length + activeTrace.bitwiseEvents.length +
      activeTrace.ltEvents.length + activeTrace.shiftLeftEvents.length +
      activeTrace.shiftRightEvents.length + activeTrace.jalEvents.length +
      activeTrace.jalrEvents.length + activeTrace.branchEvents.length +
      activeTrace.uTypeEvents.length + activeTrace.loadByteEvents.length +
      activeTrace.loadHalfEvents.length + activeTrace.loadWordEvents.length +
      activeTrace.loadDoubleEvents.length + activeTrace.loadX0Events.length +
      activeTrace.storeByteEvents.length + activeTrace.storeHalfEvents.length +
      activeTrace.storeWordEvents.length + activeTrace.storeDoubleEvents.length +
      activeTrace.mulEvents.length + activeTrace.divRemEvents.length +
      activeTrace.aluX0Events.length = 1 := by native_decide

/-- The sole source event is the one active JAL row. -/
theorem active_jal_row_count : activeTrace.jalEvents.length = 1 := by native_decide

/-- The canonical heterogeneous decoder therefore sees exactly one physical instruction row. -/
theorem active_decoded_instruction_row_count :
    (decodedInstructionRows activeTrace.witness.tables).length = 1 := by rfl

private def activeJalDescriptor : SupportedChip SP1Prime :=
  ⟨JalChip.kind, JalChip.circuit, rfl, [.JAL], .any⟩

private def activeDecodedJalRow : DecodedInstructionRow SP1Prime where
  chip := activeJalDescriptor
  physical := JalChip.component.buildRow
    (activeEvent.toJalInputs (p := SP1Prime)) anchorData anchorHint

private theorem active_decoded_instruction_rows_eq :
    decodedInstructionRows activeTrace.witness.tables = [activeDecodedJalRow] := by rfl

private theorem activeDecodedJalRow_is_real :
    (activeDecodedJalRow.toChipRow activeTrace.data).is_real = 1 := by
  unfold ChipRow.is_real
  rw [DecodedInstructionRow.toChipRow_view]
  change (JalChip.component.rowInput
    (Environment.fromArray
      (JalChip.component.buildRow (activeEvent.toJalInputs (p := SP1Prime)) anchorData anchorHint)
      anchorData)).is_real = 1
  rw [Component.rowInput_buildRow]
  rfl

/-- The canonical decoder's sole physical instruction row is active, not padding. -/
theorem active_real_decoded_instruction_row_count :
    (realDecodedInstructionRows activeTrace.witness.data
      activeTrace.witness.tables).length = 1 := by
  unfold realDecodedInstructionRows
  rw [active_decoded_instruction_rows_eq]
  simp [activeDecodedJalRow_is_real]

/-- In particular, the active instruction table cannot regress to the empty trace. -/
theorem active_jal_rows_nonempty : activeTrace.jalEvents ≠ [] := by native_decide

private theorem activeU8Entries_wellFormed :
    ∀ e ∈ activeU8Entries, e.WellFormed := by
  intro e he
  simp only [activeU8Entries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> norm_num [ByteEntry.WellFormed]

private theorem activeRange13Entries_wellFormed :
    ∀ e ∈ activeRange13Entries, e.WellFormed 13 := by
  intro e he
  simp only [activeRange13Entries, List.mem_singleton] at he
  subst e
  norm_num [RangeEntry.WellFormed]

private theorem activeRange14Entries_wellFormed :
    ∀ e ∈ activeRange14Entries, e.WellFormed 14 := by
  intro e he
  simp only [activeRange14Entries, List.mem_singleton] at he
  subst e
  norm_num [RangeEntry.WellFormed]

private theorem activeRange16Entries_wellFormed :
    ∀ e ∈ activeRange16Entries, e.WellFormed 16 := by
  intro e he
  simp only [activeRange16Entries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> norm_num [RangeEntry.WellFormed]

/-- All instruction and provider occurrences are admitted by their semantic builders. -/
theorem activeTrace_wellFormed : activeTrace.WellFormed where
  add := by simp [activeTrace]
  addi := by simp [activeTrace]
  addw := by simp [activeTrace]
  sub := by simp [activeTrace]
  subw := by simp [activeTrace]
  bitwise := by simp [activeTrace]
  lt := by simp [activeTrace]
  shiftLeft := by simp [activeTrace]
  shiftRight := by simp [activeTrace]
  jal := by
    intro e he
    simp only [activeTrace] at he
    rw [List.mem_singleton] at he
    subst e
    exact ⟨activeEvent_wellFormed, activeEvent_targets⟩
  jalr := by simp [activeTrace]
  branch := by simp [activeTrace]
  uType := by simp [activeTrace]
  loadByte := by simp [activeTrace]
  loadHalf := by simp [activeTrace]
  loadWord := by simp [activeTrace]
  loadDouble := by simp [activeTrace]
  loadX0 := by simp [activeTrace]
  storeByte := by simp [activeTrace]
  storeHalf := by simp [activeTrace]
  storeWord := by simp [activeTrace]
  storeDouble := by simp [activeTrace]
  mul := by simp [activeTrace]
  divRem := by simp [activeTrace]
  aluX0 := by simp [activeTrace]
  u8Range := activeU8Entries_wellFormed
  msb := by simp [activeTrace]
  andByte := by simp [activeTrace]
  orByte := by simp [activeTrace]
  xorByte := by simp [activeTrace]
  ltu := by simp [activeTrace]
  range := by
    intro width e he
    by_cases h13 : width = activeWidth13
    · subst width
      simp only [activeTrace, activeRangeEntries] at he
      exact activeRange13Entries_wellFormed e he
    · by_cases h14 : width = activeWidth14
      · subst width
        simp [activeTrace, activeRangeEntries, activeWidth13, activeWidth14] at he
        exact activeRange14Entries_wellFormed e he
      · by_cases h16 : width = activeWidth16
        · subst width
          simp [activeTrace, activeRangeEntries, activeWidth13, activeWidth14,
            activeWidth16] at he
          exact activeRange16Entries_wellFormed e he
        · simp [activeTrace, activeRangeEntries, h13, h14, h16] at he
  rom := by
    intro e he
    simp only [activeTrace] at he
    rw [List.mem_singleton] at he
    subst e
    exact ⟨by norm_num [activeRomEntry], Or.inr rfl⟩
  memoryInit := by
    intro e he
    simp only [activeTrace] at he
    rw [List.mem_singleton] at he
    subst e
    rfl
  memoryBump := by simp [activeTrace]
  stateBump := by simp [activeTrace]

/-- All aggregate-capable provider entries use canonical positive field counts. -/
theorem activeTrace_providerMultiplicitiesFit :
    activeTrace.ProviderMultiplicitiesFit := by
  constructor
  case range =>
    intro width e he
    by_cases h13 : width = activeWidth13
    · subst width
      simp [activeTrace, activeRangeEntries, activeRange13Entries] at he
      subst e
      norm_num [TraceGen.RangeEntry.MultiplicityFits, SP1Prime]
    · by_cases h14 : width = activeWidth14
      · subst width
        simp [activeTrace, activeRangeEntries, activeRange14Entries, activeWidth13,
          activeWidth14] at he
        subst e
        norm_num [TraceGen.RangeEntry.MultiplicityFits, SP1Prime]
      · by_cases h16 : width = activeWidth16
        · subst width
          simp [activeTrace, activeRangeEntries, activeRange16Entries, activeWidth13,
            activeWidth14, activeWidth16] at he
          rcases he with rfl | rfl | rfl | rfl <;>
            norm_num [TraceGen.RangeEntry.MultiplicityFits, SP1Prime]
        · simp [activeTrace, activeRangeEntries, h13, h14, h16] at he
  all_goals
    simp [activeTrace, activeU8Entries, activeRomEntry, TraceGen.ByteEntry.MultiplicityFits,
      TraceGen.RomEntry.MultiplicityFits, SP1Prime]

/-! ## Circuit-built provider tables -/

def activeProgramBuilt : Table (ZMod SP1Prime) :=
  Table.build ProgramProviderChip.component (ProgramProviderChip.traceInputs [activeRomEntry])
    anchorData anchorHint

def activeMemoryInitBuilt : Table (ZMod SP1Prime) :=
  Table.build MemoryProviderChip.component (MemoryProviderChip.traceInputs [activeMemoryInit])
    anchorData anchorHint

def activeMemoryFinalizeBuilt : Table (ZMod SP1Prime) :=
  Table.build MemoryFinalizeChip.component
    (MemoryFinalizeChip.traceInputs [activeMemoryFinalize]) anchorData anchorHint

def activeJalBuilt : Table (ZMod SP1Prime) :=
  Table.build JalChip.component (JalChip.traceInputs [activeEvent] 0) anchorData anchorHint

def activeU8Built : Table (ZMod SP1Prime) :=
  Table.build ByteChip.U8Range.component (ByteChip.U8Range.traceInputs activeU8Entries)
    anchorData anchorHint

def activeRange13Built : Table (ZMod SP1Prime) :=
  Table.build (RangeChip.componentFor activeWidth13)
    (RangeChip.traceInputs activeRange13Entries) anchorData anchorHint

def activeRange14Built : Table (ZMod SP1Prime) :=
  Table.build (RangeChip.componentFor activeWidth14)
    (RangeChip.traceInputs activeRange14Entries) anchorData anchorHint

def activeRange16Built : Table (ZMod SP1Prime) :=
  Table.build (RangeChip.componentFor activeWidth16)
    (RangeChip.traceInputs activeRange16Entries) anchorData anchorHint

private def activeTableGroup0 : List (Table (ZMod SP1Prime)) :=
  [Table.build AddChip.component [] anchorData anchorHint,
   Table.build AddiChip.component [] anchorData anchorHint,
   Table.build AddwChip.component [] anchorData anchorHint,
   Table.build SubChip.component [] anchorData anchorHint,
   Table.build SubwChip.component [] anchorData anchorHint,
   Table.buildHinted BitwiseChip.component [] anchorData,
   Table.buildHinted LtChip.component [] anchorData,
   Table.buildHinted ShiftLeftChip.component [] anchorData,
   Table.buildHinted ShiftRightChip.component [] anchorData]

private def activeTableGroup1 : List (Table (ZMod SP1Prime)) :=
  [activeJalBuilt,
   Table.build JalrChip.component [] anchorData anchorHint,
   Table.buildHinted BranchChip.component [] anchorData,
   Table.build UTypeChip.component [] anchorData anchorHint,
   Table.build LoadByteChip.component [] anchorData anchorHint,
   Table.build LoadHalfChip.component [] anchorData anchorHint,
   Table.build LoadWordChip.component [] anchorData anchorHint,
   Table.build LoadDoubleChip.component [] anchorData anchorHint,
   Table.build LoadX0Chip.component [] anchorData anchorHint]

private def activeTableGroup2 : List (Table (ZMod SP1Prime)) :=
  [Table.build StoreByteChip.component [] anchorData anchorHint,
   Table.build StoreHalfChip.component [] anchorData anchorHint,
   Table.build StoreWordChip.component [] anchorData anchorHint,
   Table.build StoreDoubleChip.component [] anchorData anchorHint,
   Table.buildHinted MulChip.component [] anchorData,
   Table.buildHinted DivRemChip.component [] anchorData,
   Table.build AluX0Chip.component [] anchorData anchorHint]

private def activeTableGroup3 : List (Table (ZMod SP1Prime)) :=
  [activeU8Built,
   Table.build ByteChip.MSB.component [] anchorData anchorHint,
   Table.build ByteChip.AndByte.component [] anchorData anchorHint,
   Table.build ByteChip.OrByte.component [] anchorData anchorHint,
   Table.build ByteChip.XorByte.component [] anchorData anchorHint,
   Table.build ByteChip.Ltu.component [] anchorData anchorHint]

private def activeTableGroup4 : List (Table (ZMod SP1Prime)) :=
  [activeProgramBuilt, activeMemoryInitBuilt, activeMemoryFinalizeBuilt,
   Table.build MemoryBumpChip.component [] anchorData anchorHint,
   Table.build StateBumpChip.component [] anchorData anchorHint]

private def activeGroupedTables : List (Table (ZMod SP1Prime)) :=
  activeTableGroup0 ++
    (activeTableGroup1 ++
      (activeTableGroup2 ++ (activeTableGroup3 ++ (activeTrace.rangeTables ++ activeTableGroup4))))

private theorem activeTrace_tables_eq : activeTrace.tables = activeGroupedTables := rfl

private theorem activeTableGroup0_interactionsWith (ch : RawChannel (ZMod SP1Prime)) :
    activeTableGroup0.flatMap (·.interactionsWith ch) = [] := by
  simp only [activeTableGroup0, List.flatMap_cons, List.flatMap_nil,
    TraceNonVacuity.nilTable, TraceNonVacuity.nilTableHinted, List.nil_append]

private theorem activeTableGroup1_interactionsWith (ch : RawChannel (ZMod SP1Prime)) :
    activeTableGroup1.flatMap (·.interactionsWith ch) = activeJalBuilt.interactionsWith ch := by
  simp only [activeTableGroup1, List.flatMap_cons, List.flatMap_nil,
    TraceNonVacuity.nilTable, TraceNonVacuity.nilTableHinted, List.append_nil]

private theorem activeTableGroup2_interactionsWith (ch : RawChannel (ZMod SP1Prime)) :
    activeTableGroup2.flatMap (·.interactionsWith ch) = [] := by
  simp only [activeTableGroup2, List.flatMap_cons, List.flatMap_nil,
    TraceNonVacuity.nilTable, TraceNonVacuity.nilTableHinted, List.nil_append]

private theorem activeTableGroup3_interactionsWith (ch : RawChannel (ZMod SP1Prime)) :
    activeTableGroup3.flatMap (·.interactionsWith ch) = activeU8Built.interactionsWith ch := by
  simp only [activeTableGroup3, List.flatMap_cons, List.flatMap_nil,
    TraceNonVacuity.nilTable, List.append_nil]

private theorem flatMap_length17_eq_at13_at14_at16
    {A B : Type*} (l : List A) (f : A → List B) (length : l.length = 17)
    (other : ∀ i (bound : i < l.length), i ≠ 13 → i ≠ 14 → i ≠ 16 → f l[i] = []) :
    l.flatMap f = f l[13] ++ (f l[14] ++ f l[16]) := by
  change (l.drop 0).flatMap f = _
  repeat rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_nil_of_le (by omega)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [other]

private theorem rangeTable_interactionsWith_nil_of_entries_eq_nil
    (width : RangeChip.Width) (entries : List TraceGen.RangeEntry)
    (entriesNil : entries = []) (ch : RawChannel (ZMod SP1Prime)) :
    (Table.build (RangeChip.componentFor width) (RangeChip.traceInputs entries)
      anchorData anchorHint).interactionsWith ch = [] := by
  subst entries
  rfl

private theorem activeRangeTables_interactionsWith (ch : RawChannel (ZMod SP1Prime)) :
    activeTrace.rangeTables.flatMap (·.interactionsWith ch) =
      activeRange13Built.interactionsWith ch ++
        (activeRange14Built.interactionsWith ch ++ activeRange16Built.interactionsWith ch) := by
  have rangeTablesLength : activeTrace.rangeTables.length = 17 := by
    simp [SupportedCoreTraceWitness.rangeTables, RangeChip.allWidths]
  have entriesAtOtherIndex (i : ℕ) (bound : i < activeTrace.rangeTables.length)
      (not13 : i ≠ 13) (not14 : i ≠ 14) (not16 : i ≠ 16) :
      activeTrace.rangeEntries RangeChip.allWidths[i] = [] := by
    rw [rangeTablesLength] at bound
    interval_cases i <;> first
      | exact (not13 rfl).elim
      | exact (not14 rfl).elim
      | exact (not16 rfl).elim
      | rfl
  have interactionsAtOtherIndex (i : ℕ) (bound : i < activeTrace.rangeTables.length)
      (not13 : i ≠ 13) (not14 : i ≠ 14) (not16 : i ≠ 16) :
      activeTrace.rangeTables[i].interactionsWith ch = [] := by
    simp only [SupportedCoreTraceWitness.rangeTables, List.getElem_map]
    convert rangeTable_interactionsWith_nil_of_entries_eq_nil
      RangeChip.allWidths[i] (activeTrace.rangeEntries RangeChip.allWidths[i])
        (entriesAtOtherIndex i bound not13 not14 not16) ch using 1
    simp only [activeTrace]
    rfl
  calc
    _ = activeTrace.rangeTables[13].interactionsWith ch ++
          (activeTrace.rangeTables[14].interactionsWith ch ++
            activeTrace.rangeTables[16].interactionsWith ch) :=
      flatMap_length17_eq_at13_at14_at16 activeTrace.rangeTables
        (fun table : Table (ZMod SP1Prime) => table.interactionsWith ch)
          rangeTablesLength interactionsAtOtherIndex
    _ = _ := by rfl

private theorem activeTableGroup4_interactionsWith (ch : RawChannel (ZMod SP1Prime)) :
    activeTableGroup4.flatMap (·.interactionsWith ch) =
      activeProgramBuilt.interactionsWith ch ++
        (activeMemoryInitBuilt.interactionsWith ch ++
          (activeMemoryFinalizeBuilt.interactionsWith ch ++ [])) := by
  simp only [activeTableGroup4, List.flatMap_cons, List.flatMap_nil,
    TraceNonVacuity.nilTable, List.append_nil]

theorem activeTrace_interactionsWith_split (ch : RawChannel (ZMod SP1Prime)) :
    activeTrace.witness.interactionsWith ch =
      activeTrace.witness.verifierTable.interactionsWith ch ++
        (activeJalBuilt.interactionsWith ch ++
          (activeU8Built.interactionsWith ch ++
            (activeRange13Built.interactionsWith ch ++
              (activeRange14Built.interactionsWith ch ++
                (activeRange16Built.interactionsWith ch ++
                  (activeProgramBuilt.interactionsWith ch ++
                    (activeMemoryInitBuilt.interactionsWith ch ++
                      (activeMemoryFinalizeBuilt.interactionsWith ch ++ [])))))))) := by
  show (activeTrace.witness.verifierTable :: activeTrace.tables).flatMap
    (·.interactionsWith ch) = _
  rw [List.flatMap_cons]
  rw [activeTrace_tables_eq]
  unfold activeGroupedTables
  rw [List.flatMap_append, activeTableGroup0_interactionsWith, List.nil_append,
    List.flatMap_append, activeTableGroup1_interactionsWith,
    List.flatMap_append, activeTableGroup2_interactionsWith, List.nil_append,
    List.flatMap_append, activeTableGroup3_interactionsWith,
    List.flatMap_append, activeRangeTables_interactionsWith,
    activeTableGroup4_interactionsWith]
  simp only [List.append_assoc]

/-! ### Single-channel provider profiles -/

theorem activeProgramBuilt_channels :
    ∀ c ∈ activeProgramBuilt.component.circuit.channels, c = programChannel.toRaw := by
  show ∀ c ∈ (ProgramProviderChip.circuit (p := SP1Prime)).channels,
    c = programChannel.toRaw
  simp [GeneralFormalCircuit.channels, ProgramProviderChip.circuit, circuit_norm]

theorem activeMemoryInitBuilt_channels :
    ∀ c ∈ activeMemoryInitBuilt.component.circuit.channels, c = memoryChannel.toRaw := by
  show ∀ c ∈ (MemoryProviderChip.circuit (p := SP1Prime)).channels,
    c = memoryChannel.toRaw
  simp [GeneralFormalCircuit.channels, MemoryProviderChip.circuit, circuit_norm]

theorem activeMemoryFinalizeBuilt_channels :
    ∀ c ∈ activeMemoryFinalizeBuilt.component.circuit.channels, c = memoryChannel.toRaw := by
  show ∀ c ∈ (MemoryFinalizeChip.circuit (p := SP1Prime)).channels,
    c = memoryChannel.toRaw
  simp [GeneralFormalCircuit.channels, MemoryFinalizeChip.circuit, circuit_norm]

theorem activeU8Built_channels :
    ∀ c ∈ activeU8Built.component.circuit.channels, c = byteChannel.toRaw := by
  show ∀ c ∈ (ByteChip.U8Range.circuit (p := SP1Prime)).channels, c = byteChannel.toRaw
  simp [GeneralFormalCircuit.channels, ByteChip.U8Range.circuit, circuit_norm]

theorem activeRange13Built_channels :
    ∀ c ∈ activeRange13Built.component.circuit.channels, c = byteChannel.toRaw := by
  show ∀ c ∈ (RangeChip.circuitFor activeWidth13 (p := SP1Prime)).channels,
    c = byteChannel.toRaw
  simp [GeneralFormalCircuit.channels, RangeChip.circuitFor, RangeChip.circuit, circuit_norm]

theorem activeRange14Built_channels :
    ∀ c ∈ activeRange14Built.component.circuit.channels, c = byteChannel.toRaw := by
  show ∀ c ∈ (RangeChip.circuitFor activeWidth14 (p := SP1Prime)).channels,
    c = byteChannel.toRaw
  simp [GeneralFormalCircuit.channels, RangeChip.circuitFor, RangeChip.circuit, circuit_norm]

theorem activeRange16Built_channels :
    ∀ c ∈ activeRange16Built.component.circuit.channels, c = byteChannel.toRaw := by
  show ∀ c ∈ (RangeChip.circuitFor activeWidth16 (p := SP1Prime)).channels,
    c = byteChannel.toRaw
  simp [GeneralFormalCircuit.channels, RangeChip.circuitFor, RangeChip.circuit, circuit_norm]

private theorem interactionsWith_nil_of_single_channel
    (table : Table (ZMod SP1Prime)) (only : RawChannel (ZMod SP1Prime))
    (channels : ∀ c ∈ table.component.circuit.channels, c = only)
    {ch : RawChannel (ZMod SP1Prime)} (hne : ch ≠ only) : table.interactionsWith ch = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  intro hmem
  exact hne (channels _ hmem)

/-! ### The verifier and JAL row -/

theorem activeTrace_verifierState :
    activeTrace.witness.verifierTable.interactionsWith stateChannel.toRaw =
      [stateChannel.pulledIfValue 1
         ⟨activeTrace.publicValues.final_clk_high, activeTrace.publicValues.final_clk_low,
          activeTrace.publicValues.final_pc0, activeTrace.publicValues.final_pc1,
          activeTrace.publicValues.final_pc2⟩,
       stateChannel.pushedIfValue 1
         ⟨activeTrace.publicValues.init_clk_high, activeTrace.publicValues.init_clk_low,
          activeTrace.publicValues.init_pc0, activeTrace.publicValues.init_pc1,
          activeTrace.publicValues.init_pc2⟩] := by
  have h := congrArg (List.map TypedInteraction.raw)
    (witness_verifierStateInteractions_eq (p := SP1Prime) activeTrace.witness)
  rw [typedTableInteractionsWith_raw] at h
  simpa using h

theorem activeTrace_verifierProgram_nil :
    activeTrace.witness.verifierTable.interactionsWith programChannel.toRaw = [] := by
  have h := congrArg (List.map TypedInteraction.raw)
    (witness_verifierProgramInteractions_eq_nil (p := SP1Prime) activeTrace.witness)
  rw [typedTableInteractionsWith_raw] at h
  simpa using h

theorem activeTrace_verifierMemory_nil :
    activeTrace.witness.verifierTable.interactionsWith memoryChannel.toRaw = [] := by
  have h := congrArg (List.map TypedInteraction.raw)
    (witness_verifierMemoryInteractions_eq_nil (p := SP1Prime) activeTrace.witness)
  rw [typedTableInteractionsWith_raw] at h
  simpa using h

def activeVerifierByteInteractions : List (Interaction (ZMod SP1Prime)) :=
  (verifierBytePulls (varFromOffset SP1PublicIO 0)).map
    (AbstractInteraction.eval (Environment.fromInput activeTrace.publicValues anchorData))

theorem activeTrace_verifierByte :
    activeTrace.witness.verifierTable.interactionsWith byteChannel.toRaw =
      activeVerifierByteInteractions := by
  unfold Table.interactionsWith
  rw [EnsembleWitness.verifierTable_flatMap]
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval
      (Environment.fromInput activeTrace.publicValues anchorData))
    (((sp1StateVerifierMain (varFromOffset SP1PublicIO 0)).operations
      (size SP1PublicIO)).interactionsWith byteChannel.toRaw) = _
  rw [sp1StateVerifierMain_byteInteractions]
  rfl

def activeJalEnvironment : Environment (ZMod SP1Prime) :=
  Environment.fromArray
    (JalChip.component.buildRow (activeEvent.toJalInputs (p := SP1Prime)) anchorData anchorHint)
    anchorData

def activeJalStateInteractions : List (Interaction (ZMod SP1Prime)) :=
  ((JalChip.exposedStateInteractions (varFromOffset JalChip.Inputs 0) (size JalChip.Inputs)).map
    ChannelInteraction.toRaw).map (AbstractInteraction.eval activeJalEnvironment)

def activeJalByteInteractions : List (Interaction (ZMod SP1Prime)) :=
  ((JalChip.exposedByteInteractions (varFromOffset JalChip.Inputs 0) (size JalChip.Inputs)).map
    ChannelInteraction.toRaw).map (AbstractInteraction.eval activeJalEnvironment)

def activeJalProgramInteractions : List (Interaction (ZMod SP1Prime)) :=
  ((JalChip.exposedProgramInteractions (varFromOffset JalChip.Inputs 0)).map
    ChannelInteraction.toRaw).map (AbstractInteraction.eval activeJalEnvironment)

def activeJalMemoryInteractions : List (Interaction (ZMod SP1Prime)) :=
  ((JalChip.exposedMemoryInteractions (varFromOffset JalChip.Inputs 0) (size JalChip.Inputs)).map
    ChannelInteraction.toRaw).map (AbstractInteraction.eval activeJalEnvironment)

private theorem activeJalBuilt_interactionsWith
    (channel : RawChannel (ZMod SP1Prime))
    (exposed : List (AbstractInteraction (ZMod SP1Prime)))
    (hexposed : ((JalChip.main (varFromOffset JalChip.Inputs 0)).operations
      (size JalChip.Inputs)).interactionsWith channel = exposed) :
    activeJalBuilt.interactionsWith channel =
      exposed.map (AbstractInteraction.eval activeJalEnvironment) := by
  unfold activeJalBuilt
  rw [JalChip.traceTable_interactionsWith]
  change (JalChip.traceInputs [activeEvent] 0).flatMap
    (fun input : JalChip.Inputs (ZMod SP1Prime) =>
      (⟨JalChip.circuit⟩ : Component (ZMod SP1Prime)).operations.interactionValuesWith channel
        (Environment.fromArray
          ((⟨JalChip.circuit⟩ : Component (ZMod SP1Prime)).buildRow input anchorData anchorHint)
          anchorData)) = _
  simp only [JalChip.traceInputs, List.map_cons, List.map_nil, List.replicate_zero,
    List.append_nil, List.flatMap_cons, List.flatMap_nil]
  change (⟨JalChip.circuit⟩ : Component (ZMod SP1Prime)).operations.interactionValuesWith
    channel activeJalEnvironment = _
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval activeJalEnvironment)
    (((JalChip.main (varFromOffset JalChip.Inputs 0)).operations
      (size JalChip.Inputs)).interactionsWith channel) = _
  rw [hexposed]

theorem activeJalBuilt_stateInteractions :
    activeJalBuilt.interactionsWith stateChannel.toRaw = activeJalStateInteractions := by
  apply activeJalBuilt_interactionsWith
  exact JalChip.interactionsWith_state_eq _ _

theorem activeJalBuilt_byteInteractions :
    activeJalBuilt.interactionsWith byteChannel.toRaw = activeJalByteInteractions := by
  apply activeJalBuilt_interactionsWith
  exact JalChip.interactionsWith_byte_eq _ _

theorem activeJalBuilt_programInteractions :
    activeJalBuilt.interactionsWith programChannel.toRaw = activeJalProgramInteractions := by
  apply activeJalBuilt_interactionsWith
  exact JalChip.interactionsWith_program_eq _ _

theorem activeJalBuilt_memoryInteractions :
    activeJalBuilt.interactionsWith memoryChannel.toRaw = activeJalMemoryInteractions := by
  apply activeJalBuilt_interactionsWith
  exact JalChip.interactionsWith_memory_eq _ _

/-! ## Four-bus balance -/

def activeStateLedger : List (Interaction (ZMod SP1Prime)) :=
  [stateChannel.pulledIfValue 1
      ⟨activeTrace.publicValues.final_clk_high, activeTrace.publicValues.final_clk_low,
       activeTrace.publicValues.final_pc0, activeTrace.publicValues.final_pc1,
       activeTrace.publicValues.final_pc2⟩,
   stateChannel.pushedIfValue 1
      ⟨activeTrace.publicValues.init_clk_high, activeTrace.publicValues.init_clk_low,
       activeTrace.publicValues.init_pc0, activeTrace.publicValues.init_pc1,
       activeTrace.publicValues.init_pc2⟩] ++ activeJalStateInteractions

def activeByteLedger : List (Interaction (ZMod SP1Prime)) :=
  activeVerifierByteInteractions ++ activeJalByteInteractions ++
    activeU8Built.interactions ++ activeRange13Built.interactions ++
      activeRange14Built.interactions ++ activeRange16Built.interactions

def activeProgramLedger : List (Interaction (ZMod SP1Prime)) :=
  activeJalProgramInteractions ++ activeProgramBuilt.interactions

def activeMemoryLedger : List (Interaction (ZMod SP1Prime)) :=
  activeJalMemoryInteractions ++ activeMemoryInitBuilt.interactions ++
    activeMemoryFinalizeBuilt.interactions

theorem activeTrace_stateInteractions :
    activeTrace.witness.interactionsWith stateChannel.toRaw = activeStateLedger := by
  rw [activeTrace_interactionsWith_split, activeTrace_verifierState,
    activeJalBuilt_stateInteractions,
    interactionsWith_nil_of_single_channel activeU8Built byteChannel.toRaw activeU8Built_channels
      (of_eq_false Channels.stateChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange13Built byteChannel.toRaw
      activeRange13Built_channels (of_eq_false Channels.stateChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange14Built byteChannel.toRaw
      activeRange14Built_channels (of_eq_false Channels.stateChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange16Built byteChannel.toRaw
      activeRange16Built_channels (of_eq_false Channels.stateChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeProgramBuilt programChannel.toRaw
      activeProgramBuilt_channels (of_eq_false Channels.stateChannel_eq_programChannel_false),
    interactionsWith_nil_of_single_channel activeMemoryInitBuilt memoryChannel.toRaw
      activeMemoryInitBuilt_channels (of_eq_false Channels.stateChannel_eq_memoryChannel_false),
    interactionsWith_nil_of_single_channel activeMemoryFinalizeBuilt memoryChannel.toRaw
      activeMemoryFinalizeBuilt_channels (of_eq_false Channels.stateChannel_eq_memoryChannel_false)]
  simp only [activeStateLedger, List.append_nil]

theorem activeTrace_byteInteractions :
    activeTrace.witness.interactionsWith byteChannel.toRaw = activeByteLedger := by
  rw [activeTrace_interactionsWith_split, activeTrace_verifierByte,
    activeJalBuilt_byteInteractions,
    table_interactionsWith_eq_interactions activeU8Built_channels,
    table_interactionsWith_eq_interactions activeRange13Built_channels,
    table_interactionsWith_eq_interactions activeRange14Built_channels,
    table_interactionsWith_eq_interactions activeRange16Built_channels,
    interactionsWith_nil_of_single_channel activeProgramBuilt programChannel.toRaw
      activeProgramBuilt_channels (of_eq_false Channels.byteChannel_eq_programChannel_false),
    interactionsWith_nil_of_single_channel activeMemoryInitBuilt memoryChannel.toRaw
      activeMemoryInitBuilt_channels (of_eq_false Channels.byteChannel_eq_memoryChannel_false),
    interactionsWith_nil_of_single_channel activeMemoryFinalizeBuilt memoryChannel.toRaw
      activeMemoryFinalizeBuilt_channels (of_eq_false Channels.byteChannel_eq_memoryChannel_false)]
  simp only [activeByteLedger, List.append_nil, List.append_assoc]

theorem activeTrace_programInteractions :
    activeTrace.witness.interactionsWith programChannel.toRaw = activeProgramLedger := by
  rw [activeTrace_interactionsWith_split, activeTrace_verifierProgram_nil,
    activeJalBuilt_programInteractions,
    interactionsWith_nil_of_single_channel activeU8Built byteChannel.toRaw activeU8Built_channels
      (of_eq_false Channels.programChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange13Built byteChannel.toRaw
      activeRange13Built_channels (of_eq_false Channels.programChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange14Built byteChannel.toRaw
      activeRange14Built_channels (of_eq_false Channels.programChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange16Built byteChannel.toRaw
      activeRange16Built_channels (of_eq_false Channels.programChannel_eq_byteChannel_false),
    table_interactionsWith_eq_interactions activeProgramBuilt_channels,
    interactionsWith_nil_of_single_channel activeMemoryInitBuilt memoryChannel.toRaw
      activeMemoryInitBuilt_channels
      (Ne.symm (of_eq_false Channels.memoryChannel_eq_programChannel_false)),
    interactionsWith_nil_of_single_channel activeMemoryFinalizeBuilt memoryChannel.toRaw
      activeMemoryFinalizeBuilt_channels
      (Ne.symm (of_eq_false Channels.memoryChannel_eq_programChannel_false))]
  simp only [activeProgramLedger, List.append_nil, List.nil_append]

theorem activeTrace_memoryInteractions :
    activeTrace.witness.interactionsWith memoryChannel.toRaw = activeMemoryLedger := by
  rw [activeTrace_interactionsWith_split, activeTrace_verifierMemory_nil,
    activeJalBuilt_memoryInteractions,
    interactionsWith_nil_of_single_channel activeU8Built byteChannel.toRaw activeU8Built_channels
      (of_eq_false Channels.memoryChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange13Built byteChannel.toRaw
      activeRange13Built_channels (of_eq_false Channels.memoryChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange14Built byteChannel.toRaw
      activeRange14Built_channels (of_eq_false Channels.memoryChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange16Built byteChannel.toRaw
      activeRange16Built_channels (of_eq_false Channels.memoryChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeProgramBuilt programChannel.toRaw
      activeProgramBuilt_channels (of_eq_false Channels.memoryChannel_eq_programChannel_false),
    table_interactionsWith_eq_interactions activeMemoryInitBuilt_channels,
    table_interactionsWith_eq_interactions activeMemoryFinalizeBuilt_channels]
  simp only [activeMemoryLedger, List.append_nil, List.nil_append, List.append_assoc]

theorem activeStateLedger_length : activeStateLedger.length = 4 := by native_decide
theorem activeByteLedger_length : activeByteLedger.length = 46 := by native_decide
theorem activeProgramLedger_length : activeProgramLedger.length = 2 := by native_decide
theorem activeMemoryLedger_length : activeMemoryLedger.length = 4 := by native_decide

theorem activeStateLedger_signed : SignedMults activeStateLedger := by
  exact (by native_decide : ∀ i ∈ activeStateLedger, i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1)

theorem activeByteLedger_signed : SignedMults activeByteLedger := by
  exact (by native_decide : ∀ i ∈ activeByteLedger, i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1)

theorem activeProgramLedger_signed : SignedMults activeProgramLedger := by
  exact (by native_decide : ∀ i ∈ activeProgramLedger, i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1)

theorem activeMemoryLedger_signed : SignedMults activeMemoryLedger := by
  exact (by native_decide : ∀ i ∈ activeMemoryLedger, i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1)

theorem activeStateLedger_perm :
    (pushedMessages activeStateLedger).Perm (pulledMessages activeStateLedger) := by native_decide

theorem activeByteLedger_perm :
    (pushedMessages activeByteLedger).Perm (pulledMessages activeByteLedger) := by native_decide

theorem activeProgramLedger_perm :
    (pushedMessages activeProgramLedger).Perm (pulledMessages activeProgramLedger) := by native_decide

theorem activeMemoryLedger_perm :
    (pushedMessages activeMemoryLedger).Perm (pulledMessages activeMemoryLedger) := by native_decide

/-! ### The provider closure, checked against a real shard

`Proofs/Completeness/ClosureRealization.lean` recounts Byte/Program demand from the consumer
skeleton alone and proves that supplying it balances both buses. This anchor is the independent
check: the demand that recount computes agrees, key for key, with what *this* shard's provider
tables — hand-written months earlier, and in the unit-multiplicity style rather than the closure's
aggregated one — actually supply.

That the two styles agree is the point. `SuppliesDemand` is stated on per-key sums precisely so it
does not care whether a provider emits nine rows of multiplicity one or one row of multiplicity
nine; this anchor is what confirms the recount lands on the same sums either way.
-/
theorem activeTrace_suppliesDemand : activeTrace.SuppliesDemand := by
  refine activeTrace.suppliesDemand_of_keys ?_
  native_decide

/-! ### The hand-off model, decided on a real shard

`Model/InteractionBus.lean` says the State and Memory buses balance because they carry *tokens*,
each created once and consumed once. On this shard that is visible in the data rather than argued:
the State bus carries two tokens — the machine's `(clk_low = 1)` state, pushed by the boundary
verifier and pulled by the JAL row, and its `(clk_low = 9)` successor, pushed by the row and pulled
by the verifier as the final state — and the Memory bus carries two records for `x0`, one at
timestamp `0` from memory-init and its refresh at timestamp `5`.

These anchors are the demonstration that the obligation is **computable**: `stateLedger` and
`memoryLedger` are `List.filter` on the computable `fullLedger`, `handoff` is a `flatMap`, and
`List.Perm` on `LookupAccess` is decidable — so the hand-off condition on a concrete shard is
*decided*, not proved. That is why the ledger obligation was stated over the filtered whole ledger
rather than over Clean's `noncomputable` per-channel projection.
-/

/-- The two `(clock, pc)` tokens this shard's State bus carries. -/
def activeStateTokens : List LookupAccessList.LookupKey :=
  [(InteractionKind.State, "SP1State", [0, 1, 0, 1, 0]),
   (InteractionKind.State, "SP1State", [0, 9, 0, 1, 0])]

/-- The two `x0` records this shard's Memory bus carries: genesis, and its refresh. -/
def activeMemoryTokens : List LookupAccessList.LookupKey :=
  [(InteractionKind.Memory, "SP1Memory", [0, 0, 0, 0, 0, 0, 0, 0, 0]),
   (InteractionKind.Memory, "SP1Memory", [0, 5, 0, 0, 0, 0, 0, 0, 0])]

theorem activeTrace_stateHandoff :
    (LookupAccessList.active activeTrace.stateLedger).Perm
      (LookupAccessList.handoff activeStateTokens) := by
  native_decide

theorem activeTrace_memoryHandoff :
    (LookupAccessList.active activeTrace.memoryLedger).Perm
      (LookupAccessList.handoff activeMemoryTokens) := by
  native_decide

/-! ### Why the obligation is stated over `active` — a shard that shows it

`activeTrace` pads nothing (every `*Padding := 0`), so on it the `active` filter is the identity and
the two anchors above would hold with or without it. That makes them silent about the one thing
`active` is there for, so here is a shard that is not silent.

`activePaddedTrace` is `activeTrace` with a single JAL padding row. A padding row still *emits* its
State and Memory accesses — at multiplicity `0` (`stateLookups_padding`) — so the raw ledger gains
two entries that no token's life contains. The pair below is the demonstration: **the raw
permutation is false and the `active` one is true**, on the same shard, for the same tokens.

Without `active` the hand-off obligation would be unprovable for every trace that pads, which is
every real trace. -/

/-- The same shard with one padding row. -/
def activePaddedTrace : SupportedCoreTraceWitness SP1Prime :=
  { activeTrace with jalPadding := 1 }

/-- A padding row's accesses really are in the raw ledger, and really are not a token's life. -/
theorem activePaddedTrace_stateHandoff_raw_false :
    ¬ activePaddedTrace.stateLedger.Perm (LookupAccessList.handoff activeStateTokens) := by
  native_decide

/-- Dropping the zero-multiplicity entries recovers exactly the same two tokens. -/
theorem activePaddedTrace_stateHandoff :
    (LookupAccessList.active activePaddedTrace.stateLedger).Perm
      (LookupAccessList.handoff activeStateTokens) := by
  native_decide

theorem activeTrace_balanced : activeTrace.Balanced := by
  intro channel hchannel
  rw [sp1Ensemble_channels] at hchannel
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hchannel
  rcases hchannel with rfl | rfl | rfl | rfl
  · apply activeTrace.balancedOn_of_signed_perm stateChannel.toRaw
    · rw [activeTrace_stateInteractions, activeStateLedger_length]
      norm_num [SP1Prime]
    · rw [activeTrace_stateInteractions]
      exact activeStateLedger_signed
    · rw [activeTrace_stateInteractions]
      exact activeStateLedger_perm
  · apply activeTrace.balancedOn_of_signed_perm byteChannel.toRaw
    · rw [activeTrace_byteInteractions, activeByteLedger_length]
      norm_num [SP1Prime]
    · rw [activeTrace_byteInteractions]
      exact activeByteLedger_signed
    · rw [activeTrace_byteInteractions]
      exact activeByteLedger_perm
  · apply activeTrace.balancedOn_of_signed_perm programChannel.toRaw
    · rw [activeTrace_programInteractions, activeProgramLedger_length]
      norm_num [SP1Prime]
    · rw [activeTrace_programInteractions]
      exact activeProgramLedger_signed
    · rw [activeTrace_programInteractions]
      exact activeProgramLedger_perm
  · apply activeTrace.balancedOn_of_signed_perm memoryChannel.toRaw
    · rw [activeTrace_memoryInteractions, activeMemoryLedger_length]
      norm_num [SP1Prime]
    · rw [activeTrace_memoryInteractions]
      exact activeMemoryLedger_signed
    · rw [activeTrace_memoryInteractions]
      exact activeMemoryLedger_perm

/-! ## Semantic provider binding -/

def activeProgramMessage : Channels.ProgramMsg (ZMod SP1Prime) where
  pc0 := 0
  pc1 := 1
  pc2 := 0
  opcode := 46
  op_a := 0
  op_b := #v[0, 0, 0, 0]
  op_c := #v[0, 0, 0, 0]
  op_a_0 := 1
  imm_b := 1
  imm_c := 1

def activeInitMessage : Channels.MemoryMsg (ZMod SP1Prime) :=
  ⟨0, 0, 0, 0, 0, #v[0, 0, 0, 0]⟩

def activeFinalizeMessage : Channels.MemoryMsg (ZMod SP1Prime) :=
  ⟨0, 5, 0, 0, 0, #v[0, 0, 0, 0]⟩

theorem activeTrace_programProviderTable :
    programProviderTable activeTrace.witness =
      Table.build ProgramProviderChip.component
        (ProgramProviderChip.traceInputs [activeRomEntry]) anchorData (ProverHint.empty _) := rfl

theorem activeTrace_memoryInitProviderTable :
    memoryInitProviderTable activeTrace.witness =
      Table.build MemoryProviderChip.component
        (MemoryProviderChip.traceInputs [activeMemoryInit]) anchorData (ProverHint.empty _) := rfl

theorem activeTrace_memoryFinalizeProviderTable :
    memoryFinalizeProviderTable activeTrace.witness =
      Table.build MemoryFinalizeChip.component
        (MemoryFinalizeChip.traceInputs [activeMemoryFinalize]) anchorData (ProverHint.empty _) := rfl

private theorem interactionList_eq_singleton_of_projections
    (interactions : List (Interaction (ZMod SP1Prime)))
    (target : Interaction (ZMod SP1Prime))
    (length_eq : interactions.length = 1)
    (channel_eq : ∀ interaction ∈ interactions, interaction.channel = target.channel)
    (mult_eq : interactions.map (·.mult) = [target.mult])
    (msg_eq : interactions.map (·.msg) = [target.msg])
    (assume_eq : interactions.map (·.assumeGuarantees) = [target.assumeGuarantees]) :
    interactions = [target] := by
  cases interactions with
  | nil => simp at length_eq
  | cons interaction rest =>
      cases rest with
      | nil =>
          have hchannel := channel_eq interaction (by simp)
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mult_eq msg_eq assume_eq
          apply congrArg (fun value => [value])
          cases interaction
          cases target
          simp_all
      | cons other rest => simp at length_eq

private def InteractionProfile (interactions : List (Interaction (ZMod SP1Prime)))
    (target : Interaction (ZMod SP1Prime)) : Prop :=
  interactions.length = 1 ∧
    interactions.map (·.mult) = [target.mult] ∧
      interactions.map (·.msg) = [target.msg] ∧
        interactions.map (·.assumeGuarantees) = [target.assumeGuarantees]

/-- The provider rows' decidable data projections are evaluated in the test-only compiler-trust
quarantine; raw channel identity remains a structural theorem because channels carry predicates. -/
private theorem activeProviderProfiles :
    InteractionProfile activeProgramBuilt.interactions
      (programChannel.pushedIfValue 1 activeProgramMessage) ∧
    InteractionProfile activeMemoryInitBuilt.interactions
      (memoryChannel.pushedIfValue 1 activeInitMessage) ∧
    InteractionProfile activeMemoryFinalizeBuilt.interactions
      (memoryChannel.pulledIfValue 1 activeFinalizeMessage) := by
  unfold InteractionProfile
  native_decide

theorem activeTrace_programProviderInteractions :
    (programProviderTable activeTrace.witness).interactionsWith programChannel.toRaw =
      [programChannel.pushedIfValue 1 activeProgramMessage] := by
  rw [activeTrace_programProviderTable]
  change activeProgramBuilt.interactionsWith programChannel.toRaw = _
  have profile := activeProviderProfiles.1
  unfold InteractionProfile at profile
  apply interactionList_eq_singleton_of_projections
  · rw [table_interactionsWith_eq_interactions activeProgramBuilt_channels]
    exact profile.1
  · intro interaction member
    exact activeProgramBuilt.channel_eq_of_mem_interactionsWith member
  · rw [table_interactionsWith_eq_interactions activeProgramBuilt_channels]
    exact profile.2.1
  · rw [table_interactionsWith_eq_interactions activeProgramBuilt_channels]
    exact profile.2.2.1
  · rw [table_interactionsWith_eq_interactions activeProgramBuilt_channels]
    exact profile.2.2.2

theorem activeTrace_memoryInitProviderInteractions :
    (memoryInitProviderTable activeTrace.witness).interactionsWith memoryChannel.toRaw =
      [memoryChannel.pushedIfValue 1 activeInitMessage] := by
  rw [activeTrace_memoryInitProviderTable]
  change activeMemoryInitBuilt.interactionsWith memoryChannel.toRaw = _
  have profile := activeProviderProfiles.2.1
  unfold InteractionProfile at profile
  apply interactionList_eq_singleton_of_projections
  · rw [table_interactionsWith_eq_interactions activeMemoryInitBuilt_channels]
    exact profile.1
  · intro interaction member
    exact activeMemoryInitBuilt.channel_eq_of_mem_interactionsWith member
  · rw [table_interactionsWith_eq_interactions activeMemoryInitBuilt_channels]
    exact profile.2.1
  · rw [table_interactionsWith_eq_interactions activeMemoryInitBuilt_channels]
    exact profile.2.2.1
  · rw [table_interactionsWith_eq_interactions activeMemoryInitBuilt_channels]
    exact profile.2.2.2

theorem activeTrace_memoryFinalizeProviderInteractions :
    (memoryFinalizeProviderTable activeTrace.witness).interactionsWith memoryChannel.toRaw =
      [memoryChannel.pulledIfValue 1 activeFinalizeMessage] := by
  rw [activeTrace_memoryFinalizeProviderTable]
  change activeMemoryFinalizeBuilt.interactionsWith memoryChannel.toRaw = _
  have profile := activeProviderProfiles.2.2
  unfold InteractionProfile at profile
  apply interactionList_eq_singleton_of_projections
  · rw [table_interactionsWith_eq_interactions activeMemoryFinalizeBuilt_channels]
    exact profile.1
  · intro interaction member
    exact activeMemoryFinalizeBuilt.channel_eq_of_mem_interactionsWith member
  · rw [table_interactionsWith_eq_interactions activeMemoryFinalizeBuilt_channels]
    exact profile.2.1
  · rw [table_interactionsWith_eq_interactions activeMemoryFinalizeBuilt_channels]
    exact profile.2.2.1
  · rw [table_interactionsWith_eq_interactions activeMemoryFinalizeBuilt_channels]
    exact profile.2.2.2

theorem activeProgramMessage_jalView :
    Semantics.rowOfMsg activeProgramMessage = (programAccess jalView).toRow := by
  rfl

theorem activeTrace_programProviderBound : ProgramProviderBound activeTrace.witness := by
  intro interaction member _
  have member' := member
  rw [activeTrace_programProviderInteractions, List.mem_singleton] at member'
  subst interaction
  let typed : TypedInteraction programChannel :=
    { raw := programChannel.pushedIfValue 1 activeProgramMessage
      channel_eq :=
        (programProviderTable activeTrace.witness).channel_eq_of_mem_interactionsWith member }
  change Semantics.ProgTruth typed.message anchorData
  have message_eq : typed.message = activeProgramMessage := by
    rw [TypedInteraction.message_eq_iff]
    rfl
  rw [message_eq]
  refine ⟨?_, ?_⟩
  · norm_num [Channels.ProgramMsg.RowSpec, activeProgramMessage]
    native_decide
  rw [activeProgramMessage_jalView]
  exact jalView_decodedInROM

theorem activeInitMessage_content :
    Semantics.locContent anchorState (Semantics.MemoryMsg.locOf activeInitMessage) =
      some (Word.toBitVec64 activeInitMessage.value) := by
  change anchorState.get_reg? 0 = some (0#64)
  simp [SailState.get_reg?]

theorem activeTrace_memoryInitProviderBound :
    MemoryInitProviderBound activeTrace.witness anchorState (Commit.initClkNat anchorData) := by
  intro interaction member _
  have member' := member
  rw [activeTrace_memoryInitProviderInteractions, List.mem_singleton] at member'
  subst interaction
  let typed : TypedInteraction memoryChannel :=
    { raw := memoryChannel.pushedIfValue 1 activeInitMessage
      channel_eq :=
        (memoryInitProviderTable activeTrace.witness).channel_eq_of_mem_interactionsWith member }
  change MemoryInitMessageBound anchorState (Commit.initClkNat anchorData) typed.message
  have message_eq : typed.message = activeInitMessage := by
    rw [TypedInteraction.message_eq_iff]
    rfl
  rw [message_eq]
  exact ⟨activeInitMessage_content, by native_decide⟩

private theorem pairwise_of_map_eq_singleton {A B : Type} {f : A → B} {l : List A} {b : B}
    {r : A → A → Prop} (h : l.map f = [b]) : l.Pairwise r := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons a l =>
      cases l with
      | nil => simp
      | cons a' l => simp at h

theorem activeTrace_memoryInitProviderUnique : MemoryInitProviderUnique activeTrace.witness := by
  apply pairwise_of_map_eq_singleton
  rw [typedTableInteractionsWith_raw, activeTrace_memoryInitProviderInteractions]

theorem activeTrace_memoryFinalizeProviderUnique :
    MemoryFinalizeProviderUnique activeTrace.witness := by
  apply pairwise_of_map_eq_singleton
  rw [typedTableInteractionsWith_raw, activeTrace_memoryFinalizeProviderInteractions]

theorem activeTrace_boundaryFacts :
    InitialBoundaryFacts activeStatement activeTrace.witness anchorState where
  programWellFormed := anchorProgram_wellFormed
  programCommitted := ⟨anchorData_canonicalEncoding, rfl⟩
  initialPc := anchorBoundaryFacts.initialPc
  initialClock := anchorBoundaryFacts.initialClock
  romLoaded := anchorState_romLoaded
  configured := anchorState_configured
  codeMemoryCompatible := anchor_codeMemoryCompatible
  programProvider := activeTrace_programProviderBound
  memoryProvider := activeTrace_memoryInitProviderBound
  memoryProviderUnique := activeTrace_memoryInitProviderUnique
  memoryFinalizeProviderUnique := activeTrace_memoryFinalizeProviderUnique

/-- The hand-assembled trace source's public endpoint cells are the statement's public cells. -/
theorem activeTrace_public_eq : activeTrace.publicValues = activeStatement.publicValues := rfl

/-- The active providers bind the trace to the committed program and concrete initial Sail state. -/
theorem activeTrace_semanticBoundaryBinding :
    SemanticBoundaryBinding activeStatement activeTrace.witness :=
  ⟨anchorState, activeTrace_boundaryFacts⟩

/-! ## Active relation and AIR witness -/

/-- The complete trace-source relation witness with one circuit-built active instruction row. -/
theorem activeTrace_traceGeneratable :
    SupportedCoreTraceGeneratableExecutionRelation activeStatement activeTrace :=
  ⟨activeTrace_wellFormed, activeTrace_providerMultiplicitiesFit, activeTrace_balanced,
    activeTrace_public_eq,
    activeTrace_semanticBoundaryBinding⟩

/-- The particular circuit-built witness stored in `activeTrace` satisfies the native relation.
This keeps the non-vacuity anchor attached to the row-count and ledger theorems above, rather than
recovering an opaque existential witness from the generic completeness theorem. -/
theorem activeTrace_nativeRelation :
    SupportedCoreNativeRelation activeStatement activeTrace.witness :=
  ⟨⟨activeTrace_public_eq, activeTrace.witness_constraints activeTrace_wellFormed,
      activeTrace.witness_balancedChannels activeTrace_balanced⟩,
    activeTrace_semanticBoundaryBinding⟩

/-- Completeness assembles the active trace into the native AIR relation. -/
theorem activeTrace_yields_airWitness :
    ∃ witness, SupportedCoreNativeRelation activeStatement witness :=
  ⟨activeTrace.witness, activeTrace_nativeRelation⟩

/-- The circuit-built active row passes through native AIR soundness to an official-Sail local
execution segment for every machine model using SP1's ordinary eight-tick schedule. -/
theorem activeTrace_yields_localExecution (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    ∃ execution, SupportedCoreLocalExecutionRelation model activeStatement execution := by
  exact supported_core_native_sound model ordinary activeStatement activeTrace.witness
    activeTrace_nativeRelation

end SP1Clean.Audit.ActiveTraceNonVacuity
