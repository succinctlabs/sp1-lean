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
`supported_core_generated_trace_complete` checks every resulting row before yielding the native AIR relation
consumed by soundness.  The explicit active-row counts prevent this regression from silently
collapsing back to the boundary-only case. `Audit/ActiveNativeCompleteness.lean` additionally ties
this exact event to an official Sail step and the deterministic execution compiler.
-/

namespace SP1Clean.Audit.ActiveTraceNonVacuity

open Air.Flat Circuit
open SP1Clean SP1Clean.TraceGen SP1Clean.TraceGenTests SP1Clean.Soundness
open SP1Clean.Execution
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel exitChannel)
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

/-- The one-event instruction registry: only the JAL table receives an occurrence. -/
def activeInstructionEvents : (id : InstructionChipId) → List id.Event
  | .jal => [activeEvent]
  | .add | .addi | .addw | .sub | .subw | .bitwise | .lt | .shiftLeft | .shiftRight |
      .jalr | .branch | .uType | .loadByte | .loadHalf | .loadWord | .loadDouble |
      .loadX0 | .storeByte | .storeHalf | .storeWord | .storeDouble | .mul | .divRem |
      .aluX0 => []

/-- The active shard's provider occurrences, indexed by the physical provider registry. -/
def activeProviderOccurrences : (id : ProviderTableId) → List id.Occurrence
  | .byte .u8Range => activeU8Entries
  | .byte .msb => []
  | .byte .andByte => []
  | .byte .orByte => []
  | .byte .xorByte => []
  | .byte .ltu => []
  | .range width => activeRangeEntries width
  | .program => [activeRomEntry]
  | .memoryInit => [activeMemoryInit]
  | .memoryFinalize => [activeMemoryFinalize]
  | .memoryBump => []
  | .stateBump => []
  -- `Occurrence .halt = Empty`: the Halt table still carries its mandatory single padding row,
  -- whose anti-gated `⟨0⟩` Exit push balances the boundary verifier's ungated `⟨exit_code⟩` pull.
  | .halt => []

/-! ## The hand-assembled trace source -/

/-- A hand-assembled semantic source for one active JAL row, no padding, the exact provider
occurrences above, and public endpoints matching the row's State pull/push (`clk 1 → 9`, self-loop
pc). `SupportedCoreTraceWitness.tables` turns these records into physical circuit-built rows. -/
def activeTrace : SupportedCoreTraceWitness SP1Prime where
  instructionEvents := activeInstructionEvents
  providerOccurrences := activeProviderOccurrences
  data := anchorData
  hint := anchorHint
  boundary := boundaryInputs 1 65536 9 65536

/-- The public statement proved by the active shard. -/
def activeStatement : SupportedCoreStatement SP1Prime :=
  ⟨anchorProgram, activeTrace.publicValues⟩

/-- The hand-assembled instruction-event count is exactly one. -/
theorem active_instruction_count :
    (activeTrace.instructionEvents .add).length +
      (activeTrace.instructionEvents .addi).length +
      (activeTrace.instructionEvents .addw).length +
      (activeTrace.instructionEvents .sub).length +
      (activeTrace.instructionEvents .subw).length +
      (activeTrace.instructionEvents .bitwise).length +
      (activeTrace.instructionEvents .lt).length +
      (activeTrace.instructionEvents .shiftLeft).length +
      (activeTrace.instructionEvents .shiftRight).length +
      (activeTrace.instructionEvents .jal).length +
      (activeTrace.instructionEvents .jalr).length +
      (activeTrace.instructionEvents .branch).length +
      (activeTrace.instructionEvents .uType).length +
      (activeTrace.instructionEvents .loadByte).length +
      (activeTrace.instructionEvents .loadHalf).length +
      (activeTrace.instructionEvents .loadWord).length +
      (activeTrace.instructionEvents .loadDouble).length +
      (activeTrace.instructionEvents .loadX0).length +
      (activeTrace.instructionEvents .storeByte).length +
      (activeTrace.instructionEvents .storeHalf).length +
      (activeTrace.instructionEvents .storeWord).length +
      (activeTrace.instructionEvents .storeDouble).length +
      (activeTrace.instructionEvents .mul).length +
      (activeTrace.instructionEvents .divRem).length +
      (activeTrace.instructionEvents .aluX0).length = 1 := by native_decide

/-- The sole source event is the one active JAL row. -/
theorem active_jal_row_count : (activeTrace.instructionEvents .jal).length = 1 := by native_decide

/-- The canonical heterogeneous decoder therefore sees exactly one physical instruction row. -/
theorem active_decoded_instruction_row_count :
    (decodedInstructionRows activeTrace.witness.tables).length = 1 := by rfl

private def activeJalDescriptor : SupportedChip SP1Prime :=
  supportedChipFor .jal

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
theorem active_jal_rows_nonempty : activeTrace.instructionEvents .jal ≠ [] := by native_decide

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
  instruction := by
    intro id e he
    cases id <;>
      simp_all [activeTrace, activeInstructionEvents, InstructionChipId.Valid,
        activeEvent_wellFormed, activeEvent_targets]
  provider := by
    intro id e he
    cases id with
    | byte provider =>
        cases provider with
        | u8Range =>
            simp only [activeTrace, activeProviderOccurrences] at he
            fin_cases he <;>
              norm_num [ProviderTableId.Valid, ByteEntry.WellFormed]
        | msb | andByte | orByte | xorByte | ltu =>
            simp [activeTrace, activeProviderOccurrences] at he
    | range width =>
        by_cases h13 : width = activeWidth13
        · subst width
          simp only [activeTrace, activeProviderOccurrences, activeRangeEntries] at he
          fin_cases he
          norm_num [ProviderTableId.Valid, RangeEntry.WellFormed, activeWidth13]
        · by_cases h14 : width = activeWidth14
          · subst width
            simp [activeTrace, activeProviderOccurrences, activeRangeEntries,
              activeWidth13, activeWidth14] at he
            fin_cases he
            norm_num [ProviderTableId.Valid, RangeEntry.WellFormed, activeWidth14]
          · by_cases h16 : width = activeWidth16
            · subst width
              simp [activeTrace, activeProviderOccurrences, activeRangeEntries,
                activeWidth13, activeWidth14, activeWidth16] at he
              fin_cases he <;>
                norm_num [ProviderTableId.Valid, RangeEntry.WellFormed, activeWidth16]
            · have hocc : activeTrace.providerOccurrences (.range width) = [] := by
                simp [activeTrace, activeProviderOccurrences, activeRangeEntries, h13, h14, h16]
                rfl
              rw [hocc] at he
              exact absurd he List.not_mem_nil
    | program =>
        simp only [activeTrace, activeProviderOccurrences, List.mem_singleton] at he
        subst e
        exact (by
          change activeRomEntry.WellFormed
          exact ⟨by norm_num [activeRomEntry], Or.inr rfl⟩)
    | memoryInit =>
        simp only [activeTrace, activeProviderOccurrences, List.mem_singleton] at he
        subst e
        change activeMemoryInit.WellFormedInit
        rfl
    | memoryFinalize =>
        change True
        trivial
    | memoryBump | stateBump => simp [activeTrace, activeProviderOccurrences] at he
    | halt => exact e.elim
  boundary := boundaryInputs_limbBounds _ _ _ _

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
   Table.build StateBumpChip.component [] anchorData anchorHint,
   TraceNonVacuity.haltBuilt]

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
      activeTrace.providerOccurrences (.range RangeChip.allWidths[i]) = [] := by
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
      RangeChip.allWidths[i]
        (activeTrace.providerOccurrences (.range RangeChip.allWidths[i]))
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
          (activeMemoryFinalizeBuilt.interactionsWith ch ++
            haltPaddingTable.interactionsWith ch)) := by
  simp only [activeTableGroup4, List.flatMap_cons, List.flatMap_nil,
    TraceNonVacuity.nilTable, TraceNonVacuity.haltBuilt_eq, List.append_nil, List.nil_append]

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
                      (activeMemoryFinalizeBuilt.interactionsWith ch ++
                        haltPaddingTable.interactionsWith ch)))))))) := by
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

/-- The verifier row's Exit view: the single ungated `⟨exit_code⟩` pull.  `boundaryInputs` commits
`exit_code = 0`, so this is a `-1` pull of `⟨0⟩`. -/
theorem activeTrace_verifierExit :
    activeTrace.witness.verifierTable.interactionsWith exitChannel.toRaw =
      [exitChannel.pulledIfValue 1
        (⟨activeTrace.publicValues.exit_code⟩ : Channels.ExitMsg (ZMod SP1Prime))] := by
  have h := congrArg (List.map TypedInteraction.raw)
    (witness_verifierExitInteractions_eq (p := SP1Prime) activeTrace.witness)
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

theorem activeJalBuilt_exitInteractions_nil :
    activeJalBuilt.interactionsWith exitChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  show exitChannel.toRaw ∉ (JalChip.circuit (p := SP1Prime)).channels
  simp [GeneralFormalCircuit.channels, JalChip.circuit, circuit_norm]

/-! ## Five-bus balance -/

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

/-- The verifier's ungated Exit pull of the committed `exit_code = 0`, followed by the Halt padding
row's two pushes (the reduced word at multiplicity `0`, the zero code at multiplicity `1`). -/
def activeExitLedger : List (Interaction (ZMod SP1Prime)) :=
  [exitChannel.pulledIfValue 1
      (⟨activeTrace.publicValues.exit_code⟩ : Channels.ExitMsg (ZMod SP1Prime))] ++
    haltExitInteractions

theorem activeTrace_stateInteractions :
    activeTrace.witness.interactionsWith stateChannel.toRaw =
      activeStateLedger ++ haltPaddingTable.interactionsWith stateChannel.toRaw := by
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
  simp only [activeStateLedger, List.nil_append, List.append_assoc]

theorem activeTrace_byteInteractions :
    activeTrace.witness.interactionsWith byteChannel.toRaw =
      activeByteLedger ++ haltPaddingTable.interactionsWith byteChannel.toRaw := by
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
  simp only [activeByteLedger, List.nil_append, List.append_assoc]

theorem activeTrace_programInteractions :
    activeTrace.witness.interactionsWith programChannel.toRaw =
      activeProgramLedger ++ haltPaddingTable.interactionsWith programChannel.toRaw := by
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
  simp only [activeProgramLedger, List.nil_append, List.append_assoc]

theorem activeTrace_memoryInteractions :
    activeTrace.witness.interactionsWith memoryChannel.toRaw =
      activeMemoryLedger ++ haltPaddingTable.interactionsWith memoryChannel.toRaw := by
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
  simp only [activeMemoryLedger, List.nil_append, List.append_assoc]

/-- The shard's Exit view: only the verifier's ungated pull and the Halt padding row's pushes; the
JAL row and every byte/program/memory provider are silent on the Exit bus. -/
theorem activeTrace_exitInteractions :
    activeTrace.witness.interactionsWith exitChannel.toRaw = activeExitLedger := by
  rw [activeTrace_interactionsWith_split, activeTrace_verifierExit,
    activeJalBuilt_exitInteractions_nil,
    interactionsWith_nil_of_single_channel activeU8Built byteChannel.toRaw activeU8Built_channels
      (of_eq_false Channels.exitChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange13Built byteChannel.toRaw
      activeRange13Built_channels (of_eq_false Channels.exitChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange14Built byteChannel.toRaw
      activeRange14Built_channels (of_eq_false Channels.exitChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeRange16Built byteChannel.toRaw
      activeRange16Built_channels (of_eq_false Channels.exitChannel_eq_byteChannel_false),
    interactionsWith_nil_of_single_channel activeProgramBuilt programChannel.toRaw
      activeProgramBuilt_channels (of_eq_false Channels.exitChannel_eq_programChannel_false),
    interactionsWith_nil_of_single_channel activeMemoryInitBuilt memoryChannel.toRaw
      activeMemoryInitBuilt_channels (of_eq_false Channels.exitChannel_eq_memoryChannel_false),
    interactionsWith_nil_of_single_channel activeMemoryFinalizeBuilt memoryChannel.toRaw
      activeMemoryFinalizeBuilt_channels
      (of_eq_false Channels.exitChannel_eq_memoryChannel_false),
    haltPaddingTable_exit]
  simp only [activeExitLedger, List.nil_append]

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

theorem activeExitLedger_length : activeExitLedger.length = 3 := by native_decide

theorem activeExitLedger_signed : SignedMults activeExitLedger := by
  exact (by native_decide : ∀ i ∈ activeExitLedger, i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1)

theorem activeExitLedger_perm :
    (pushedMessages activeExitLedger).Perm (pulledMessages activeExitLedger) := by native_decide

/-- The active shard's ledger conditions survive appending the Halt padding row's gated-off view of
a non-Exit channel: its entries are multiplicity zero, hence signed bits absent from both
`pushedMessages` and `pulledMessages`, and at most nineteen in number.  (The `anchorTrace` sibling
is `TraceNonVacuity.balancedOn_append_halt`.) -/
private theorem activeBalancedOn_append_halt {ch : RawChannel (ZMod SP1Prime)}
    {l : List (Interaction (ZMod SP1Prime))}
    (heq : activeTrace.witness.interactionsWith ch = l ++ haltPaddingTable.interactionsWith ch)
    (hname : ch.name ≠ "SP1Exit") (hlen : l.length < 100) (hbin : SignedMults l)
    (hperm : (pushedMessages l).Perm (pulledMessages l)) :
    activeTrace.BalancedOn ch := by
  have hzero := haltPaddingTable_mult_zero hname
  refine activeTrace.balancedOn_of_signed_perm ch ?_ ?_ ?_ <;> rw [heq]
  · have h19 := haltPaddingTable_interactionsWith_length ch
    have hp : (119 : ℕ) < SP1Prime := by norm_num [SP1Prime]
    rw [List.length_append]
    omega
  · intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact hbin i h
    · exact Or.inl (hzero i h)
  · rw [Ledger.pushedMessages_append, Ledger.pulledMessages_append,
      TraceNonVacuity.pushedMessages_nil_of_mult_zero hzero,
      TraceNonVacuity.pulledMessages_nil_of_mult_zero hzero, List.append_nil, List.append_nil]
    exact hperm

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

theorem activeTrace_balanced : activeTrace.Balanced := by
  intro channel hchannel
  rw [sp1Ensemble_channels] at hchannel
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hchannel
  rcases hchannel with rfl | rfl | rfl | rfl | rfl
  · exact activeBalancedOn_append_halt activeTrace_stateInteractions
      (by simp only [Channel.toRaw_name, Channels.stateChannel]; decide)
      (by rw [activeStateLedger_length]; norm_num)
      activeStateLedger_signed activeStateLedger_perm
  · exact activeBalancedOn_append_halt activeTrace_byteInteractions
      (by simp only [Channel.toRaw_name, Channels.byteChannel]; decide)
      (by rw [activeByteLedger_length]; norm_num)
      activeByteLedger_signed activeByteLedger_perm
  · exact activeBalancedOn_append_halt activeTrace_programInteractions
      (by simp only [Channel.toRaw_name, Channels.programChannel]; decide)
      (by rw [activeProgramLedger_length]; norm_num)
      activeProgramLedger_signed activeProgramLedger_perm
  · exact activeBalancedOn_append_halt activeTrace_memoryInteractions
      (by simp only [Channel.toRaw_name, Channels.memoryChannel]; decide)
      (by rw [activeMemoryLedger_length]; norm_num)
      activeMemoryLedger_signed activeMemoryLedger_perm
  · apply activeTrace.balancedOn_of_signed_perm exitChannel.toRaw
    · rw [activeTrace_exitInteractions, activeExitLedger_length]
      norm_num [SP1Prime]
    · rw [activeTrace_exitInteractions]
      exact activeExitLedger_signed
    · rw [activeTrace_exitInteractions]
      exact activeExitLedger_perm

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
  change Semantics.CommittedProgTruth typed.message anchorData
  have message_eq : typed.message = activeProgramMessage := by
    rw [TypedInteraction.message_eq_iff]
    rfl
  rw [message_eq]
  refine Semantics.ProgTruth.committed ⟨?_, ?_⟩
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
  activeTrace_boundaryFacts.binding

/-! ## Active relation and AIR witness -/

/-- The complete trace-source relation witness with one circuit-built active instruction row. -/
theorem activeTrace_generatedTrace :
    SupportedCoreGeneratedTraceRelation activeStatement activeTrace :=
  ⟨activeTrace_wellFormed, activeTrace.witness_balancedChannels activeTrace_balanced,
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

/-- The circuit-built active row passes through native AIR soundness to a normally-retiring
official-Sail run — the model-free plain-Sail conclusion, strictly stronger than the former
per-machine-model local-execution anchor. -/
theorem activeTrace_yields_sailExecution :
    ∃ w, SupportedCoreSailRelation activeStatement w := by
  exact supported_core_native_sound activeStatement activeTrace.witness
    activeTrace_nativeRelation

end SP1Clean.Audit.ActiveTraceNonVacuity
