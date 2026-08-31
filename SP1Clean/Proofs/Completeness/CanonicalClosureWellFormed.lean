import SP1Clean.Proofs.Completeness.CanonicalClosure

/-!
# Canonical closure row validity

This module isolates the row-local validity argument for the canonical Byte, Range, and Program
providers.  It is deliberately independent of the registry-wide consumer-polarity argument, so a
deterministic trace assembler only pays for the `DemandServable` contract it actually consumes.
-/

namespace SP1Clean.Soundness

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-- Servability of a key selected by one of the six Byte providers supplies exactly the operand
bounds required by its canonical `ByteEntry`. -/
theorem byteEntryOfKey_wellFormed {key : LookupAccessList.LookupKey} {opcode multiplicity : ℕ}
    (opcodeBound : opcode ≤ 5) (selected : selByte opcode key = true)
    (servable : ByteServable key) :
    (byteEntryOfKey key multiplicity).WellFormed := by
  have opcodeEq : cell key 0 = opcode := cell_zero_of_selByte selected
  have hb : cell key 2 < 2 ^ 8 := by
    interval_cases opcode <;> simp only [ByteServable, opcodeEq] at servable <;> omega
  have hc : cell key 3 < 2 ^ 8 := by
    interval_cases opcode <;> simp only [ByteServable, opcodeEq] at servable
    all_goals try omega
    have lastCell := congrArg (fun cells : List ℕ => cells.getD 3 0) servable.1
    have lastCellZero : cell key 3 = 0 := by
      simpa only [cell, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] using lastCell
    omega
  exact ⟨hb, hc⟩

/-- Servability of a key selected by a fixed-width Range provider supplies the range bound required
by its canonical `RangeEntry`. -/
theorem rangeEntryOfKey_wellFormed (width : RangeChip.Width)
    {key : LookupAccessList.LookupKey} {multiplicity : ℕ}
    (selected : selRange width key = true)
    (servable : ByteServable key) :
    (rangeEntryOfKey key multiplicity).WellFormed width.val := by
  simp only [selRange, Bool.and_eq_true, decide_eq_true_eq] at selected
  have opcodeEq : cell key 0 = 6 := selected.2.1
  have widthEq : cell key 2 = width.val := selected.2.2
  simp only [ByteServable, opcodeEq] at servable
  simpa only [TraceGen.RangeEntry.WellFormed, rangeEntryOfKey, widthEq] using servable.2.2

/-- The strengthened Program servability contract includes the row validity required by the
canonical ROM occurrence, not just the limb round-trip facts. -/
theorem romEntryOfKey_wellFormed {key : LookupAccessList.LookupKey} {multiplicity : ℕ}
    (servable : ProgramServable key) : (romEntryOfKey key multiplicity).WellFormed := by
  simpa only [TraceGen.RomEntry.WellFormed, romEntryOfKey] using servable.1

/-- Replacing the preprocessed-provider window by the canonical closure preserves generated-trace
well-formedness.  For Byte/Range/Program, `DemandServable` proves the rebuilt rows valid; every
instruction, boundary, and bump occurrence is preserved from the base trace. -/
theorem canonicalClosure_wellFormed (wf : trace.WellFormed)
    (servable : trace.DemandServable) : trace.canonicalClosure.WellFormed where
  instruction id event eventMem := wf.instruction id event eventMem
  provider id entry entryMem := by
    rw [canonicalClosure_providerOccurrences] at entryMem
    cases id with
    | byte provider =>
        cases provider with
        | u8Range =>
            change entry ∈ trace.closureU8RangeEntries at entryMem
            obtain ⟨key, keyMem, rfl⟩ := List.mem_map.mp entryMem
            have selected := (List.mem_filter.mp keyMem).2
            exact byteEntryOfKey_wellFormed (by omega) selected
              (servable.byte key (List.mem_filter.mp keyMem).1
                (byteKey_kind (isByteKey_of_selByte selected))).2
        | msb =>
            change entry ∈ trace.closureMsbEntries at entryMem
            obtain ⟨key, keyMem, rfl⟩ := List.mem_map.mp entryMem
            have selected := (List.mem_filter.mp keyMem).2
            exact byteEntryOfKey_wellFormed (by omega) selected
              (servable.byte key (List.mem_filter.mp keyMem).1
                (byteKey_kind (isByteKey_of_selByte selected))).2
        | andByte =>
            change entry ∈ trace.closureAndByteEntries at entryMem
            obtain ⟨key, keyMem, rfl⟩ := List.mem_map.mp entryMem
            have selected := (List.mem_filter.mp keyMem).2
            exact byteEntryOfKey_wellFormed (by omega) selected
              (servable.byte key (List.mem_filter.mp keyMem).1
                (byteKey_kind (isByteKey_of_selByte selected))).2
        | orByte =>
            change entry ∈ trace.closureOrByteEntries at entryMem
            obtain ⟨key, keyMem, rfl⟩ := List.mem_map.mp entryMem
            have selected := (List.mem_filter.mp keyMem).2
            exact byteEntryOfKey_wellFormed (by omega) selected
              (servable.byte key (List.mem_filter.mp keyMem).1
                (byteKey_kind (isByteKey_of_selByte selected))).2
        | xorByte =>
            change entry ∈ trace.closureXorByteEntries at entryMem
            obtain ⟨key, keyMem, rfl⟩ := List.mem_map.mp entryMem
            have selected := (List.mem_filter.mp keyMem).2
            exact byteEntryOfKey_wellFormed (by omega) selected
              (servable.byte key (List.mem_filter.mp keyMem).1
                (byteKey_kind (isByteKey_of_selByte selected))).2
        | ltu =>
            change entry ∈ trace.closureLtuEntries at entryMem
            obtain ⟨key, keyMem, rfl⟩ := List.mem_map.mp entryMem
            have selected := (List.mem_filter.mp keyMem).2
            exact byteEntryOfKey_wellFormed (by omega) selected
              (servable.byte key (List.mem_filter.mp keyMem).1
                (byteKey_kind (isByteKey_of_selByte selected))).2
    | range width =>
        change entry ∈ trace.closureRangeEntries width at entryMem
        obtain ⟨key, keyMem, rfl⟩ := List.mem_map.mp entryMem
        have selected := (List.mem_filter.mp keyMem).2
        have byteKey : IsByteKey key = true := by
          have selectedParts := selected
          simp only [selRange, Bool.and_eq_true] at selectedParts
          exact selectedParts.1
        exact rangeEntryOfKey_wellFormed width selected
          (servable.byte key (List.mem_filter.mp keyMem).1 (byteKey_kind byteKey)).2
    | program =>
        change entry ∈ trace.closureRomEntries at entryMem
        obtain ⟨key, keyMem, rfl⟩ := List.mem_map.mp entryMem
        have selected := (List.mem_filter.mp keyMem).2
        exact romEntryOfKey_wellFormed
          (servable.program key (List.mem_filter.mp keyMem).1 (programKey_kind selected)).2
    | memoryInit => exact wf.provider .memoryInit entry entryMem
    | memoryFinalize => exact wf.provider .memoryFinalize entry entryMem
    | memoryBump => exact wf.provider .memoryBump entry entryMem
    | stateBump => exact wf.provider .stateBump entry entryMem
    | halt => exact wf.provider .halt entry entryMem
  boundary := wf.boundary

end SupportedCoreTraceWitness

end SP1Clean.Soundness
