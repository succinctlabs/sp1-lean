import SP1Clean.Proofs.Completeness.Providers
import SP1Clean.Proofs.Completeness.Ledger
import SP1Clean.Model.BalanceBridge
import SP1CleanTest.Audit.JointNonVacuity
import SP1CleanTest.TraceGenTests.Conformance

/-! # Provider multiplicity witness-generation regressions

These executable anchors close the provider **row/count encoding** seam at the concrete SP1 field.
They exercise `Air.Flat.Table.build` itself, rather than only the provider circuits or their input
builders:

* a zero-count Byte row is retained as a real padding row whose evaluated bus interaction has
  multiplicity zero;
* counts greater than one survive the complete Byte, Range, and Program builders; and
* Memory init and finalize builders reach both boolean selector branches, with the finalize pull
  negating the active selector on the evaluated bus.

The accompanying `Constraints` theorems show that these are honest generated rows, not merely
unconstrained input arrays. `native_decide` is confined to this test library and only computes the
finite evaluated interaction lists. This battery does not select the source-backed preprocessing
demand inventory used by exact transport; that remains an explicit integration input and contract.
-/

namespace SP1Clean.Audit.ProviderMultiplicity

open Air.Flat Circuit
open SP1Clean SP1Clean.TraceGenTests

/-- Provider tables in this regression do not consult committed lookup data. -/
def data : ProverData (ZMod SP1Prime) := fun _ _ => #[]

/-- None of the provider witnesses below consults a prover hint. -/
def hint : ProverHint (ZMod SP1Prime) := ProverHint.empty _

/-! ## Byte padding and aggregation -/

def bytePadding : TraceGen.ByteEntry := ⟨17, 34, 0⟩
def byteAggregate : TraceGen.ByteEntry := ⟨17, 34, 7⟩

def bytePaddingTable : Table (ZMod SP1Prime) :=
  Table.build ByteChip.U8Range.component (ByteChip.U8Range.traceInputs [bytePadding]) data hint

def byteAggregateTable : Table (ZMod SP1Prime) :=
  Table.build ByteChip.U8Range.component (ByteChip.U8Range.traceInputs [byteAggregate]) data hint

theorem bytePaddingTable_constraints : bytePaddingTable.Constraints := by
  apply ByteChip.U8Range.traceTable_constraints [bytePadding] data hint
  intro e he
  simp only [List.mem_singleton] at he
  subst e
  norm_num [bytePadding, TraceGen.ByteEntry.WellFormed]

theorem byteAggregateTable_constraints : byteAggregateTable.Constraints := by
  apply ByteChip.U8Range.traceTable_constraints [byteAggregate] data hint
  intro e he
  simp only [List.mem_singleton] at he
  subst e
  norm_num [byteAggregate, TraceGen.ByteEntry.WellFormed]

/-- `Table.build` retains a zero-multiplicity padding row and evaluates its sole bus interaction
to multiplicity zero, so it is bus-neutral without disappearing from the table. -/
theorem bytePaddingTable_busNeutral :
    bytePaddingTable.table.length = 1 ∧ bytePaddingTable.interactions.map (fun i => i.mult) = [0] := by
  native_decide

/-- An aggregate Byte count is not replaced by the historical hard-coded multiplicity one. -/
theorem byteAggregateTable_preservesMultiplicity :
    byteAggregateTable.interactions.map (fun i => i.mult) = [7] := by
  native_decide

/-! ### Aggregate count through the machine balance dialect -/

/-- The exact Byte row shared by the aggregate provider and its seven unit consumers. -/
def byteAggregateMessage : ByteRow (ZMod SP1Prime) := ⟨3, 0, 17, 34⟩

/-- One aggregate `+7` provider interaction and seven matching unit pulls.  The provider interaction
is the one produced by `Table.build`, so this tests the integration seam rather than a parallel
hand-written positive access. -/
def byteAggregateLedger : List (Interaction (ZMod SP1Prime)) :=
  byteAggregateTable.interactions ++
    List.replicate 7 (Channels.byteChannel.pulledIfValue 1 byteAggregateMessage)

/-- The aggregate provider row evaluates to the expected native Byte access, including its key and
centered multiplicity.  The access projection is decidable even though a raw channel carries a
predicate and therefore has no `DecidableEq`. -/
theorem byteAggregateTable_accesses :
    byteAggregateTable.interactions.map Interaction.toAccess =
      [(.Byte, "SP1Byte", [3, 0, 17, 34], 7)] := by
  native_decide

/-- Every interaction of the circuit-built aggregate table is on the Byte channel. -/
theorem byteAggregateTable_channels :
    ∀ channel ∈ byteAggregateTable.component.circuit.channels,
      channel = Channels.byteChannel.toRaw := by
  show SP1Clean.Ledger.OnlyChannel ByteChip.U8Range.component Channels.byteChannel.toRaw
  exact SP1Clean.Ledger.onlyChannel_U8Range

/-- The complete aggregate ledger in the native centered-integer access dialect. -/
theorem byteAggregateLedger_accesses :
    byteAggregateLedger.map Interaction.toAccess =
      [(.Byte, "SP1Byte", [3, 0, 17, 34], 7),
       (.Byte, "SP1Byte", [3, 0, 17, 34], -1),
       (.Byte, "SP1Byte", [3, 0, 17, 34], -1),
       (.Byte, "SP1Byte", [3, 0, 17, 34], -1),
       (.Byte, "SP1Byte", [3, 0, 17, 34], -1),
       (.Byte, "SP1Byte", [3, 0, 17, 34], -1),
       (.Byte, "SP1Byte", [3, 0, 17, 34], -1),
       (.Byte, "SP1Byte", [3, 0, 17, 34], -1)] := by
  native_decide

/-- Seven is inside the canonical nonnegative half of the concrete SP1 field, so the generic
capacity lemma recovers it as the integer multiplicity used below. -/
theorem byteAggregate_signedVal :
    signedVal (7 : ZMod SP1Prime) = 7 := by
  exact signedVal_natCast_of_twice_le 7 (by norm_num [SP1Prime])

/-- The aggregate row closes against seven unit consumers in the exact integer ledger.  This is the
regression that prevents machine completeness from silently reverting to a `0/±1`-only contract. -/
theorem byteAggregateLedger_integerBalanced :
    LookupAccessList.isConsistentBalanced
      (byteAggregateLedger.map Interaction.toAccess) := by
  rw [byteAggregateLedger_accesses]
  intro k
  by_cases hk : (InteractionKind.Byte, "SP1Byte", [3, 0, 17, 34]) = k
  · rw [← hk]
    norm_num [LookupAccessList.multiplicitySum, LookupAccessList.filterKey,
      LookupAccessList.keyOf, LookupAccessList.multOf]
  · simp [LookupAccessList.multiplicitySum, LookupAccessList.filterKey,
      LookupAccessList.keyOf, hk]

/-- The same aggregate ledger therefore satisfies Clean's field-valued channel balance.  This is
the exact integer-to-Clean bridge used by `SupportedCoreTraceWitness.BalancedOn`. -/
theorem byteAggregateLedger_balancedInteractions :
    BalancedInteractions byteAggregateLedger := by
  apply LookupAccessList.balancedInteractions_of_isConsistentBalanced
    (byteAggregateLedger.map Interaction.toAccess) byteAggregateLedger
      Channels.byteChannel.toRaw
  · intro interaction interactionMem
    simp only [byteAggregateLedger, List.mem_append] at interactionMem
    rcases interactionMem with interactionMem | interactionMem
    · apply byteAggregateTable.channel_eq_of_mem_interactionsWith
      rw [SP1Clean.Audit.JointNonVacuity.table_interactionsWith_eq_interactions
        byteAggregateTable_channels]
      exact interactionMem
    · rw [List.eq_of_mem_replicate interactionMem]
      rfl
  · exact List.Perm.refl _
  · rw [show byteAggregateLedger.length = 8 by native_decide]
    norm_num [SP1Prime]
  · exact byteAggregateLedger_integerBalanced

/-! ## Range and Program aggregation -/

def rangeAggregate : TraceGen.RangeEntry := ⟨123, 9⟩
def rangeWidth8 : RangeChip.Width := ⟨8, by norm_num⟩

def rangeAggregateTable : Table (ZMod SP1Prime) :=
  Table.build (RangeChip.componentFor rangeWidth8)
    (RangeChip.traceInputs [rangeAggregate]) data hint

theorem rangeAggregateTable_constraints : rangeAggregateTable.Constraints := by
  apply RangeChip.traceTable_constraints
    (RangeChip.two_pow_lt (Nat.le_of_lt_succ rangeWidth8.isLt))
    (Nat.le_of_lt_succ rangeWidth8.isLt) [rangeAggregate] data hint
  intro e he
  simp only [List.mem_singleton] at he
  subst e
  norm_num [rangeAggregate, rangeWidth8, TraceGen.RangeEntry.WellFormed]

/-- An aggregate Range count survives both bit-witness generation and table assembly. -/
theorem rangeAggregateTable_preservesMultiplicity :
    rangeAggregateTable.interactions.map (fun i => i.mult) = [9] := by
  native_decide

def programAggregate : TraceGen.RomEntry :=
  ⟨0x10000, 13, 1, 2, 3, 0, 0, 0, 11⟩

def programAggregateTable : Table (ZMod SP1Prime) :=
  Table.build ProgramProviderChip.component
    (ProgramProviderChip.traceInputs [programAggregate]) data hint

theorem programAggregateTable_constraints : programAggregateTable.Constraints := by
  apply ProgramProviderChip.traceTable_constraints [programAggregate] data hint
  intro e he
  simp only [List.mem_singleton] at he
  subst e
  norm_num [programAggregate, TraceGen.RomEntry.WellFormed]

/-- An aggregate Program fetch count survives the complete ROM-provider builder. -/
theorem programAggregateTable_preservesMultiplicity :
    programAggregateTable.interactions.map (fun i => i.mult) = [11] := by
  native_decide

/-! ## Memory's two boolean branches -/

def memoryInactive : TraceGen.MemRecordEntry := ⟨0x1234, 0x55, 0, false⟩
def memoryActive : TraceGen.MemRecordEntry := ⟨0x1234, 0x55, 0, true⟩

def memoryInitTable : Table (ZMod SP1Prime) :=
  Table.build MemoryProviderChip.component
    (MemoryProviderChip.traceInputs [memoryInactive, memoryActive]) data hint

def memoryFinalizeTable : Table (ZMod SP1Prime) :=
  Table.build MemoryFinalizeChip.component
    (MemoryFinalizeChip.traceInputs [memoryInactive, memoryActive]) data hint

theorem memoryInitTable_constraints : memoryInitTable.Constraints := by
  apply MemoryProviderChip.traceTable_constraints [memoryInactive, memoryActive] data hint
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;>
    rfl

theorem memoryFinalizeTable_constraints : memoryFinalizeTable.Constraints :=
  MemoryFinalizeChip.traceTable_constraints [memoryInactive, memoryActive] data hint

/-- Memory init reaches both allowed selectors, and its push interaction preserves `0`/`1`. -/
theorem memoryInitTable_booleanBranches :
    memoryInitTable.interactions.map (fun i => i.mult) = [0, 1] := by
  native_decide

/-- Memory finalize reaches both allowed selectors; its pull interaction evaluates them as
`-0 = 0` and `-1`, respectively. -/
theorem memoryFinalizeTable_booleanBranches :
    memoryFinalizeTable.interactions.map (fun i => i.mult) = [0, -1] := by
  native_decide

end SP1Clean.Audit.ProviderMultiplicity
