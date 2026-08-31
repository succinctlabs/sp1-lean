import SP1Clean.Model.CleanLedger
import SP1Clean.Proofs.Completeness.Assembly
import SP1Clean.Proofs.Completeness.ProviderTables

/-! # The provider closure: recounting Byte/Range/Program demand from the consumers

`SupportedCoreTraceWitness` takes its provider occurrence lists through the provider registry, and
`Soundness/AIRCompleteness.lean`'s `Balanced` is a *hypothesis*: the assembled witness satisfies
the ensemble's constraint system, but nothing derives that its channels cancel. Every use so far
discharges balance by compiled evaluation on a fully concrete shard — which is only available in the
test library, and is why `SP1CleanTest/Audit/ActiveTraceNonVacuity.lean` spends roughly five hundred
lines on ledger plumbing for a single `JAL x0, 0` row and does not generalise to a symbolic trace.

This module is the first half of closing that gap. It does not invent an algorithm: the exact→native
transport already recounts provider multiplicities from a deliberately provider-free consumer ledger
and proves the result balances (`Faithful/Transport/PreprocessedProviders.lean`). What it recounts
over is `CoreAIR.Current.Row`, the extracted exact AIR. The same recount applies verbatim to a
`Table.build`-over-events trace, and that is what is defined here.

## Why no per-chip interaction list is needed

The obvious shape for "what do the consumers demand" is a symbolic per-chip list, and the tree has a
partial one (`exposedByteInteractions` and friends). It is not what this needs, and it would be the
expensive way to get it — for eight of the twenty-five chips those byte pulls descend from the
`CPUState` reader and the arithmetic operation subcircuits, so exposing them means extending each
chip's `exposedChannels_eq` lawfulness proof through those subcircuits.

`Faithful/Transport/Table.lean`'s `tableCleanAccesses_build` needs none of it. It folds
`component.operations.interactions` — every channel at once, and the *computable* `.interactions`
rather than the `noncomputable` per-channel `.interactionsWith` projection — into a
`LookupAccessList` whose entries already carry their `(kind, table, entry)` key. Demand is then a
question about that list, not about any chip.

## The acyclicity condition, and why the skeleton is defined by position

A recount is only well-founded if the providers being recounted are absent from the ledger they
recount against; otherwise a provider's multiplicity depends on itself. The twenty-four preprocessed
providers (six Byte opcode tables, all seventeen fixed Range widths, and Program) occupy positions
`25 .. 48` of `sp1Ensemble.tables`, so the skeleton is everything outside that window: the verifier
row, the twenty-five instruction tables, MemoryInit/MemoryFinalize, and both bumps. That mirrors
`Transport/CoreEnsemble.lean`'s `exactNativeSkeletonLedger` exactly.

Taking the window positionally rather than re-listing the tables is deliberate — the skeleton and
the assembled `tables` then cannot drift apart under a future reordering, and
`skeletonTables_eq_split` below is the `rfl` that says so.

**Scope.** This closes the *shape* of the demand side only. Byte (including Range) and Program are
the channels a recount can close, because a provider supplies them unilaterally. State and Memory
cannot be recounted: their balance is a clock telescope and a per-address touch chain respectively,
and they remain explicit hypotheses — the same split the exact transport lives with
(`ExactNativeGlobalContract.remainingIntegerBalance`).
-/


namespace SP1Clean.Soundness

open Air.Flat (Table)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-- The trace's own verifier row, as a built table. Definitionally the row Clean's ensemble
verifier checks — `Assembly.lean`'s `witness_verifierTable` is the bridge. -/
def skeletonVerifierTable : Table (ZMod p) :=
  Table.build (verifierComponent (p := p)) [trace.publicValues] trace.data trace.hint

/-- Every table that *consumes* preprocessed provider keys, and no table that supplies them: the
verifier row, the twenty-five instruction tables, and the four-table
MemoryInit/MemoryFinalize/MemoryBump/StateBump tail. -/
def skeletonTables : List (Table (ZMod p)) :=
  trace.skeletonVerifierTable ::
    (trace.tables.take instructionTableCount ++
      trace.tables.drop (instructionTableCount + preprocessedProviderTableCount))

/-- The skeleton really is the assembled table list with the preprocessed provider window removed:
the same `tables`, split at the same two positions. -/
theorem skeletonTables_eq_split :
    trace.skeletonTables =
      trace.skeletonVerifierTable ::
        (trace.tables.take instructionTableCount ++
          trace.tables.drop (instructionTableCount + preprocessedProviderTableCount)) :=
  rfl

/-- The literal Clean access ledger of the consumer side. Preprocessed providers are absent by
construction, so a multiplicity recounted against this cannot depend on itself. -/
def skeletonLedger : LookupAccessList :=
  tablesCleanAccesses trace.skeletonTables

@[simp] theorem skeletonLedger_eq :
    trace.skeletonLedger =
      tableCleanAccesses trace.skeletonVerifierTable ++
        tablesCleanAccesses
          (trace.tables.take instructionTableCount ++
            trace.tables.drop (instructionTableCount + preprocessedProviderTableCount)) := by
  simp only [skeletonLedger, skeletonTables, tablesCleanAccesses, List.flatMap_cons]

/-- How many times the shard's consumers ask for one provider key.

This is the multiplicity an honest provider row must carry at that key. It is
`LookupAccessList.providerRecount` — the same function the exact→native transport recounts with,
not a second copy of it. -/
def providerDemand (key : LookupAccessList.LookupKey) : ℕ :=
  LookupAccessList.providerRecount trace.skeletonLedger key

/-- A key no consumer touches is demanded zero times, so the closure may omit its row entirely
rather than emit a zero-multiplicity padding row. -/
theorem providerDemand_eq_zero_of_untouched {key : LookupAccessList.LookupKey}
    (h : LookupAccessList.multiplicitySum trace.skeletonLedger key = 0) :
    trace.providerDemand key = 0 :=
  LookupAccessList.providerRecount_eq_zero_of_balanced h

/-! ### The trace's own closure

Instantiating the ledger closure at this trace's consumer skeleton. `preprocessedKey` is the scope
decision made concrete: the Byte bus (which carries the seventeen fixed Range widths as well as the
six byte opcodes) and the Program bus are supplied by preprocessed provider tables, so a recount can
close them. State and Memory are not, and `closingAccesses_not_preprocessed` records that the
closure leaves them untouched rather than quietly perturbing them.
-/

/-- The buses a provider closure is allowed to supply. -/
def preprocessedKey (key : LookupAccessList.LookupKey) : Bool :=
  match key.1 with
  | .Byte | .Program => true
  | .Memory | .State | .Exit => false

/-- The provider ledger this trace's consumers demand: one recounted access per touched
Byte/Program key. -/
def closingAccesses : LookupAccessList :=
  LookupAccessList.closingAccesses trace.skeletonLedger
    (LookupAccessList.closingKeys trace.skeletonLedger preprocessedKey)

/-- **Byte and Program balance, derived rather than assumed** — given only that no consumer key is
already net-supplied. This is the statement that replaces a per-shard evaluation of the whole
ledger. -/
theorem closingAccesses_balances
    (hnonpos : ∀ key ∈ LookupAccessList.closingKeys trace.skeletonLedger preprocessedKey,
      LookupAccessList.multiplicitySum trace.skeletonLedger key ≤ 0)
    {key : LookupAccessList.LookupKey} (hsel : preprocessedKey key = true) :
    LookupAccessList.multiplicitySum (trace.skeletonLedger ++ trace.closingAccesses) key = 0 :=
  LookupAccessList.multiplicitySum_append_closing trace.skeletonLedger preprocessedKey hnonpos hsel

/-- The closure contributes nothing on State or Memory, so a balance already established there is
undisturbed by adding providers. -/
theorem closingAccesses_not_preprocessed {key : LookupAccessList.LookupKey}
    (hsel : preprocessedKey key = false) :
    LookupAccessList.multiplicitySum trace.closingAccesses key = 0 :=
  LookupAccessList.multiplicitySum_closingAccesses_of_not_select trace.skeletonLedger hsel

/-- Concretely: State keys are outside the closure's remit. -/
theorem closingAccesses_state (key : LookupAccessList.LookupKey) (hkind : key.1 = .State) :
    LookupAccessList.multiplicitySum trace.closingAccesses key = 0 :=
  trace.closingAccesses_not_preprocessed (by simp [preprocessedKey, hkind])

/-- Concretely: Memory keys are outside the closure's remit. -/
theorem closingAccesses_memory (key : LookupAccessList.LookupKey) (hkind : key.1 = .Memory) :
    LookupAccessList.multiplicitySum trace.closingAccesses key = 0 :=
  trace.closingAccesses_not_preprocessed (by simp [preprocessedKey, hkind])


/-! ### The supply side: what the twenty-four preprocessed provider tables actually emit

The demand side above is a recount against a ledger the providers are absent from. This is the
other half: the ledger those providers *do* emit, computed from the eight Tier-2 table lemmas
rather than assumed. Together they are what turns Byte/Program balance from a per-shard evaluation
into a theorem.
-/

/-- The twenty-four preprocessed provider tables: the window the skeleton omits. -/
def preprocessedProviderTables : List (Table (ZMod p)) :=
  (trace.tables.drop instructionTableCount).take preprocessedProviderTableCount

/-- The window really is the six byte tables, the seventeen fixed-width range tables, and the
program table — one `rfl`, so it cannot drift from `tables` under a reordering. -/
theorem preprocessedProviderTables_eq :
    trace.preprocessedProviderTables =
      [Table.build ByteChip.U8Range.component
          (ByteChip.U8Range.traceInputs (trace.providerOccurrences (.byte .u8Range)))
            trace.data trace.hint,
        Table.build ByteChip.MSB.component
          (ByteChip.MSB.traceInputs (trace.providerOccurrences (.byte .msb)))
            trace.data trace.hint,
        Table.build ByteChip.AndByte.component
          (ByteChip.AndByte.traceInputs (trace.providerOccurrences (.byte .andByte)))
            trace.data trace.hint,
        Table.build ByteChip.OrByte.component
          (ByteChip.OrByte.traceInputs (trace.providerOccurrences (.byte .orByte)))
            trace.data trace.hint,
        Table.build ByteChip.XorByte.component
          (ByteChip.XorByte.traceInputs (trace.providerOccurrences (.byte .xorByte)))
            trace.data trace.hint,
        Table.build ByteChip.Ltu.component
          (ByteChip.Ltu.traceInputs (trace.providerOccurrences (.byte .ltu)))
            trace.data trace.hint] ++
      trace.rangeTables ++
      [Table.build ProgramProviderChip.component
        (ProgramProviderChip.traceInputs (trace.providerOccurrences .program))
          trace.data trace.hint] := rfl

/--
**The capacity contract a trace generator owes the ledger.**

A provider row carries its aggregate count in one field element, and the machine's centered ledger
reads that field element back as a signed integer. Recovering the count exactly therefore needs the
count to be under half the field — a fact about the *generator*, not a constraint any provider
circuit can impose on itself. `Assembly.lean`'s `WellFormed` collects what each table needs of its
occurrences' semantic content; this collects what the ledger needs of their magnitudes, plus the
five Program key cells the program circuit passes through unchecked.
-/
structure CountsFit : Prop where
  u8Range : ∀ e ∈ trace.providerOccurrences (.byte .u8Range), e.MultiplicityFits p
  msb : ∀ e ∈ trace.providerOccurrences (.byte .msb), e.MultiplicityFits p
  andByte : ∀ e ∈ trace.providerOccurrences (.byte .andByte), e.MultiplicityFits p
  orByte : ∀ e ∈ trace.providerOccurrences (.byte .orByte), e.MultiplicityFits p
  xorByte : ∀ e ∈ trace.providerOccurrences (.byte .xorByte), e.MultiplicityFits p
  ltu : ∀ e ∈ trace.providerOccurrences (.byte .ltu), e.MultiplicityFits p
  range : ∀ width e, e ∈ trace.providerOccurrences (.range width) → e.MultiplicityFits p
  rom : ∀ e ∈ trace.providerOccurrences .program, e.MultiplicityFits p
  romKeys : ∀ e ∈ trace.providerOccurrences .program, RomKeyFits e

/-- The ledger the preprocessed providers supply, as an occurrence list rather than as a fold over
built rows. -/
def providerLedger : LookupAccessList :=
  (trace.providerOccurrences (.byte .u8Range)).map u8RangeAccess ++
    (trace.providerOccurrences (.byte .msb)).map msbAccess ++
    (trace.providerOccurrences (.byte .andByte)).map andAccess ++
    (trace.providerOccurrences (.byte .orByte)).map orAccess ++
    (trace.providerOccurrences (.byte .xorByte)).map xorAccess ++
    (trace.providerOccurrences (.byte .ltu)).map ltuAccess ++
    (RangeChip.allWidths.flatMap fun width =>
      (trace.providerOccurrences (.range width)).map (rangeAccess width)) ++
    (trace.providerOccurrences .program).map programEntryAccess

/-- **What the twenty-four provider tables emit is exactly their occurrence lists.**

Every step is one of the eight Tier-2 lemmas; nothing here evaluates a row. -/
theorem preprocessedProviderLedger_eq (hwf : trace.WellFormed) (hfit : trace.CountsFit) :
    tablesCleanAccesses trace.preprocessedProviderTables = trace.providerLedger := by
  rw [preprocessedProviderTables_eq]
  simp only [tablesCleanAccesses, List.flatMap_cons, List.flatMap_nil, List.flatMap_append,
    List.append_nil, rangeTables,
    u8Range_traceTable_cleanAccesses _ _ _ (hwf.provider (.byte .u8Range)) hfit.u8Range,
    msb_traceTable_cleanAccesses _ _ _ (hwf.provider (.byte .msb)) hfit.msb,
    and_traceTable_cleanAccesses _ _ _ (hwf.provider (.byte .andByte)) hfit.andByte,
    or_traceTable_cleanAccesses _ _ _ (hwf.provider (.byte .orByte)) hfit.orByte,
    xor_traceTable_cleanAccesses _ _ _ (hwf.provider (.byte .xorByte)) hfit.xorByte,
    ltu_traceTable_cleanAccesses _ _ _ (hwf.provider (.byte .ltu)) hfit.ltu,
    program_traceTable_cleanAccesses _ _ _ hfit.romKeys hfit.rom]
  simp only [providerLedger, List.flatMap_def, List.map_map, Function.comp_def,
    range_traceTable_cleanAccesses _ _ _ _ (fun e he => hwf.provider (.range _) e he)
      (fun e he => hfit.range _ e he)]
  simp [List.append_assoc]

end SupportedCoreTraceWitness

end SP1Clean.Soundness
