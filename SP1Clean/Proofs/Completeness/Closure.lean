import SP1Clean.Model.CleanLedger
import SP1Clean.Proofs.Completeness.Assembly
import SP1Clean.Proofs.Completeness.ProviderTables

/-! # Recounting Byte, Range and Program demand

The consumer ledger combines the actual public verifier with physical tables outside the
preprocessed provider window. The 24 excluded tables are the six Byte providers, seventeen
Range widths and Program. Recounting this ledger cannot depend on those providers' multiplicities.

`LookupAccessList.providerRecount` supplies the shared recount algorithm. Ledger projection keeps
all occurrences and uses Clean's interaction signs; the row lemmas below recover natural keys
and integer multiplicities under explicit range/count bounds. Evaluation uses canonical data,
while the table builders retain their separate generation inputs.

Only Byte and Program are closed by this recount. State, Memory, Exit and host-channel balance
remain separate semantic obligations. This module establishes the demand/supply ledger equations,
not a complete execution or the data-dependent program commitment.
-/

namespace SP1Clean.Soundness

open Air.Flat (Table)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-- The actual public verifier's literal access ledger, including every assertion occurrence. -/
def verifierLedger : LookupAccessList :=
  ((sp1Ensemble (p := p)).verifierOperations.interactionValues
    (Environment.fromInput trace.publicValues trace.data)).map Interaction.toAccess

/-- The physical consumers outside the 24-table preprocessed provider window. The remaining
provider tail includes MemoryInit/Finalize, both bumps, Halt and SyscallInstrs. -/
def skeletonTables : List (Table (ZMod p)) :=
  trace.tables.take instructionTableCount ++
    trace.tables.drop (instructionTableCount + preprocessedProviderTableCount)

/-- Public verifier demand followed by physical consumer demand. Preprocessed providers are
absent, so their recounted multiplicities cannot depend on their own ledger contributions. -/
def skeletonLedger : LookupAccessList :=
  trace.verifierLedger ++ tablesCleanAccesses trace.skeletonTables trace.data

@[simp] theorem skeletonLedger_eq :
    trace.skeletonLedger =
      trace.verifierLedger ++ tablesCleanAccesses
        (trace.tables.take instructionTableCount ++
          trace.tables.drop (instructionTableCount + preprocessedProviderTableCount)) trace.data := rfl

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

/-- The buses a provider closure is allowed to supply. Written as an exhaustive match on purpose:
a new `InteractionKind` must not join the closure by default, and this is where Lean makes that a
decision rather than an omission. -/
def preprocessedKey (key : LookupAccessList.LookupKey) : Bool :=
  match key.1 with
  | .Byte | .Program => true
  | .Memory | .State | .Exit | .Syscall | .PublicValues | .Unmodelled => false

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
            trace.generationData trace.hint,
        Table.build ByteChip.MSB.component
          (ByteChip.MSB.traceInputs (trace.providerOccurrences (.byte .msb)))
            trace.generationData trace.hint,
        Table.build ByteChip.AndByte.component
          (ByteChip.AndByte.traceInputs (trace.providerOccurrences (.byte .andByte)))
            trace.generationData trace.hint,
        Table.build ByteChip.OrByte.component
          (ByteChip.OrByte.traceInputs (trace.providerOccurrences (.byte .orByte)))
            trace.generationData trace.hint,
        Table.build ByteChip.XorByte.component
          (ByteChip.XorByte.traceInputs (trace.providerOccurrences (.byte .xorByte)))
            trace.generationData trace.hint,
        Table.build ByteChip.Ltu.component
          (ByteChip.Ltu.traceInputs (trace.providerOccurrences (.byte .ltu)))
            trace.generationData trace.hint] ++
      trace.rangeTables ++
      [Table.build ProgramProviderChip.component
        (ProgramProviderChip.traceInputs (trace.providerOccurrences .program))
          trace.generationData trace.hint] := rfl

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
    tablesCleanAccesses trace.preprocessedProviderTables trace.data = trace.providerLedger := by
  rw [tablesCleanAccesses_setData _ trace.data trace.generationData]
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
