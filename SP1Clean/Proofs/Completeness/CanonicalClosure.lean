import SP1Clean.Proofs.Completeness.ClosureRealization
import SP1Clean.Proofs.Completeness.FieldClosure

/-!
# Canonical preprocessed-provider closure

`ClosureRealization.lean` computes the unique aggregate Byte, Range, and Program occurrence lists
which close a trace's provider-free consumer skeleton.  This module makes that computation into a
trace transformer.  The instruction, boundary, and bump portions are preserved verbatim; only the
twenty-four preprocessed-provider lists are replaced.

The crucial fixed-point fact is `canonicalClosure_skeletonLedger`: the provider window is absent
from the skeleton by construction, so replacing that window cannot change the demand being
recounted.  Consequently the transformed trace realizes its *own* closure, rather than merely the
closure of the input trace.
-/

namespace SP1Clean.Soundness

open Air.Flat (Table)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance canonicalClosureFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

open LookupAccessList (LookupKey keyOf multOf multiplicitySum)

/-! ## The field-valued provider ledger

The historical `providerLedger` stores the intended natural aggregate count as an integer.  The
actual Clean row stores that count in `ZMod p`; its centered representative may therefore differ
when the count crosses `p / 2`.  `withFieldMultiplicity` keeps the key and records that actual
representative.  Casting it back to `ZMod p` is lossless for *every* count.
-/

/-- Replace only an access's multiplicity by the centered representative of an actual field
multiplicity. -/
def withFieldMultiplicity (access : LookupAccess) (multiplicity : ZMod p) : LookupAccess :=
  (access.1, access.2.1, access.2.2.1, signedVal multiplicity)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
@[simp] theorem keyOf_withFieldMultiplicity (access : LookupAccess) (multiplicity : ZMod p) :
    keyOf (withFieldMultiplicity access multiplicity) = keyOf access := rfl

omit [Fact (2 ^ 25 < p)] in
theorem intCast_multOf_withFieldMultiplicity (access : LookupAccess) (multiplicity : ZMod p) :
    ((multOf (withFieldMultiplicity access multiplicity) : ℤ) : ZMod p) = multiplicity :=
  intCast_signedVal multiplicity

omit [Fact (2 ^ 25 < p)] in
/-- Replacing each integer multiplicity by any congruent centered field representative preserves
every key's sum modulo `p`. -/
theorem intCast_multiplicitySum_map_congr {Entry : Type}
    (entries : List Entry) (actual intended : Entry → LookupAccess)
    (hkey : ∀ entry, keyOf (actual entry) = keyOf (intended entry))
    (hmult : ∀ entry,
      ((multOf (actual entry) : ℤ) : ZMod p) = ((multOf (intended entry) : ℤ) : ZMod p))
    (key : LookupKey) :
    ((multiplicitySum (entries.map actual) key : ℤ) : ZMod p) =
      ((multiplicitySum (entries.map intended) key : ℤ) : ZMod p) := by
  induction entries with
  | nil => simp [LookupAccessList.multiplicitySum_nil]
  | cons entry entries ih =>
      simp only [List.map_cons, LookupAccessList.multiplicitySum_cons]
      rw [hkey entry]
      by_cases h : keyOf (intended entry) = key
      · simp only [h, if_true, Int.cast_add, hmult entry, ih]
      · simpa only [h, if_false, zero_add] using ih

/-- One provider occurrence's access with the multiplicity the built Clean row actually carries. -/
def actualProviderAccess (access : LookupAccess) (multiplicity : ℕ) : LookupAccess :=
  withFieldMultiplicity (p := p) access (multiplicity : ZMod p)

omit [Fact (2 ^ 25 < p)] in
theorem intCast_actualProviderAccess (access : LookupAccess) (multiplicity : ℕ) :
    ((multOf (actualProviderAccess (p := p) access multiplicity) : ℤ) : ZMod p) =
      (multiplicity : ZMod p) :=
  intCast_multOf_withFieldMultiplicity access _

omit [Fact (2 ^ 25 < p)] in
/-- List-level specialization for aggregate provider entries: replacing the intended natural
count by the actual centered representative changes no key sum in the field. -/
theorem intCast_multiplicitySum_actualProviderAccess {Entry : Type}
    (entries : List Entry) (access : Entry → LookupAccess) (multiplicity : Entry → ℕ)
    (hmult : ∀ entry, multOf (access entry) = (multiplicity entry : ℤ))
    (key : LookupKey) :
    ((multiplicitySum
        (entries.map fun entry =>
          actualProviderAccess (p := p) (access entry) (multiplicity entry)) key : ℤ) : ZMod p) =
      ((multiplicitySum (entries.map access) key : ℤ) : ZMod p) := by
  refine intCast_multiplicitySum_map_congr (p := p) entries
    (fun entry => actualProviderAccess (p := p) (access entry) (multiplicity entry)) access
    (fun _ => rfl) (fun entry => ?_) key
  rw [intCast_actualProviderAccess, hmult]
  norm_cast

omit [Fact (2 ^ 25 < p)] in
/-- Modular per-key congruence composes through a family `flatMap`. -/
theorem intCast_multiplicitySum_flatMap_congr {Index : Type}
    (indices : List Index) (actual intended : Index → LookupAccessList)
    (h : ∀ index key,
      ((multiplicitySum (actual index) key : ℤ) : ZMod p) =
        ((multiplicitySum (intended index) key : ℤ) : ZMod p))
    (key : LookupKey) :
    ((multiplicitySum (indices.flatMap actual) key : ℤ) : ZMod p) =
      ((multiplicitySum (indices.flatMap intended) key : ℤ) : ZMod p) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.flatMap_cons, LookupAccessList.multiplicitySum_append, Int.cast_add]
      rw [h index key, ih]

omit [Fact (2 ^ 25 < p)] in
/-- A raw Clean interaction ledger may use any order: once it permutes to the generic
`FieldClosure` construction, the generic field-native theorem closes it with only the actual
interaction-count bound.  This is the reusable direct-presentation route; the trace theorem below
uses the equivalent `Interaction.toAccess` modular bridge because the current compiler already
recounts in that vocabulary. -/
theorem balancedInteractions_of_fieldClosurePermutation {Message : Type*}
    [DecidableEq Message]
    (interactions : List (Interaction (ZMod p)))
    (encode : Message → Array (ZMod p))
    (pull : Message → Interaction (ZMod p))
    (provider : Message → ℕ → Interaction (ZMod p))
    (pull_msg : ∀ message, (pull message).msg = encode message)
    (pull_mult : ∀ message, (pull message).mult = -1)
    (provider_msg : ∀ message demand, (provider message demand).msg = encode message)
    (provider_mult : ∀ message demand,
      (provider message demand).mult = (demand : ZMod p))
    (messages : List Message)
    (hperm : interactions.Perm
      (SP1Clean.FieldClosure.unitPulls pull messages ++
        SP1Clean.FieldClosure.aggregateProviders provider messages))
    (hlen : interactions.length < p) :
    BalancedInteractions interactions := by
  have hlen' :
      (SP1Clean.FieldClosure.unitPulls pull messages ++
        SP1Clean.FieldClosure.aggregateProviders provider messages).length < p := by
    rwa [← hperm.length_eq]
  exact balancedInteractions_of_perm
    (SP1Clean.FieldClosure.balancedInteractions_unitPulls_append_aggregateProviders
      encode pull provider pull_msg pull_mult provider_msg provider_mult messages hlen')
    hperm.symm

/-! ### Provider-table closed forms without a multiplicity bound -/

theorem u8Range_traceTable_actualAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed) :
    tableCleanAccesses (Table.build (ByteChip.U8Range.component (p := p))
        (ByteChip.U8Range.traceInputs entries) data hint) =
      entries.map fun e => actualProviderAccess (p := p) (u8RangeAccess e) e.multiplicity := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.U8Range.component (p := p)) entries
    ByteChip.U8Range.ofEntry _ data hint (fun e he => ?_)
  rw [u8Range_buildRow_cleanAccesses]
  have hb := (hwf e he).1
  have hc := (hwf e he).2
  simp only [actualProviderAccess, withFieldMultiplicity, u8RangeAccess,
    ByteChip.U8Range.ofEntry,
    val_ofNat_small (p := p) (n := 3) (by norm_num), val_zero_zmod,
    val_natCast_eq (p := p) (by omega : e.b < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.c < 2 ^ 24)]

theorem msb_traceTable_actualAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed) :
    tableCleanAccesses (Table.build (ByteChip.MSB.component (p := p))
        (ByteChip.MSB.traceInputs entries) data hint) =
      entries.map fun e => actualProviderAccess (p := p) (msbAccess e) e.multiplicity := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.MSB.component (p := p)) entries
    ByteChip.MSB.ofEntry _ data hint (fun e he => ?_)
  rw [msb_buildRow_cleanAccesses _ _ _ (val_natCast_lt (hwf e he).1 (by norm_num))]
  simp only [actualProviderAccess, withFieldMultiplicity, msbAccess, ByteChip.MSB.ofEntry,
    val_ofNat_small (p := p) (n := 5) (by norm_num), val_ite_bit, val_zero_zmod,
    val_natCast_eq (p := p) (by have := (hwf e he).1; omega : e.b < 2 ^ 24)]

theorem and_traceTable_actualAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed) :
    tableCleanAccesses (Table.build (ByteChip.AndByte.component (p := p))
        (ByteChip.AndByte.traceInputs entries) data hint) =
      entries.map fun e => actualProviderAccess (p := p) (andAccess e) e.multiplicity := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.AndByte.component (p := p)) entries
    ByteChip.AndByte.ofEntry _ data hint (fun e he => ?_)
  rw [and_buildRow_cleanAccesses _ _ _
    ⟨val_natCast_lt (hwf e he).1 (by norm_num), val_natCast_lt (hwf e he).2 (by norm_num)⟩]
  simp only [actualProviderAccess, withFieldMultiplicity, andAccess, ByteChip.AndByte.ofEntry,
    val_zero_zmod,
    val_natCast_eq (p := p) (by have := (hwf e he).1; omega : e.b < 2 ^ 24),
    val_natCast_eq (p := p) (by have := (hwf e he).2; omega : e.c < 2 ^ 24)]

theorem or_traceTable_actualAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed) :
    tableCleanAccesses (Table.build (ByteChip.OrByte.component (p := p))
        (ByteChip.OrByte.traceInputs entries) data hint) =
      entries.map fun e => actualProviderAccess (p := p) (orAccess e) e.multiplicity := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.OrByte.component (p := p)) entries
    ByteChip.OrByte.ofEntry _ data hint (fun e he => ?_)
  rw [or_buildRow_cleanAccesses _ _ _
    ⟨val_natCast_lt (hwf e he).1 (by norm_num), val_natCast_lt (hwf e he).2 (by norm_num)⟩]
  simp only [actualProviderAccess, withFieldMultiplicity, orAccess, ByteChip.OrByte.ofEntry,
    val_one_zmod,
    val_natCast_eq (p := p) (by have := (hwf e he).1; omega : e.b < 2 ^ 24),
    val_natCast_eq (p := p) (by have := (hwf e he).2; omega : e.c < 2 ^ 24)]

theorem xor_traceTable_actualAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed) :
    tableCleanAccesses (Table.build (ByteChip.XorByte.component (p := p))
        (ByteChip.XorByte.traceInputs entries) data hint) =
      entries.map fun e => actualProviderAccess (p := p) (xorAccess e) e.multiplicity := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.XorByte.component (p := p)) entries
    ByteChip.XorByte.ofEntry _ data hint (fun e he => ?_)
  rw [xor_buildRow_cleanAccesses _ _ _
    ⟨val_natCast_lt (hwf e he).1 (by norm_num), val_natCast_lt (hwf e he).2 (by norm_num)⟩]
  simp only [actualProviderAccess, withFieldMultiplicity, xorAccess, ByteChip.XorByte.ofEntry,
    val_ofNat_small (p := p) (n := 2) (by norm_num),
    val_natCast_eq (p := p) (by have := (hwf e he).1; omega : e.b < 2 ^ 24),
    val_natCast_eq (p := p) (by have := (hwf e he).2; omega : e.c < 2 ^ 24)]

theorem ltu_traceTable_actualAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed) :
    tableCleanAccesses (Table.build (ByteChip.Ltu.component (p := p))
        (ByteChip.Ltu.traceInputs entries) data hint) =
      entries.map fun e => actualProviderAccess (p := p) (ltuAccess e) e.multiplicity := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.Ltu.component (p := p)) entries
    ByteChip.Ltu.ofEntry _ data hint (fun e he => ?_)
  rw [ltu_buildRow_cleanAccesses _ _ _
    ⟨val_natCast_lt (hwf e he).1 (by norm_num), val_natCast_lt (hwf e he).2 (by norm_num)⟩]
  simp only [actualProviderAccess, withFieldMultiplicity, ltuAccess, ByteChip.Ltu.ofEntry,
    val_ofNat_small (p := p) (n := 4) (by norm_num), val_ite_bit,
    val_natCast_eq (p := p) (by have := (hwf e he).1; omega : e.b < 2 ^ 24),
    val_natCast_eq (p := p) (by have := (hwf e he).2; omega : e.c < 2 ^ 24)]

theorem range_traceTable_actualAccesses (width : RangeChip.Width)
    (entries : List TraceGen.RangeEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed width.val) :
    tableCleanAccesses (Table.build (RangeChip.componentFor (p := p) width)
        (RangeChip.traceInputs entries) data hint) =
      entries.map fun e =>
        actualProviderAccess (p := p) (rangeAccess width e) e.multiplicity := by
  refine tableCleanAccesses_build_map_singleton (RangeChip.componentFor (p := p) width) entries
    RangeChip.ofEntry _ data hint (fun e he => ?_)
  rw [range_buildRow_cleanAccesses]
  have ha : e.a < 2 ^ 24 := by
    have hlt : e.a < 2 ^ width.val := hwf e he
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [actualProviderAccess, withFieldMultiplicity, rangeAccess, RangeChip.ofEntry,
    val_ofNat_small (p := p) (n := 6) (by norm_num), val_zero_zmod,
    val_natCast_eq (p := p) ha,
    val_natCast_eq (p := p) (by omega : width.val < 2 ^ 24)]

theorem program_traceTable_actualAccesses (entries : List TraceGen.RomEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hfit : ∀ e ∈ entries, RomKeyFits e) :
    tableCleanAccesses (Table.build (ProgramProviderChip.component (p := p))
        (ProgramProviderChip.traceInputs entries) data hint) =
      entries.map fun e =>
        actualProviderAccess (p := p) (programEntryAccess e) e.multiplicity := by
  refine tableCleanAccesses_build_map_singleton (ProgramProviderChip.component (p := p)) entries
    ProgramProviderChip.ofEntry _ data hint (fun e he => ?_)
  rw [program_buildRow_cleanAccesses]
  obtain ⟨hop, hopa, hopa0, himmb, himmc⟩ := hfit e he
  simp only [actualProviderAccess, withFieldMultiplicity, programRowAccess, programEntryAccess,
    ProgramProviderChip.ofEntry, TraceGen.wordOfNat_zero, TraceGen.wordOfNat_one,
    TraceGen.wordOfNat_two, TraceGen.wordOfNat_three,
    val_natCast_eq (p := p) (by omega : e.pc % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.pc / 2 ^ 16 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.pc / 2 ^ 32 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opB % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opB / 2 ^ 16 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opB / 2 ^ 32 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opB / 2 ^ 48 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opC % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opC / 2 ^ 16 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opC / 2 ^ 32 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opC / 2 ^ 48 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) hop, val_natCast_eq (p := p) hopa,
    val_natCast_eq (p := p) hopa0, val_natCast_eq (p := p) himmb,
    val_natCast_eq (p := p) himmc]

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-! ## The preprocessed provider window, at actual field multiplicities -/

/-- The canonical access keys of the provider rows, but with each row's actual field
multiplicity read through `signedVal`. -/
def actualProviderLedger : LookupAccessList :=
  ((trace.providerOccurrences (.byte .u8Range)).map fun e =>
      actualProviderAccess (p := p) (u8RangeAccess e) e.multiplicity) ++
    ((trace.providerOccurrences (.byte .msb)).map fun e =>
      actualProviderAccess (p := p) (msbAccess e) e.multiplicity) ++
    ((trace.providerOccurrences (.byte .andByte)).map fun e =>
      actualProviderAccess (p := p) (andAccess e) e.multiplicity) ++
    ((trace.providerOccurrences (.byte .orByte)).map fun e =>
      actualProviderAccess (p := p) (orAccess e) e.multiplicity) ++
    ((trace.providerOccurrences (.byte .xorByte)).map fun e =>
      actualProviderAccess (p := p) (xorAccess e) e.multiplicity) ++
    ((trace.providerOccurrences (.byte .ltu)).map fun e =>
      actualProviderAccess (p := p) (ltuAccess e) e.multiplicity) ++
    (RangeChip.allWidths.flatMap fun width =>
      (trace.providerOccurrences (.range width)).map fun e =>
        actualProviderAccess (p := p) (rangeAccess width e) e.multiplicity) ++
    ((trace.providerOccurrences .program).map fun e =>
      actualProviderAccess (p := p) (programEntryAccess e) e.multiplicity)

/-- The actual Clean provider tables emit `actualProviderLedger`.  Unlike
`preprocessedProviderLedger_eq`, this needs no multiplicity-capacity premise. -/
theorem preprocessedProviderActualLedger_eq (hwf : trace.WellFormed)
    (hromKeys : ∀ e ∈ trace.providerOccurrences .program, RomKeyFits e) :
    tablesCleanAccesses trace.preprocessedProviderTables = trace.actualProviderLedger := by
  rw [preprocessedProviderTables_eq]
  simp only [tablesCleanAccesses, List.flatMap_cons, List.flatMap_nil, List.flatMap_append,
    List.append_nil, rangeTables,
    u8Range_traceTable_actualAccesses _ _ _ (hwf.provider (.byte .u8Range)),
    msb_traceTable_actualAccesses _ _ _ (hwf.provider (.byte .msb)),
    and_traceTable_actualAccesses _ _ _ (hwf.provider (.byte .andByte)),
    or_traceTable_actualAccesses _ _ _ (hwf.provider (.byte .orByte)),
    xor_traceTable_actualAccesses _ _ _ (hwf.provider (.byte .xorByte)),
    ltu_traceTable_actualAccesses _ _ _ (hwf.provider (.byte .ltu)),
    program_traceTable_actualAccesses _ _ _ hromKeys]
  simp only [actualProviderLedger, List.flatMap_def, List.map_map, Function.comp_def,
    range_traceTable_actualAccesses _ _ _ _
      (fun e he => hwf.provider (.range _) e he)]
  simp [List.append_assoc]

/-- The actual provider ledger and the natural-demand ledger have identical per-key sums modulo
`p`, for arbitrary aggregate counts. -/
theorem actualProviderLedger_mod_providerLedger (key : LookupKey) :
    ((multiplicitySum trace.actualProviderLedger key : ℤ) : ZMod p) =
      ((multiplicitySum trace.providerLedger key : ℤ) : ZMod p) := by
  simp only [actualProviderLedger, providerLedger,
    LookupAccessList.multiplicitySum_append, Int.cast_add]
  rw [intCast_multiplicitySum_actualProviderAccess _ u8RangeAccess (fun e => e.multiplicity)
      (fun _ => rfl) key,
    intCast_multiplicitySum_actualProviderAccess _ msbAccess (fun e => e.multiplicity)
      (fun _ => rfl) key,
    intCast_multiplicitySum_actualProviderAccess _ andAccess (fun e => e.multiplicity)
      (fun _ => rfl) key,
    intCast_multiplicitySum_actualProviderAccess _ orAccess (fun e => e.multiplicity)
      (fun _ => rfl) key,
    intCast_multiplicitySum_actualProviderAccess _ xorAccess (fun e => e.multiplicity)
      (fun _ => rfl) key,
    intCast_multiplicitySum_actualProviderAccess _ ltuAccess (fun e => e.multiplicity)
      (fun _ => rfl) key,
    intCast_multiplicitySum_flatMap_congr RangeChip.allWidths
      (fun width => (trace.providerOccurrences (.range width)).map fun e =>
        actualProviderAccess (p := p) (rangeAccess width e) e.multiplicity)
      (fun width => (trace.providerOccurrences (.range width)).map (rangeAccess width))
      (fun width k => intCast_multiplicitySum_actualProviderAccess _ (rangeAccess width)
        (fun e => e.multiplicity) (fun _ => rfl) k) key,
    intCast_multiplicitySum_actualProviderAccess _ programEntryAccess
      (fun e => e.multiplicity) (fun _ => rfl) key]

/-- The canonical occurrence list for one provider identity.  Preprocessed providers are rebuilt
from the consumer skeleton; Memory boundaries and the two bump tables are left untouched. -/
def canonicalProviderOccurrences : (id : ProviderTableId) → List id.Occurrence
  | .byte .u8Range => trace.closureU8RangeEntries
  | .byte .msb => trace.closureMsbEntries
  | .byte .andByte => trace.closureAndByteEntries
  | .byte .orByte => trace.closureOrByteEntries
  | .byte .xorByte => trace.closureXorByteEntries
  | .byte .ltu => trace.closureLtuEntries
  | .range width => trace.closureRangeEntries width
  | .program => trace.closureRomEntries
  | .memoryInit => trace.providerOccurrences .memoryInit
  | .memoryFinalize => trace.providerOccurrences .memoryFinalize
  | .memoryBump => trace.providerOccurrences .memoryBump
  | .stateBump => trace.providerOccurrences .stateBump

/-- Rebuild only the Byte, Range, and Program provider window from the trace's own demand. -/
def canonicalClosure : SupportedCoreTraceWitness p where
  instructionEvents := trace.instructionEvents
  providerOccurrences := trace.canonicalProviderOccurrences
  data := trace.data
  hint := trace.hint
  boundary := trace.boundary

@[simp] theorem canonicalClosure_providerOccurrences (id : ProviderTableId) :
    trace.canonicalClosure.providerOccurrences id = trace.canonicalProviderOccurrences id := rfl

@[simp] theorem canonicalClosure_instructionEvents (id : InstructionChipId) :
    trace.canonicalClosure.instructionEvents id = trace.instructionEvents id := rfl

@[simp] theorem canonicalClosure_data : trace.canonicalClosure.data = trace.data := rfl
@[simp] theorem canonicalClosure_hint : trace.canonicalClosure.hint = trace.hint := rfl
@[simp] theorem canonicalClosure_boundary : trace.canonicalClosure.boundary = trace.boundary := rfl
@[simp] theorem canonicalClosure_publicValues :
    trace.canonicalClosure.publicValues = trace.publicValues := rfl

theorem canonicalClosure_memoryInit :
    trace.canonicalClosure.providerOccurrences .memoryInit =
      trace.providerOccurrences .memoryInit := rfl

theorem canonicalClosure_memoryFinalize :
    trace.canonicalClosure.providerOccurrences .memoryFinalize =
      trace.providerOccurrences .memoryFinalize := rfl

theorem canonicalClosure_memoryBump :
    trace.canonicalClosure.providerOccurrences .memoryBump =
      trace.providerOccurrences .memoryBump := rfl

theorem canonicalClosure_stateBump :
    trace.canonicalClosure.providerOccurrences .stateBump =
      trace.providerOccurrences .stateBump := rfl

@[simp] theorem canonicalClosure_instructionTableFor (id : InstructionChipId) :
    trace.canonicalClosure.instructionTableFor id = trace.instructionTableFor id := by
  cases id <;> rfl

theorem canonicalClosure_instructionTables :
    trace.canonicalClosure.instructionTables = trace.instructionTables := by
  rw [instructionTables, instructionTables]
  exact List.map_congr_left fun id _ => trace.canonicalClosure_instructionTableFor id

@[simp] theorem canonicalClosure_skeletonVerifierTable :
    trace.canonicalClosure.skeletonVerifierTable = trace.skeletonVerifierTable := rfl

/-- The prefix selected by `skeletonTables` is exactly the instruction segment. -/
theorem tables_take_instructionTables (t : SupportedCoreTraceWitness p) :
    t.tables.take instructionTableCount = t.instructionTables := by
  simp [tables, instructionTableCount, instructionTables]

/-- Dropping the instruction segment and the 24-table preprocessed window leaves exactly the four
Memory/State boundary-and-bump tables. -/
theorem tables_drop_preprocessed (t : SupportedCoreTraceWitness p) :
    t.tables.drop (instructionTableCount + preprocessedProviderTableCount) =
      t.providerTables.drop preprocessedProviderTableCount := by
  simp [tables, instructionTableCount, preprocessedProviderTableCount, instructionTables,
    List.drop_append]

/-- The provider suffix after the 24 preprocessed tables is exactly the two Memory boundaries and
the two canonicalization-bump tables. -/
theorem providerTables_drop_preprocessed (t : SupportedCoreTraceWitness p) :
    t.providerTables.drop preprocessedProviderTableCount =
      [t.providerTableFor .memoryInit, t.providerTableFor .memoryFinalize,
        t.providerTableFor .memoryBump, t.providerTableFor .stateBump] := by
  simp [providerTables, ProviderTableId.all, ByteProviderId.all,
    preprocessedProviderTableCount, List.drop_append]

/-- Canonical closure preserves the four-table suffix after the preprocessed window. -/
theorem canonicalClosure_providerTables_drop :
    trace.canonicalClosure.providerTables.drop preprocessedProviderTableCount =
      trace.providerTables.drop preprocessedProviderTableCount := by
  simp [providerTables, ProviderTableId.all, ByteProviderId.all,
    preprocessedProviderTableCount, canonicalClosure, List.drop_append]
  rw [List.drop_eq_nil_of_le (by simp), List.drop_eq_nil_of_le (by simp)]
  rfl

/-- Replacing the preprocessed-provider occurrence lists leaves the provider-free skeleton tables
unchanged.  This is deliberately a definitional audit of the two registry orders. -/
theorem canonicalClosure_skeletonTables :
    trace.canonicalClosure.skeletonTables = trace.skeletonTables := by
  rw [skeletonTables, skeletonTables, tables_take_instructionTables,
    tables_take_instructionTables, tables_drop_preprocessed, tables_drop_preprocessed,
    canonicalClosure_instructionTables, canonicalClosure_providerTables_drop,
    canonicalClosure_skeletonVerifierTable]

/-- Therefore canonical closure does not change the Clean ledger against which provider demand is
computed. -/
theorem canonicalClosure_skeletonLedger :
    trace.canonicalClosure.skeletonLedger = trace.skeletonLedger := by
  exact congrArg tablesCleanAccesses trace.canonicalClosure_skeletonTables

@[simp] theorem canonicalClosure_closingKeyList :
    trace.canonicalClosure.closingKeyList = trace.closingKeyList := by
  rw [closingKeyList, closingKeyList, canonicalClosure_skeletonLedger]

@[simp] theorem canonicalClosure_providerDemand (key : LookupAccessList.LookupKey) :
    trace.canonicalClosure.providerDemand key = trace.providerDemand key := by
  rw [providerDemand, providerDemand, canonicalClosure_skeletonLedger]

@[simp] theorem canonicalClosure_closureU8RangeEntries :
    trace.canonicalClosure.closureU8RangeEntries = trace.closureU8RangeEntries := by
  simp [closureU8RangeEntries]

@[simp] theorem canonicalClosure_closureMsbEntries :
    trace.canonicalClosure.closureMsbEntries = trace.closureMsbEntries := by
  simp [closureMsbEntries]

@[simp] theorem canonicalClosure_closureAndByteEntries :
    trace.canonicalClosure.closureAndByteEntries = trace.closureAndByteEntries := by
  simp [closureAndByteEntries]

@[simp] theorem canonicalClosure_closureOrByteEntries :
    trace.canonicalClosure.closureOrByteEntries = trace.closureOrByteEntries := by
  simp [closureOrByteEntries]

@[simp] theorem canonicalClosure_closureXorByteEntries :
    trace.canonicalClosure.closureXorByteEntries = trace.closureXorByteEntries := by
  simp [closureXorByteEntries]

@[simp] theorem canonicalClosure_closureLtuEntries :
    trace.canonicalClosure.closureLtuEntries = trace.closureLtuEntries := by
  simp [closureLtuEntries]

@[simp] theorem canonicalClosure_closureRangeEntries (width : RangeChip.Width) :
    trace.canonicalClosure.closureRangeEntries width = trace.closureRangeEntries width := by
  simp [closureRangeEntries]

@[simp] theorem canonicalClosure_closureRomEntries :
    trace.canonicalClosure.closureRomEntries = trace.closureRomEntries := by
  simp [closureRomEntries]

/-- The rebuilt trace realizes its own closure.  Idempotence is supplied by skeleton invariance. -/
theorem canonicalClosure_closureRealized : trace.canonicalClosure.ClosureRealized where
  u8Range := trace.canonicalClosure_closureU8RangeEntries.symm
  msb := trace.canonicalClosure_closureMsbEntries.symm
  andByte := trace.canonicalClosure_closureAndByteEntries.symm
  orByte := trace.canonicalClosure_closureOrByteEntries.symm
  xorByte := trace.canonicalClosure_closureXorByteEntries.symm
  ltu := trace.canonicalClosure_closureLtuEntries.symm
  range width := (trace.canonicalClosure_closureRangeEntries width).symm
  rom := trace.canonicalClosure_closureRomEntries.symm

/-- Servability depends only on the provider-free skeleton, so it is preserved by canonical
closure. -/
theorem DemandServable.canonicalClosure (hserv : trace.DemandServable) :
    trace.canonicalClosure.DemandServable where
  byte key hkey hkind := hserv.byte key (by simpa using hkey) hkind
  program key hkey hkind := hserv.program key (by simpa using hkey) hkind

/-- Program servability contains exactly the unchecked-cell bounds needed to read a built ROM
provider row back at its intended key. -/
theorem closureRomEntries_romKeyFits (hserv : trace.DemandServable) :
    ∀ entry ∈ trace.closureRomEntries, RomKeyFits entry := by
  intro entry hentry
  obtain ⟨key, hkey, rfl⟩ := List.mem_map.mp hentry
  have hmem : key ∈ trace.closingKeyList := (List.mem_filter.mp hkey).1
  have hsel : IsProgramKey key = true := (List.mem_filter.mp hkey).2
  have bounds := (hserv.program key hmem (programKey_kind hsel)).2.2.2
  simpa only [RomKeyFits, romEntryOfKey] using bounds

/-- The canonical trace's ROM provider rows meet the unchecked-key bounds. -/
theorem canonicalClosure_romKeyFits (hserv : trace.DemandServable) :
    ∀ entry ∈ trace.canonicalClosure.providerOccurrences .program, RomKeyFits entry := by
  intro entry hentry
  change entry ∈ trace.closureRomEntries at hentry
  exact trace.closureRomEntries_romKeyFits hserv entry hentry

/-! ## Modular cancellation of the actual provider window -/

/-- Splitting the ensemble's literal Clean ledger around the provider window, now retaining the
actual field multiplicities rather than requiring centered recovery. -/
theorem fullLedger_multiplicitySum_actualProvider
    (hwf : trace.WellFormed)
    (hromKeys : ∀ entry ∈ trace.providerOccurrences .program, RomKeyFits entry)
    (key : LookupKey) :
    multiplicitySum trace.fullLedger key =
      multiplicitySum (trace.skeletonLedger ++ trace.actualProviderLedger) key := by
  rw [fullLedger, skeletonLedger_eq,
    trace.preprocessedProviderActualLedger_eq hwf hromKeys |>.symm]
  conv_lhs => rw [tables_split trace]
  simp only [tablesCleanAccesses_append, LookupAccessList.multiplicitySum_append]
  ring

/-- The whole actual ledger agrees modulo `p` with the legacy natural-demand ledger.  No
individual provider count is required to lie in the centered half of the field. -/
theorem fullLedger_mod_skeleton_provider
    (hwf : trace.WellFormed)
    (hromKeys : ∀ entry ∈ trace.providerOccurrences .program, RomKeyFits entry)
    (key : LookupKey) :
    ((multiplicitySum trace.fullLedger key : ℤ) : ZMod p) =
      ((multiplicitySum (trace.skeletonLedger ++ trace.providerLedger) key : ℤ) : ZMod p) := by
  rw [trace.fullLedger_multiplicitySum_actualProvider hwf hromKeys,
    LookupAccessList.multiplicitySum_append, LookupAccessList.multiplicitySum_append,
    Int.cast_add, Int.cast_add, trace.actualProviderLedger_mod_providerLedger key]

/-- The natural-demand ledger cancels a selected consumer key exactly over `ℤ`. -/
theorem skeleton_providerLedger_balanced
    (hsupply : trace.SuppliesDemand)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      multiplicitySum trace.skeletonLedger key ≤ 0)
    {key : LookupKey} (hsel : preprocessedKey key = true) :
    multiplicitySum (trace.skeletonLedger ++ trace.providerLedger) key = 0 := by
  rw [LookupAccessList.multiplicitySum_append, hsupply key]
  by_cases hkey : key ∈ trace.closingKeyList
  · rw [if_pos hkey]
    have hbalanced := trace.closingAccesses_balances hnonpos hsel
    rw [LookupAccessList.multiplicitySum_append, closingAccesses,
      LookupAccessList.multiplicitySum_closingAccesses _
        (LookupAccessList.closingKeys_nodup _ _) hkey] at hbalanced
    exact hbalanced
  · rw [if_neg hkey, add_zero]
    have hnot : key ∉ LookupAccessList.closingKeys trace.skeletonLedger preprocessedKey := hkey
    have hbalanced := trace.closingAccesses_balances hnonpos hsel
    rw [LookupAccessList.multiplicitySum_append, closingAccesses,
      LookupAccessList.multiplicitySum_closingAccesses_of_not_mem _ hnot, add_zero] at hbalanced
    exact hbalanced

/-- Field-native cancellation at every Byte or Program key in the actual full ledger. -/
theorem fullLedger_intCast_zero
    (hwf : trace.WellFormed)
    (hromKeys : ∀ entry ∈ trace.providerOccurrences .program, RomKeyFits entry)
    (hsupply : trace.SuppliesDemand)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      multiplicitySum trace.skeletonLedger key ≤ 0)
    {key : LookupKey} (hsel : preprocessedKey key = true) :
    ((multiplicitySum trace.fullLedger key : ℤ) : ZMod p) = 0 := by
  rw [trace.fullLedger_mod_skeleton_provider hwf hromKeys key,
    trace.skeleton_providerLedger_balanced hsupply hnonpos hsel, Int.cast_zero]

/-- **Canonical Byte/Program balance in Clean's native field semantics.**

This is the replacement for `balancedOn_of_closure` on the aggregate-provider buses.  Its only
capacity premise is Clean's own interaction-list bound.  In particular there is no `CountsFit`,
`ProviderMultiplicitiesFit`, or `2 * multiplicity ≤ p` premise. -/
theorem canonicalClosure_balancedInteractions
    (hwf : trace.canonicalClosure.WellFormed)
    (hserv : trace.DemandServable)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      multiplicitySum trace.skeletonLedger key ≤ 0)
    (channel : RawChannel (ZMod p))
    (hchannel : channel ∈ (sp1Ensemble (p := p)).channels)
    (hkind : kindOf channel.name = InteractionKind.Byte ∨
      kindOf channel.name = InteractionKind.Program)
    (hlen : (trace.canonicalClosure.witness.interactionsWith channel).length < p) :
    BalancedInteractions (trace.canonicalClosure.witness.interactionsWith channel) := by
  let closed := trace.canonicalClosure
  have hservClosed : closed.DemandServable := hserv.canonicalClosure
  have hreal : closed.ClosureRealized := by
    change trace.canonicalClosure.ClosureRealized
    exact trace.canonicalClosure_closureRealized
  have hsupply : closed.SuppliesDemand :=
    closed.suppliesDemand_of_closureRealized hreal hservClosed
  have hnonposClosed : ∀ key ∈ closed.closingKeyList,
      multiplicitySum closed.skeletonLedger key ≤ 0 := by
    intro key hkey
    rw [canonicalClosure_closingKeyList] at hkey
    rw [canonicalClosure_skeletonLedger]
    exact hnonpos key hkey
  have hromKeys : ∀ entry ∈ closed.providerOccurrences .program, RomKeyFits entry :=
    trace.canonicalClosure_romKeyFits hserv
  constructor
  · left
    simpa only [ZMod.ringChar_zmod_n] using hlen
  · intro message
    by_cases hexists : ∃ interaction ∈ closed.witness.interactionsWith channel,
        interaction.msg = message
    · obtain ⟨interaction, hinteraction, rfl⟩ := hexists
      rw [← LookupAccessList.intCast_multiplicitySum_map_toAccess_eq_balanceOf
        (closed.witness.interactionsWith channel) channel
        (fun i hi => Air.Flat.EnsembleWitness.channel_eq_of_mem_interactionsWith hi)
        interaction hinteraction]
      rw [closed.fullLedger_multiplicitySum_channel channel hchannel (by
        have hch := Air.Flat.EnsembleWitness.channel_eq_of_mem_interactionsWith hinteraction
        simp only [Interaction.toAccess, hch])]
      refine closed.fullLedger_intCast_zero hwf hromKeys hsupply hnonposClosed ?_
      have hch := Air.Flat.EnsembleWitness.channel_eq_of_mem_interactionsWith hinteraction
      simp only [preprocessedKey, Interaction.toAccess, hch]
      rcases hkind with hkind | hkind <;> rw [hkind]
    · have hfilter :
          (closed.witness.interactionsWith channel).filter (fun i => i.msg = message) = [] :=
        List.filter_eq_nil_iff.mpr fun interaction hmem hmessage =>
          hexists ⟨interaction, hmem, by simpa using hmessage⟩
      change List.sum (List.map (fun i => i.mult)
        ((closed.witness.interactionsWith channel).filter (fun i => i.msg = message))) = 0
      rw [hfilter]
      rfl

/-- Byte-channel specialization of `canonicalClosure_balancedInteractions`. -/
theorem canonicalClosure_byte_balancedInteractions
    (hwf : trace.canonicalClosure.WellFormed)
    (hserv : trace.DemandServable)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      multiplicitySum trace.skeletonLedger key ≤ 0)
    (hlen : (trace.canonicalClosure.witness.interactionsWith
      Channels.byteChannel.toRaw).length < p) :
    BalancedInteractions
      (trace.canonicalClosure.witness.interactionsWith Channels.byteChannel.toRaw) :=
  trace.canonicalClosure_balancedInteractions hwf hserv hnonpos _
    (by simp [sp1Ensemble_channels]) (Or.inl rfl) hlen

/-- Program-channel specialization of `canonicalClosure_balancedInteractions`. -/
theorem canonicalClosure_program_balancedInteractions
    (hwf : trace.canonicalClosure.WellFormed)
    (hserv : trace.DemandServable)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      multiplicitySum trace.skeletonLedger key ≤ 0)
    (hlen : (trace.canonicalClosure.witness.interactionsWith
      Channels.programChannel.toRaw).length < p) :
    BalancedInteractions
      (trace.canonicalClosure.witness.interactionsWith Channels.programChannel.toRaw) :=
  trace.canonicalClosure_balancedInteractions hwf hserv hnonpos _
    (by simp [sp1Ensemble_channels]) (Or.inr rfl) hlen

end SupportedCoreTraceWitness

end SP1Clean.Soundness
