import SP1Clean.Faithful.CoreAIR
import SP1Clean.Composition.Table
import SP1Clean.Proofs.Completeness.Providers

/-! # Exact preprocessing to native Byte/Range/Program providers

The pinned Core AIR exposes three verifying-key-facing preprocessed matrices: `Byte`, `Range`, and
`Program`.  Their main rows contain multiplicities, while their preprocessed rows carry the lookup
keys.  At this layer those rows are source data selected by an explicit inventory; the later PCS/
ArkLib adapter must prove that they open the verifying-key commitment.  The native Clean ensemble
represents the corresponding source-key space as twenty-four proof-producing tables (six byte
opcodes, all seventeen Range widths `0..16`, and one program-ROM table).

This file gives the constructive redistribution.  `PreprocessedProviderContract` is intentionally
explicit: it states only the **per-present-row local semantics** needed by the twenty-four native provider
circuits — Byte operation correctness, Range validity/support, and Program `RowSpec`.  It proves
neither full-matrix coverage nor identity with a particular `GuestProgram`.
`CoreAIR.Current.PreprocessedBinding` separately states the opaque matrix-opening contract, while a
verifying-key/PCS theorem and the global `SemanticBoundaryBinding` must prove that contract and connect
the opened matrices to the canonical tables and committed program.  Authentication and coverage remain
visible obligations at the global boundary.  A Type-valued `CanonicalPreprocessedInventory` is an explicit
integration input: it selects source-backed representatives for nonzero native demand without
quadratic deduplication or materializing the enormous zero-demand preprocessing universe.  Given
that inventory and its proof contract, the definitions below build all twenty-four native tables
and prove their constraints.  Provider multiplicities are not copied from the exact main matrices:
each is reconstructed from the literal Clean interaction ledger of the non-preprocessed native
skeleton.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

-- The faithfulness vocabulary (`ChipOracle`, `ChipFaithful`, `ChipRowCodec`,
-- `nativeAccesses`) is at the stratum below; this namespace no longer encloses it since the
-- 2026-08 move out of `Faithful/Transport/`.
open SP1Clean.Faithful

open Circuit
open Air.Flat (Component Table)
open SP1Clean.Channels (ProgramMsg)
open SP1Clean.LookupAccessList (LookupKey)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance preprocessedProviderFieldBound : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## Exact-row decoders -/

/-- Decode a source Program key into the native ROM-provider input.  The sixteen
preprocessed cells are copied in source order; the multiplicity is the native-consumer recount,
not the exact Program table's main column. -/
def programProviderInput (row : CoreAIR.Current.Row p .program) (multiplicity : ℕ) :
    ProgramProviderChip.Inputs (ZMod p) where
  pc0 := row.preprocessed[0]
  pc1 := row.preprocessed[1]
  pc2 := row.preprocessed[2]
  opcode := row.preprocessed[3]
  op_a := row.preprocessed[4]
  op_b := #v[row.preprocessed[5], row.preprocessed[6], row.preprocessed[7], row.preprocessed[8]]
  op_c := #v[row.preprocessed[9], row.preprocessed[10], row.preprocessed[11], row.preprocessed[12]]
  op_a_0 := row.preprocessed[13]
  imm_b := row.preprocessed[14]
  imm_c := row.preprocessed[15]
  multiplicity := (multiplicity : ZMod p)

/-- Decode one exact Byte row for the native u8-range provider. -/
def byteU8RangeInput (row : CoreAIR.Current.Row p .byteLookup) (multiplicity : ℕ) :
    ByteChip.U8Range.Inputs (ZMod p) :=
  ⟨row.preprocessed[0], row.preprocessed[1], (multiplicity : ZMod p)⟩

/-- Decode one exact Byte row for the native most-significant-bit provider. -/
def byteMsbInput (row : CoreAIR.Current.Row p .byteLookup) (multiplicity : ℕ) :
    ByteChip.MSB.Inputs (ZMod p) :=
  ⟨row.preprocessed[0], (multiplicity : ZMod p)⟩

/-- Decode one exact Byte row for the native bitwise-AND provider. -/
def byteAndInput (row : CoreAIR.Current.Row p .byteLookup) (multiplicity : ℕ) :
    ByteChip.AndByte.Inputs (ZMod p) :=
  ⟨row.preprocessed[0], row.preprocessed[1], (multiplicity : ZMod p)⟩

/-- Decode one exact Byte row for the native bitwise-OR provider. -/
def byteOrInput (row : CoreAIR.Current.Row p .byteLookup) (multiplicity : ℕ) :
    ByteChip.OrByte.Inputs (ZMod p) :=
  ⟨row.preprocessed[0], row.preprocessed[1], (multiplicity : ZMod p)⟩

/-- Decode one exact Byte row for the native bitwise-XOR provider. -/
def byteXorInput (row : CoreAIR.Current.Row p .byteLookup) (multiplicity : ℕ) :
    ByteChip.XorByte.Inputs (ZMod p) :=
  ⟨row.preprocessed[0], row.preprocessed[1], (multiplicity : ZMod p)⟩

/-- Decode one exact Byte row for the native unsigned-less-than provider. -/
def byteLtuInput (row : CoreAIR.Current.Row p .byteLookup) (multiplicity : ℕ) :
    ByteChip.Ltu.Inputs (ZMod p) :=
  ⟨row.preprocessed[0], row.preprocessed[1], (multiplicity : ZMod p)⟩

/-- Decode the value and multiplicity of one exact Range row.  Its width selects the destination
native table and is therefore not duplicated as an input cell. -/
def rangeProviderInput (row : CoreAIR.Current.Row p .rangeLookup) (multiplicity : ℕ) :
    RangeChip.Inputs (ZMod p) :=
  ⟨row.preprocessed[0], (multiplicity : ZMod p)⟩

/-- Exact Range rows whose committed width cell has the selected native width. -/
def rangeRowsAt (width : RangeChip.Width)
    (rows : List (CoreAIR.Current.Row p .rangeLookup)) :
    List (CoreAIR.Current.Row p .rangeLookup) :=
  rows.filter fun row => decide (row.preprocessed[1].val = width.val)

/-! ## Exact provider-access vocabulary -/

/-- The exact Byte table's AND receive, projected to the common access vocabulary. -/
def exactByteAndAccess (row : CoreAIR.Current.Row p .byteLookup) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.receive, .byte 0 row.preprocessed[2] row.preprocessed[0] row.preprocessed[1],
      row.main.values[0]⟩)

/-- The exact Byte table's OR receive. -/
def exactByteOrAccess (row : CoreAIR.Current.Row p .byteLookup) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.receive, .byte 1 row.preprocessed[3] row.preprocessed[0] row.preprocessed[1],
      row.main.values[1]⟩)

/-- The exact Byte table's XOR receive. -/
def exactByteXorAccess (row : CoreAIR.Current.Row p .byteLookup) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.receive, .byte 2 row.preprocessed[4] row.preprocessed[0] row.preprocessed[1],
      row.main.values[2]⟩)

/-- The exact Byte table's paired-u8 receive. -/
def exactByteU8RangeAccess (row : CoreAIR.Current.Row p .byteLookup) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.receive, .byte 3 0 row.preprocessed[0] row.preprocessed[1], row.main.values[3]⟩)

/-- The exact Byte table's unsigned-comparison receive. -/
def exactByteLtuAccess (row : CoreAIR.Current.Row p .byteLookup) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.receive, .byte 4 row.preprocessed[5] row.preprocessed[0] row.preprocessed[1],
      row.main.values[4]⟩)

/-- The exact Byte table's high-bit receive. -/
def exactByteMsbAccess (row : CoreAIR.Current.Row p .byteLookup) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.receive, .byte 5 row.preprocessed[6] row.preprocessed[0] 0, row.main.values[5]⟩)

/-- The exact Range table's single receive. -/
def exactRangeAccess (row : CoreAIR.Current.Row p .rangeLookup) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.receive, .byte 6 row.preprocessed[0] row.preprocessed[1] 0, row.main.values[0]⟩)

/-- The exact Program table's single receive. -/
def exactProgramAccess (row : CoreAIR.Current.Row p .program) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.receive,
      .program row.preprocessed[0] row.preprocessed[1] row.preprocessed[2]
        (Opcode.ofNat row.preprocessed[3]) row.preprocessed[4]
        row.preprocessed[5] row.preprocessed[6] row.preprocessed[7] row.preprocessed[8]
        row.preprocessed[9] row.preprocessed[10] row.preprocessed[11] row.preprocessed[12]
        row.preprocessed[13] row.preprocessed[14] row.preprocessed[15],
      row.main.values[0]⟩)

/-! The declarations above are an audit view of the extracted source interactions, including
their source main-column multiplicities.  Native provider construction below uses only their
`keyOf` projections.  In particular, no theorem identifies those source multiplicities with a
native provider output. -/

/-- Source Byte-AND key; `keyOf` deliberately erases the exact main-column count. -/
def sourceByteAndKey (row : CoreAIR.Current.Row p .byteLookup) : LookupKey :=
  LookupAccessList.keyOf (exactByteAndAccess row)

/-- Source Byte-OR key. -/
def sourceByteOrKey (row : CoreAIR.Current.Row p .byteLookup) : LookupKey :=
  LookupAccessList.keyOf (exactByteOrAccess row)

/-- Source Byte-XOR key. -/
def sourceByteXorKey (row : CoreAIR.Current.Row p .byteLookup) : LookupKey :=
  LookupAccessList.keyOf (exactByteXorAccess row)

/-- Source paired-u8 key. -/
def sourceByteU8RangeKey (row : CoreAIR.Current.Row p .byteLookup) : LookupKey :=
  LookupAccessList.keyOf (exactByteU8RangeAccess row)

/-- Source Byte-LTU key. -/
def sourceByteLtuKey (row : CoreAIR.Current.Row p .byteLookup) : LookupKey :=
  LookupAccessList.keyOf (exactByteLtuAccess row)

/-- Source Byte-MSB key. -/
def sourceByteMsbKey (row : CoreAIR.Current.Row p .byteLookup) : LookupKey :=
  LookupAccessList.keyOf (exactByteMsbAccess row)

/-- Source fixed-width Range key. -/
def sourceRangeKey (row : CoreAIR.Current.Row p .rangeLookup) : LookupKey :=
  LookupAccessList.keyOf (exactRangeAccess row)

/-- Source Program-ROM key. -/
def sourceProgramKey (row : CoreAIR.Current.Row p .program) : LookupKey :=
  LookupAccessList.keyOf (exactProgramAccess row)

/-! `providerRecount` — the native-consumer occurrence count for one inventory-selected provider
key — is `LookupAccessList.providerRecount` (`Model/InteractionBus.lean`), *exported* into this
namespace rather than redefined here: the completeness-side provider closure recounts against the
same function, and the two layers must not drift into definitionally-equal-but-separate copies.

An `export` and not an `abbrev`: an `abbrev` is reducible, so it unfolds before the `rw`/`simp`
steps below can match on the name, and the recount rewrites in this file stop firing. -/
export LookupAccessList (providerRecount)

/-- The canonical field multiplicity installed in a native provider row. -/
def providerRecountField (skeleton : LookupAccessList) (key : LookupKey) : ZMod p :=
  (providerRecount skeleton key : ZMod p)

/-- The access emitted by a constructed provider row before the centered field count is decoded
back to its intended integer. -/
def recountedProviderFieldAccess (skeleton : LookupAccessList) (key : LookupKey) : LookupAccess :=
  (key.1, key.2.1, key.2.2,
    signedVal (providerRecountField (p := p) skeleton key))

/-- A provider access with a source key and the integer count reconstructed from native
consumers.  This is the target ledger, not an exact-source main-column access. -/
def recountedProviderAccess (skeleton : LookupAccessList) (key : LookupKey) : LookupAccess :=
  (key.1, key.2.1, key.2.2, (providerRecount skeleton key : ℤ))

/-- Keep the first row at each projected provider key and discard later rows with that same key.
The comparison is on the actual `LookupKey`, not the wider exact source row: this is load-bearing
for the MSB block (which forgets the source `c` operand), Range `(a,bits)` duplicates, and repeated
Program padding.  This list-based definition is intentionally only a declarative specification and
small-regression helper: it is quadratic and is not called by the real witness construction. -/
def freshRowsByKey {Row : Type} (seen : List LookupKey) (keyOf : Row → LookupKey) :
    List Row → List Row
  | [] => []
  | row :: rows =>
      if keyOf row ∈ seen then freshRowsByKey seen keyOf rows
      else row :: freshRowsByKey (keyOf row :: seen) keyOf rows

/-- Canonicalization never invents a source row. -/
theorem freshRowsByKey_subset {Row : Type} (seen : List LookupKey)
    (keyOf : Row → LookupKey) (rows : List Row) :
    freshRowsByKey seen keyOf rows ⊆ rows := by
  induction rows generalizing seen with
  | nil => simp [freshRowsByKey]
  | cons row rows ih =>
    simp only [freshRowsByKey]
    split
    · intro candidate candidateMem
      exact List.mem_cons_of_mem row (ih seen candidateMem)
    · intro candidate candidateMem
      simp only [List.mem_cons] at candidateMem ⊢
      rcases candidateMem with rfl | candidateMem
      · exact Or.inl rfl
      · exact Or.inr (ih (keyOf row :: seen) candidateMem)

/-- Every retained key is fresh relative to the caller's prior inventory. -/
theorem freshRowsByKey_key_not_mem_seen {Row : Type} (seen : List LookupKey)
    (keyOf : Row → LookupKey) (rows : List Row) :
    ∀ row ∈ freshRowsByKey seen keyOf rows, keyOf row ∉ seen := by
  induction rows generalizing seen with
  | nil => simp [freshRowsByKey]
  | cons row rows ih =>
    simp only [freshRowsByKey]
    split <;> rename_i fresh
    · exact ih seen
    · intro candidate candidateMem
      simp only [List.mem_cons] at candidateMem
      rcases candidateMem with rfl | candidateMem
      · exact fresh
      · exact fun candidateSeen =>
          ih (keyOf row :: seen) candidate candidateMem (by simp [candidateSeen])

/-- The projected keys of canonical rows are duplicate-free, with no premise on the raw rows. -/
theorem freshRowsByKey_keys_nodup {Row : Type} (seen : List LookupKey)
    (keyOf : Row → LookupKey) (rows : List Row) :
    ((freshRowsByKey seen keyOf rows).map keyOf).Nodup := by
  induction rows generalizing seen with
  | nil => simp [freshRowsByKey]
  | cons row rows ih =>
    simp only [freshRowsByKey]
    split
    · exact ih seen
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih (keyOf row :: seen)⟩
      intro keyMem
      obtain ⟨candidate, candidateMem, candidateKey⟩ := List.mem_map.mp keyMem
      exact freshRowsByKey_key_not_mem_seen (keyOf row :: seen) keyOf rows
        candidate candidateMem (by simp [candidateKey])

/-- Canonical keys are membership-equivalent to raw keys not already present in `seen`. -/
theorem mem_map_freshRowsByKey_iff {Row : Type} (seen : List LookupKey)
    (keyOf : Row → LookupKey) (rows : List Row) (key : LookupKey) :
    key ∈ (freshRowsByKey seen keyOf rows).map keyOf ↔
      key ∈ rows.map keyOf ∧ key ∉ seen := by
  induction rows generalizing seen with
  | nil => simp [freshRowsByKey]
  | cons row rows ih =>
    simp only [freshRowsByKey]
    by_cases seenRow : keyOf row ∈ seen
    · rw [if_pos seenRow, ih seen]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro ⟨tailMem, keyFresh⟩
        exact ⟨Or.inr tailMem, keyFresh⟩
      · rintro ⟨headEq | tailMem, keyFresh⟩
        · subst key; exact absurd seenRow keyFresh
        · exact ⟨tailMem, keyFresh⟩
    · rw [if_neg seenRow]
      simp only [List.map_cons, List.mem_cons, ih (keyOf row :: seen)]
      constructor
      · rintro (rfl | ⟨tailMem, keyFresh⟩)
        · exact ⟨Or.inl rfl, seenRow⟩
        · exact ⟨Or.inr tailMem, fun keySeen => keyFresh (by simp [keySeen])⟩
      · rintro ⟨headEq | tailMem, keyFresh⟩
        · exact Or.inl headEq
        · by_cases keyEq : key = keyOf row
          · exact Or.inl keyEq
          · exact Or.inr ⟨tailMem, by simp [keyEq, keyFresh]⟩

/-- Minimal regression: two raw occurrences of one projected key retain exactly one row. -/
theorem freshRowsByKey_duplicate {Row : Type} (keyOf : Row → LookupKey) (row : Row) :
    freshRowsByKey [] keyOf [row, row] = [row] := by
  simp [freshRowsByKey]

/-- The corresponding ledger regression: two raw occurrences of one key install exactly one full
native-consumer recount, never two copies of that count.  This is a specification-level test for
canonicalization; the real witness path consumes an explicit linear-size inventory instead. -/
theorem freshRowsByKey_duplicate_recount {Row : Type} (keyOf : Row → LookupKey)
    (skeleton : LookupAccessList) (row : Row) :
    (freshRowsByKey [] keyOf [row, row]).map
        (fun retained => recountedProviderAccess skeleton (keyOf retained)) =
      [recountedProviderAccess skeleton (keyOf row)] := by
  rw [freshRowsByKey_duplicate]
  rfl

omit [Fact (2 ^ 24 < p)] in
/-- MSB regression: rows differing in source cells that the MSB key does not retain still populate
only one native row when their projected MSB keys coincide. -/
theorem freshMsbRows_duplicateKey
    (first second : CoreAIR.Current.Row p .byteLookup)
    (sameKey : sourceByteMsbKey second = sourceByteMsbKey first) :
    freshRowsByKey [] sourceByteMsbKey [first, second] = [first] := by
  simp [freshRowsByKey, sameKey]

omit [Fact (2 ^ 24 < p)] in
/-- Range regression, covering the repeated canonical `(a = 0, bits = 0)` shape. -/
theorem freshRangeRows_duplicateKey
    (first second : CoreAIR.Current.Row p .rangeLookup)
    (sameKey : sourceRangeKey second = sourceRangeKey first) :
    freshRowsByKey [] sourceRangeKey [first, second] = [first] := by
  simp [freshRowsByKey, sameKey]

omit [Fact (2 ^ 24 < p)] in
/-- Program regression: repeated padding rows with the same instruction key supply one recount. -/
theorem freshProgramRows_duplicateKey
    (first second : CoreAIR.Current.Row p .program)
    (sameKey : sourceProgramKey second = sourceProgramKey first) :
    freshRowsByKey [] sourceProgramKey [first, second] = [first] := by
  simp [freshRowsByKey, sameKey]

/-- A typed carrier records which native provider block a selected source row populates. -/
inductive PreprocessedSourceRow (p : ℕ) [Fact p.Prime] where
  | byteU8Range (row : CoreAIR.Current.Row p .byteLookup)
  | byteMsb (row : CoreAIR.Current.Row p .byteLookup)
  | byteAnd (row : CoreAIR.Current.Row p .byteLookup)
  | byteOr (row : CoreAIR.Current.Row p .byteLookup)
  | byteXor (row : CoreAIR.Current.Row p .byteLookup)
  | byteLtu (row : CoreAIR.Current.Row p .byteLookup)
  | range (width : RangeChip.Width) (row : CoreAIR.Current.Row p .rangeLookup)
  | program (row : CoreAIR.Current.Row p .program)

namespace PreprocessedSourceRow

/-- Project a typed carrier to the exact key emitted by its destination native provider. -/
def key : PreprocessedSourceRow p → LookupKey
  | .byteU8Range row => sourceByteU8RangeKey row
  | .byteMsb row => sourceByteMsbKey row
  | .byteAnd row => sourceByteAndKey row
  | .byteOr row => sourceByteOrKey row
  | .byteXor row => sourceByteXorKey row
  | .byteLtu row => sourceByteLtuKey row
  | .range _ row => sourceRangeKey row
  | .program row => sourceProgramKey row

end PreprocessedSourceRow

/-- Assemble already-partitioned representatives into one typed, auditable inventory view.  This
is a linear concatenation in native table order; it performs no key comparisons or source scan. -/
def canonicalPreprocessedInventoryRows
    (byteU8RangeRows byteMsbRows byteAndRows byteOrRows byteXorRows byteLtuRows :
      List (CoreAIR.Current.Row p .byteLookup))
    (rangeRows : RangeChip.Width → List (CoreAIR.Current.Row p .rangeLookup))
    (programRows : List (CoreAIR.Current.Row p .program)) :
    List (PreprocessedSourceRow p) :=
  byteU8RangeRows.map .byteU8Range ++
    byteMsbRows.map .byteMsb ++
    byteAndRows.map .byteAnd ++
    byteOrRows.map .byteOr ++
    byteXorRows.map .byteXor ++
    byteLtuRows.map .byteLtu ++
    (RangeChip.allWidths.flatMap fun width =>
      (rangeRows width).map (.range width)) ++
    programRows.map .program

/-- An efficient, demand-oriented inventory of source-backed provider representatives.

The integration/export layer supplies the lists already partitioned by their destination native
tables.  It need not enumerate the enormous raw preprocessing universe: the recount contract below
separately requires representatives for every *nonzero* native skeleton demand.  Each list is
source-backed by its matching exact matrix (and Range width), and global projected-key uniqueness is
stated on the concatenated typed view.  This is the linear-size construction boundary;
`freshRowsByKey` above remains a declarative specification and small-regression tool. -/
structure CanonicalPreprocessedInventory
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) where
  byteU8RangeRows : List (CoreAIR.Current.Row p .byteLookup)
  byteMsbRows : List (CoreAIR.Current.Row p .byteLookup)
  byteAndRows : List (CoreAIR.Current.Row p .byteLookup)
  byteOrRows : List (CoreAIR.Current.Row p .byteLookup)
  byteXorRows : List (CoreAIR.Current.Row p .byteLookup)
  byteLtuRows : List (CoreAIR.Current.Row p .byteLookup)
  rangeRows : RangeChip.Width → List (CoreAIR.Current.Row p .rangeLookup)
  programRows : List (CoreAIR.Current.Row p .program)
  byteU8RangeSource : byteU8RangeRows ⊆ witness.trace.rows .byteLookup
  byteMsbSource : byteMsbRows ⊆ witness.trace.rows .byteLookup
  byteAndSource : byteAndRows ⊆ witness.trace.rows .byteLookup
  byteOrSource : byteOrRows ⊆ witness.trace.rows .byteLookup
  byteXorSource : byteXorRows ⊆ witness.trace.rows .byteLookup
  byteLtuSource : byteLtuRows ⊆ witness.trace.rows .byteLookup
  /-- Range source-backedness is block-aware: the source width equals the destination width. -/
  rangeSource : ∀ width, rangeRows width ⊆
    rangeRowsAt width (witness.trace.rows .rangeLookup)
  programSource : programRows ⊆ witness.trace.rows .program
  /-- Exactly one representative is supplied for each projected key in the whole inventory. -/
  projectedKeysNodup :
    ((canonicalPreprocessedInventoryRows byteU8RangeRows byteMsbRows byteAndRows byteOrRows
      byteXorRows byteLtuRows rangeRows programRows).map
        PreprocessedSourceRow.key).Nodup

namespace CanonicalPreprocessedInventory

/-- The whole typed inventory in native table order. -/
def rows {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :
    List (PreprocessedSourceRow p) :=
  canonicalPreprocessedInventoryRows inventory.byteU8RangeRows inventory.byteMsbRows
    inventory.byteAndRows inventory.byteOrRows inventory.byteXorRows inventory.byteLtuRows
    inventory.rangeRows inventory.programRows

end CanonicalPreprocessedInventory

/-! These projections preserve the original construction API while exposing the exporter's direct
per-block lists.  No filter or deduplication runs while constructing the witness. -/

def canonicalByteU8RangeRows
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :=
  inventory.byteU8RangeRows

def canonicalByteMsbRows
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :=
  inventory.byteMsbRows

def canonicalByteAndRows
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :=
  inventory.byteAndRows

def canonicalByteOrRows
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :=
  inventory.byteOrRows

def canonicalByteXorRows
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :=
  inventory.byteXorRows

def canonicalByteLtuRows
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :=
  inventory.byteLtuRows

def canonicalRangeRows (width : RangeChip.Width)
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :=
  inventory.rangeRows width

def canonicalProgramRows
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :=
  inventory.programRows

/-- Canonical keys in the actual native table order. -/
def inventoryPreprocessedKeys
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) : List LookupKey :=
  (canonicalByteU8RangeRows inventory).map sourceByteU8RangeKey ++
    (canonicalByteMsbRows inventory).map sourceByteMsbKey ++
    (canonicalByteAndRows inventory).map sourceByteAndKey ++
    (canonicalByteOrRows inventory).map sourceByteOrKey ++
    (canonicalByteXorRows inventory).map sourceByteXorKey ++
    (canonicalByteLtuRows inventory).map sourceByteLtuKey ++
    (RangeChip.allWidths.flatMap fun width =>
      (canonicalRangeRows width inventory).map sourceRangeKey) ++
    (canonicalProgramRows inventory).map sourceProgramKey

omit [Fact (2 ^ 24 < p)] in
/-- The projected native-table key list is exactly the key image of the whole typed inventory.
This is the auditable bridge showing that construction consumes the global `Nodup` field. -/
theorem inventoryPreprocessedKeys_eq_inventoryRows
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :
    inventoryPreprocessedKeys inventory =
      inventory.rows.map PreprocessedSourceRow.key := by
  simp only [inventoryPreprocessedKeys, CanonicalPreprocessedInventory.rows,
    canonicalPreprocessedInventoryRows, canonicalByteU8RangeRows, canonicalByteMsbRows,
    canonicalByteAndRows, canonicalByteOrRows, canonicalByteXorRows,
    canonicalByteLtuRows, canonicalRangeRows, canonicalProgramRows,
    List.map_append, List.map_map, List.map_flatMap, Function.comp_def,
    PreprocessedSourceRow.key]

omit [Fact (2 ^ 24 < p)] in
/-- Canonical key uniqueness follows from the explicit inventory contract, never from raw
preprocessing-row uniqueness (which is false for MSB, Range, and Program padding). -/
theorem inventoryPreprocessedKeys_nodup
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness) :
    (inventoryPreprocessedKeys inventory).Nodup := by
  rw [inventoryPreprocessedKeys_eq_inventoryRows]
  exact inventory.projectedKeysNodup

omit [Fact (2 ^ 24 < p)] in
/-- Every canonical Byte-row projection came from the exact Byte preprocessing matrix. -/
theorem canonicalByteRows_mem_source
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (row : CoreAIR.Current.Row p .byteLookup)
    (rowMem : row ∈ canonicalByteU8RangeRows inventory ∨
      row ∈ canonicalByteMsbRows inventory ∨
      row ∈ canonicalByteAndRows inventory ∨
      row ∈ canonicalByteOrRows inventory ∨
      row ∈ canonicalByteXorRows inventory ∨
      row ∈ canonicalByteLtuRows inventory) :
    row ∈ witness.trace.rows .byteLookup := by
  rcases rowMem with rowMem | rowMem | rowMem | rowMem | rowMem | rowMem
  · exact inventory.byteU8RangeSource rowMem
  · exact inventory.byteMsbSource rowMem
  · exact inventory.byteAndSource rowMem
  · exact inventory.byteOrSource rowMem
  · exact inventory.byteXorSource rowMem
  · exact inventory.byteLtuSource rowMem

omit [Fact (2 ^ 24 < p)] in
/-- Every canonical Range-row projection came from the matching exact width block. -/
theorem canonicalRangeRows_mem_source (width : RangeChip.Width)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (row : CoreAIR.Current.Row p .rangeLookup)
    (rowMem : row ∈ canonicalRangeRows width inventory) :
    row ∈ rangeRowsAt width (witness.trace.rows .rangeLookup) :=
  inventory.rangeSource width rowMem

omit [Fact (2 ^ 24 < p)] in
/-- Every canonical Program row came from the exact Program preprocessing matrix. -/
theorem canonicalProgramRows_mem_source
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (row : CoreAIR.Current.Row p .program)
    (rowMem : row ∈ canonicalProgramRows inventory) :
    row ∈ witness.trace.rows .program :=
  inventory.programSource rowMem

/-- The complete integer provider ledger obtained by recounting the non-preprocessed native
skeleton at every inventory key. -/
def recountedPreprocessedProviderAccesses
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList) : LookupAccessList :=
  (inventoryPreprocessedKeys inventory).map (recountedProviderAccess skeleton)

/-- The three exact preprocessed provider ledgers, in a convenient Byte/Range/Program order.  This
is a reordering of the corresponding row blocks of `CoreAIR.Current.allInteractions`, not a new
interpretation of them. -/
def exactPreprocessedProviderAccesses
    (publicValues : SP1PublicValues (ZMod p))
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) : LookupAccessList :=
  ((witness.trace.rows .byteLookup).flatMap fun row =>
      (CoreAIR.Current.interactions publicValues .byteLookup row).map
        Extracted.Interaction.toAccess) ++
    ((witness.trace.rows .rangeLookup).flatMap fun row =>
      (CoreAIR.Current.interactions publicValues .rangeLookup row).map
        Extracted.Interaction.toAccess) ++
    ((witness.trace.rows .program).flatMap fun row =>
      (CoreAIR.Current.interactions publicValues .program row).map
        Extracted.Interaction.toAccess)

omit [Fact (2 ^ 24 < p)] in
/-- The generated Byte oracle contains exactly the six named receives, in Rust order. -/
theorem exactByteRowAccesses
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .byteLookup) :
    (CoreAIR.Current.interactions publicValues .byteLookup row).map
        Extracted.Interaction.toAccess =
      [exactByteAndAccess row, exactByteOrAccess row, exactByteXorAccess row,
       exactByteU8RangeAccess row, exactByteLtuAccess row, exactByteMsbAccess row] := by
  rw [CoreAIR.Current.interactions, Extracted.ByteCols.interactions]
  rfl

omit [Fact (2 ^ 24 < p)] in
/-- The generated Range oracle contains exactly its named receive. -/
theorem exactRangeRowAccesses
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .rangeLookup) :
    (CoreAIR.Current.interactions publicValues .rangeLookup row).map
        Extracted.Interaction.toAccess = [exactRangeAccess row] := by
  rw [CoreAIR.Current.interactions, Extracted.RangeCols.interactions]
  rfl

omit [Fact (2 ^ 24 < p)] in
/-- The generated Program oracle contains exactly its named receive. -/
theorem exactProgramRowAccesses
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .program) :
    (CoreAIR.Current.interactions publicValues .program row).map
        Extracted.Interaction.toAccess = [exactProgramAccess row] := by
  rw [CoreAIR.Current.interactions, Extracted.ProgramCols.interactions]
  rfl

/-! ## The per-row preprocessing contract -/

/-- The local semantic content needed to reconstruct constraint-satisfying native provider rows.

The six Byte fields say exactly that each present preprocessed result is the canonical byte-table
result.  The Program field is the typed native `RowSpec`.  Range validity is stated at the width
stored in the row.  All fields quantify only over rows present in this witness: this structure
does not assert coverage of a canonical matrix, constrain unused source Range rows to the native
width profile, or bind the Program rows to a `GuestProgram`.  The block-aware inventory selects
only widths represented by `RangeChip.Width`. -/
structure PreprocessedProviderContract
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) : Prop where
  byteAnd : ∀ row ∈ witness.trace.rows .byteLookup,
    ByteRowSpec ⟨0, row.preprocessed[2], row.preprocessed[0], row.preprocessed[1]⟩
  byteOr : ∀ row ∈ witness.trace.rows .byteLookup,
    ByteRowSpec ⟨1, row.preprocessed[3], row.preprocessed[0], row.preprocessed[1]⟩
  byteXor : ∀ row ∈ witness.trace.rows .byteLookup,
    ByteRowSpec ⟨2, row.preprocessed[4], row.preprocessed[0], row.preprocessed[1]⟩
  byteU8Range : ∀ row ∈ witness.trace.rows .byteLookup,
    ByteRowSpec ⟨3, 0, row.preprocessed[0], row.preprocessed[1]⟩
  byteLtu : ∀ row ∈ witness.trace.rows .byteLookup,
    ByteRowSpec ⟨4, row.preprocessed[5], row.preprocessed[0], row.preprocessed[1]⟩
  byteMsb : ∀ row ∈ witness.trace.rows .byteLookup,
    ByteRowSpec ⟨5, row.preprocessed[6], row.preprocessed[0], 0⟩
  rangeValid : ∀ row ∈ witness.trace.rows .rangeLookup,
    row.preprocessed[0].val < 2 ^ row.preprocessed[1].val
  program : ∀ row ∈ witness.trace.rows .program,
    ProgramMsg.RowSpec (programProviderInput row 0).toMessage

namespace PreprocessedProviderContract

variable {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}

/-- Every exact Byte preprocessing row carries genuine byte operands. -/
theorem byteOperandBounds (contract : PreprocessedProviderContract witness)
    {row : CoreAIR.Current.Row p .byteLookup}
    (hrow : row ∈ witness.trace.rows .byteLookup) :
    row.preprocessed[0].val < 2 ^ 8 ∧ row.preprocessed[1].val < 2 ^ 8 :=
  (byteRowSpec_u8range_pair row.preprocessed[0] row.preprocessed[1]).mp
    (contract.byteU8Range row hrow)

omit [Fact (2 ^ 24 < p)] in
/-- A selected exact Range row satisfies the fixed-width native provider's assumption. -/
theorem rangeAt (contract : PreprocessedProviderContract witness) {width : RangeChip.Width}
    {row : CoreAIR.Current.Row p .rangeLookup}
    (hrow : row ∈ rangeRowsAt width (witness.trace.rows .rangeLookup)) :
    row.preprocessed[0].val < 2 ^ width.val := by
  obtain ⟨sourceMem, widthEq⟩ := List.mem_filter.mp hrow
  simp only [decide_eq_true_eq] at widthEq
  rw [← widthEq]
  exact contract.rangeValid row sourceMem

/-- The locally constrained AND result is the unique canonical bytewise result for its operands. -/
theorem byteAndValue (contract : PreprocessedProviderContract witness)
    {row : CoreAIR.Current.Row p .byteLookup}
    (hrow : row ∈ witness.trace.rows .byteLookup) :
    row.preprocessed[2].val = row.preprocessed[0].val &&& row.preprocessed[1].val := by
  simpa only [ZMod.val_zero, byteOp_zero] using
    ((byteRowSpec_byteOp row.preprocessed[2] row.preprocessed[0] row.preprocessed[1]
      (by rw [ZMod.val_zero]; norm_num)).mp (contract.byteAnd row hrow)).2

/-- The locally constrained OR result is the unique canonical bytewise result for its operands. -/
theorem byteOrValue (contract : PreprocessedProviderContract witness)
    {row : CoreAIR.Current.Row p .byteLookup}
    (hrow : row ∈ witness.trace.rows .byteLookup) :
    row.preprocessed[3].val = row.preprocessed[0].val ||| row.preprocessed[1].val := by
  simpa only [ZMod.val_one, byteOp_one] using
    ((byteRowSpec_byteOp row.preprocessed[3] row.preprocessed[0] row.preprocessed[1]
      (by rw [ZMod.val_one]; norm_num)).mp (contract.byteOr row hrow)).2

/-- The locally constrained XOR result is the unique canonical bytewise result for its operands. -/
theorem byteXorValue (contract : PreprocessedProviderContract witness)
    {row : CoreAIR.Current.Row p .byteLookup}
    (hrow : row ∈ witness.trace.rows .byteLookup) :
    row.preprocessed[4].val = row.preprocessed[0].val ^^^ row.preprocessed[1].val := by
  simpa only [val_2_zmod_p, byteOp_two] using
    ((byteRowSpec_byteOp row.preprocessed[4] row.preprocessed[0] row.preprocessed[1]
      (by rw [val_2_zmod_p]; norm_num)).mp (contract.byteXor row hrow)).2

/-- The locally constrained MSB result is the canonical boolean selected by the operand's high bit. -/
theorem byteMsbValue (contract : PreprocessedProviderContract witness)
    {row : CoreAIR.Current.Row p .byteLookup}
    (hrow : row ∈ witness.trace.rows .byteLookup) :
    row.preprocessed[6] = if 128 ≤ row.preprocessed[0].val then 1 else 0 := by
  have decoded := (byteRowSpec_msb row.preprocessed[6] row.preprocessed[0]).mp
    (contract.byteMsb row hrow)
  split
  · exact decoded.2.2.mpr (by assumption)
  · rcases decoded.2.1 with zero | one
    · exact zero
    · exact absurd (decoded.2.2.mp one) (by assumption)

/-- The locally constrained LTU result is the canonical boolean selected by unsigned comparison. -/
theorem byteLtuValue (contract : PreprocessedProviderContract witness)
    {row : CoreAIR.Current.Row p .byteLookup}
    (hrow : row ∈ witness.trace.rows .byteLookup) :
    row.preprocessed[5] =
      if row.preprocessed[0].val < row.preprocessed[1].val then 1 else 0 := by
  have decoded := (byteRowSpec_ltu row.preprocessed[5] row.preprocessed[0]
    row.preprocessed[1]).mp (contract.byteLtu row hrow)
  split
  · exact decoded.2.2.mpr (by assumption)
  · rcases decoded.2.1 with zero | one
    · exact zero
    · exact absurd (decoded.2.2.mp one) (by assumption)

end PreprocessedProviderContract

/-! ## Explicit native recount obligations -/

/-- Keys supplied by the preprocessing providers.  Range is carried on the Byte channel, so the
two relevant interaction kinds are exactly Byte and Program.  This deliberately quantifies over
*every* key of either kind, not merely keys whose table names are `SP1Byte`/`SP1Program`: it is a
fail-closed promise that the skeleton contains no uncovered Byte- or Program-kind demand under an
unexpected channel name. -/
def IsPreprocessedProviderKey (key : LookupKey) : Prop :=
  key.1 = .Byte ∨ key.1 = .Program

/-- The exact/global facts needed for native-consumer recounting.

The explicit `localSemantics` field supplies what each selected source preprocessing row's key
means; the exact Byte/Range/Program assertion lists do not derive it.  The three remaining fields
are deliberately global: the caller-supplied, source-backed once-per-key inventory
must cover every nonzero Byte/Program demand in the native skeleton, see only nonpositive skeleton
sums at provider keys, and fit each reconstructed natural count into the nonnegative half of the
field.  Canonical key uniqueness is part of the Type-valued inventory input, not assumed of the raw
matrices.  None of the remaining fields is inferred from local preprocessing assertions. -/
structure PreprocessedProviderRecountContract
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
  (skeleton : LookupAccessList) : Prop where
  /-- Per-row Byte/Range/Program meaning of the selected source preprocessing matrices. -/
  localSemantics : PreprocessedProviderContract witness
  /-- Every nonzero native Byte/Program demand has an inventory-supplied provider key. -/
  coverage : ∀ key, IsPreprocessedProviderKey key →
    LookupAccessList.multiplicitySum skeleton key ≠ 0 →
      key ∈ inventoryPreprocessedKeys inventory
  /-- Native preprocessing providers only fill deficits; they never need a negative natural
  multiplicity. -/
  nonpositive : ∀ key ∈ inventoryPreprocessedKeys inventory,
    LookupAccessList.multiplicitySum skeleton key ≤ 0
  /-- The reconstructed count has its canonical centered representative in `ZMod p`. -/
  centered : ∀ key ∈ inventoryPreprocessedKeys inventory,
    2 * providerRecount skeleton key ≤ p

namespace PreprocessedProviderRecountContract

variable {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
variable {inventory : CanonicalPreprocessedInventory witness}
variable {skeleton : LookupAccessList}

omit [Fact (2 ^ 24 < p)] in
/-- Under the explicit sign premise, `Int.toNat` recovers the additive inverse of the skeleton
sum exactly. -/
theorem recount_eq_neg
    (contract : PreprocessedProviderRecountContract witness inventory skeleton)
    {key : LookupKey} (keyMem : key ∈ inventoryPreprocessedKeys inventory) :
    (providerRecount skeleton key : ℤ) =
      -LookupAccessList.multiplicitySum skeleton key := by
  rw [providerRecount, Int.toNat_of_nonneg]
  exact neg_nonneg.mpr (contract.nonpositive key keyMem)

omit [Fact (2 ^ 24 < p)] in
/-- The field cell installed in a provider row projects back to the exact natural recount. -/
theorem signedVal_providerRecountField
    (contract : PreprocessedProviderRecountContract witness inventory skeleton)
    {key : LookupKey} (keyMem : key ∈ inventoryPreprocessedKeys inventory) :
    signedVal (providerRecountField (p := p) skeleton key) =
      (providerRecount skeleton key : ℤ) := by
  exact signedVal_natCast_of_twice_le _ (contract.centered key keyMem)

omit [Fact (2 ^ 24 < p)] in
/-- The literal Clean access emitted by a recounted provider row is the intended integer ledger
entry once the explicit centered-representative obligation is supplied. -/
theorem fieldAccess_eq_recounted
    (contract : PreprocessedProviderRecountContract witness inventory skeleton)
    {key : LookupKey} (keyMem : key ∈ inventoryPreprocessedKeys inventory) :
    recountedProviderFieldAccess (p := p) skeleton key =
      recountedProviderAccess skeleton key := by
  simp only [recountedProviderFieldAccess, recountedProviderAccess]
  rw [contract.signedVal_providerRecountField keyMem]

end PreprocessedProviderRecountContract

/-! ## Constructed native tables -/

variable {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
variable {inventory : CanonicalPreprocessedInventory witness}
variable {skeleton : LookupAccessList}
variable {data : ProverData (ZMod p)} {hint : ProverHint (ZMod p)}

/-- Redistribute exact Byte rows into the native u8-range provider. -/
def transportU8RangeTable (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build (⟨ByteChip.U8Range.circuit⟩ : Component (ZMod p))
    ((canonicalByteU8RangeRows inventory).map fun row =>
      byteU8RangeInput row (providerRecount skeleton (sourceByteU8RangeKey row))) data hint

/-- Redistribute exact Byte rows into the native most-significant-bit provider. -/
def transportMsbTable (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build (⟨ByteChip.MSB.circuit⟩ : Component (ZMod p))
    ((canonicalByteMsbRows inventory).map fun row =>
      byteMsbInput row (providerRecount skeleton (sourceByteMsbKey row))) data hint

/-- Redistribute exact Byte rows into the native bitwise-AND provider. -/
def transportAndTable (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build (⟨ByteChip.AndByte.circuit⟩ : Component (ZMod p))
    ((canonicalByteAndRows inventory).map fun row =>
      byteAndInput row (providerRecount skeleton (sourceByteAndKey row))) data hint

/-- Redistribute exact Byte rows into the native bitwise-OR provider. -/
def transportOrTable (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build (⟨ByteChip.OrByte.circuit⟩ : Component (ZMod p))
    ((canonicalByteOrRows inventory).map fun row =>
      byteOrInput row (providerRecount skeleton (sourceByteOrKey row))) data hint

/-- Redistribute exact Byte rows into the native bitwise-XOR provider. -/
def transportXorTable (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build (⟨ByteChip.XorByte.circuit⟩ : Component (ZMod p))
    ((canonicalByteXorRows inventory).map fun row =>
      byteXorInput row (providerRecount skeleton (sourceByteXorKey row))) data hint

/-- Redistribute exact Byte rows into the native unsigned-less-than provider. -/
def transportLtuTable (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build (⟨ByteChip.Ltu.circuit⟩ : Component (ZMod p))
    ((canonicalByteLtuRows inventory).map fun row =>
      byteLtuInput row (providerRecount skeleton (sourceByteLtuKey row))) data hint

/-- One fixed-width native Range table, populated by exactly the matching upstream rows. -/
def transportRangeTable (width : RangeChip.Width)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build (⟨RangeChip.circuitFor width⟩ : Component (ZMod p))
    ((canonicalRangeRows width inventory).map fun row =>
      rangeProviderInput row (providerRecount skeleton (sourceRangeKey row))) data hint

/-- Redistribute exact Program rows into the native program-ROM provider. -/
def transportProgramTable (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build (⟨ProgramProviderChip.circuit⟩ : Component (ZMod p))
    ((canonicalProgramRows inventory).map fun row =>
      programProviderInput row (providerRecount skeleton (sourceProgramKey row))) data hint

omit [Fact (2 ^ 24 < p)] in
private theorem byteInputs_assumptions
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (rows : List (CoreAIR.Current.Row p .byteLookup))
    (decode : CoreAIR.Current.Row p .byteLookup → Input (ZMod p))
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (prove : ∀ row ∈ rows,
      circuit.ProverAssumptions (decode row) data hint) :
    ∀ input ∈ rows.map decode,
      circuit.ProverAssumptions input data hint := by
  intro input hinput
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hinput
  exact prove row hrow

theorem transportU8RangeTable_constraints
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (transportU8RangeTable witness inventory skeleton data hint).Constraints := by
  apply Table.build_constraints _ _ _ _ ByteChip.U8Range.computableWitnesses
  exact byteInputs_assumptions
    (canonicalByteU8RangeRows inventory)
    (fun row => byteU8RangeInput row
      (providerRecount skeleton (sourceByteU8RangeKey row))) ByteChip.U8Range.circuit
    (fun row hrow => contract.byteOperandBounds
      (canonicalByteRows_mem_source witness inventory row (Or.inl hrow)))

theorem transportMsbTable_constraints
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (transportMsbTable witness inventory skeleton data hint).Constraints := by
  apply Table.build_constraints _ _ _ _ ByteChip.MSB.computableWitnesses
  exact byteInputs_assumptions
    (canonicalByteMsbRows inventory)
    (fun row => byteMsbInput row
      (providerRecount skeleton (sourceByteMsbKey row))) ByteChip.MSB.circuit
    (fun row hrow => (contract.byteOperandBounds
      (canonicalByteRows_mem_source witness inventory row (Or.inr (Or.inl hrow)))).1)

theorem transportAndTable_constraints
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (transportAndTable witness inventory skeleton data hint).Constraints := by
  apply Table.build_constraints _ _ _ _ ByteChip.AndByte.computableWitnesses
  exact byteInputs_assumptions
    (canonicalByteAndRows inventory)
    (fun row => byteAndInput row
      (providerRecount skeleton (sourceByteAndKey row))) ByteChip.AndByte.circuit
    (fun row hrow => contract.byteOperandBounds
      (canonicalByteRows_mem_source witness inventory row (Or.inr (Or.inr (Or.inl hrow)))))

theorem transportOrTable_constraints
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (transportOrTable witness inventory skeleton data hint).Constraints := by
  apply Table.build_constraints _ _ _ _ ByteChip.OrByte.computableWitnesses
  exact byteInputs_assumptions
    (canonicalByteOrRows inventory)
    (fun row => byteOrInput row
      (providerRecount skeleton (sourceByteOrKey row))) ByteChip.OrByte.circuit
    (fun row hrow => contract.byteOperandBounds
      (canonicalByteRows_mem_source witness inventory row
        (Or.inr (Or.inr (Or.inr (Or.inl hrow))))))

theorem transportXorTable_constraints
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (transportXorTable witness inventory skeleton data hint).Constraints := by
  apply Table.build_constraints _ _ _ _ ByteChip.XorByte.computableWitnesses
  exact byteInputs_assumptions
    (canonicalByteXorRows inventory)
    (fun row => byteXorInput row
      (providerRecount skeleton (sourceByteXorKey row))) ByteChip.XorByte.circuit
    (fun row hrow => contract.byteOperandBounds
      (canonicalByteRows_mem_source witness inventory row
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hrow)))))))

theorem transportLtuTable_constraints
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (transportLtuTable witness inventory skeleton data hint).Constraints := by
  apply Table.build_constraints _ _ _ _ ByteChip.Ltu.computableWitnesses
  exact byteInputs_assumptions
    (canonicalByteLtuRows inventory)
    (fun row => byteLtuInput row
      (providerRecount skeleton (sourceByteLtuKey row))) ByteChip.Ltu.circuit
    (fun row hrow => contract.byteOperandBounds
      (canonicalByteRows_mem_source witness inventory row
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrow)))))))

theorem transportRangeTable_constraints (width : RangeChip.Width)
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (transportRangeTable width witness inventory skeleton data hint).Constraints := by
  apply Table.build_constraints _ _ _ _ (RangeChip.computableWitnessesFor width)
  intro input hinput
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hinput
  exact contract.rangeAt (canonicalRangeRows_mem_source width witness inventory row hrow)

theorem transportProgramTable_constraints
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (transportProgramTable witness inventory skeleton data hint).Constraints := by
  apply Table.build_constraints _ _ _ _ ProgramProviderChip.computableWitnesses
  intro input hinput
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hinput
  change ProgramMsg.RowSpec
    (programProviderInput row
      (providerRecount skeleton (sourceProgramKey row))).toMessage
  simpa only [programProviderInput, ProgramProviderChip.Inputs.toMessage] using
    contract.program row (canonicalProgramRows_mem_source witness inventory row hrow)

/-! ## The complete 24-table preprocessing segment -/

/-- The six Byte providers, all seventeen fixed-width Range providers, and Program, populated
with inventory-selected source keys and native-consumer recounts. -/
def extractedPreprocessedProviderTables
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : List (Table (ZMod p)) :=
  [ transportU8RangeTable witness inventory skeleton data hint,
    transportMsbTable witness inventory skeleton data hint,
    transportAndTable witness inventory skeleton data hint,
    transportOrTable witness inventory skeleton data hint,
    transportXorTable witness inventory skeleton data hint,
    transportLtuTable witness inventory skeleton data hint ] ++
    (RangeChip.allWidths.map fun width =>
      transportRangeTable width witness inventory skeleton data hint) ++
    [transportProgramTable witness inventory skeleton data hint]

/-- The constructed segment is component-for-component the native provider prefix. -/
theorem extractedPreprocessedProviderTables_components
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (extractedPreprocessedProviderTables witness inventory skeleton data hint).map (·.component) =
      (Soundness.sp1ProviderTables (p := p)).take
        Soundness.preprocessedProviderTableCount := by
  simp only [extractedPreprocessedProviderTables, List.map_append, List.map_cons, List.map_nil,
    List.map_map]
  rfl

/-- Every constructed provider table uses the same committed data. -/
theorem extractedPreprocessedProviderTables_data
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ table ∈ extractedPreprocessedProviderTables witness inventory skeleton data hint,
      table.data = data := by
  intro table hmem
  simp only [extractedPreprocessedProviderTables, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hmem
  rcases hmem with preProgram | programMem
  · rcases preProgram with byteMem | rangeMem
    · rcases byteMem with h | h | h | h | h | h
      · subst table; rfl
      · subst table; rfl
      · subst table; rfl
      · subst table; rfl
      · subst table; rfl
      · subst table; rfl
    · obtain ⟨width, -, h⟩ := rangeMem
      subst table
      rfl
  · subst table
    rfl

/-- **Constructed provider-prefix validity.** Local source-row semantics discharges every
native constraint.  Multiplicity recount obligations are irrelevant to these local polynomial
constraints and are used only by the ledger theorem below. -/
theorem extractedPreprocessedProviderTables_constraints
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ table ∈ extractedPreprocessedProviderTables witness inventory skeleton data hint,
      table.Constraints := by
  intro table hmem
  simp only [extractedPreprocessedProviderTables, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hmem
  rcases hmem with preProgram | programMem
  · rcases preProgram with byteMem | rangeMem
    · rcases byteMem with h | h | h | h | h | h
      · subst table; exact transportU8RangeTable_constraints contract inventory skeleton data hint
      · subst table; exact transportMsbTable_constraints contract inventory skeleton data hint
      · subst table; exact transportAndTable_constraints contract inventory skeleton data hint
      · subst table; exact transportOrTable_constraints contract inventory skeleton data hint
      · subst table; exact transportXorTable_constraints contract inventory skeleton data hint
      · subst table; exact transportLtuTable_constraints contract inventory skeleton data hint
    · obtain ⟨width, -, h⟩ := rangeMem
      subst table
      exact transportRangeTable_constraints width contract inventory skeleton data hint
  · subst table
    exact transportProgramTable_constraints contract inventory skeleton data hint

/-! ## Access redistribution -/

omit [Fact (2 ^ 24 < p)] in
private theorem unexpectedInteractions_rowOperations_eq_nil
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (channel : RawChannel (ZMod p))
    (known : channel = Channels.stateChannel.toRaw ∨
      channel = Channels.byteChannel.toRaw ∨
      channel = Channels.memoryChannel.toRaw ∨
      channel = Channels.programChannel.toRaw)
    (only : ∀ candidate ∈ circuit.channels, candidate = channel) :
    Faithful.unexpectedInteractions
        (⟨circuit⟩ : Component (ZMod p)).rowOperations = [] := by
  unfold Faithful.unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction interactionMem
  simp only [decide_eq_true_eq]
  intro unexpected
  have interactionMem' : interaction ∈
      ((circuit.main (varFromOffset Input 0)).operations (size Input)).interactions := by
    simpa only [Air.Flat.Component.rowOperations_mk] using interactionMem
  have channelMem : interaction.channel ∈
      ((circuit.main (varFromOffset Input 0)).operations (size Input)).channels :=
    List.mem_map.mpr ⟨interaction, interactionMem', rfl⟩
  have declared := circuit.channels_subset (varFromOffset Input 0) (size Input) channelMem
  have channelEq := only interaction.channel declared
  rcases known with known | known | known | known
  · exact unexpected.1 (channelEq.trans known)
  · exact unexpected.2.1 (channelEq.trans known)
  · exact unexpected.2.2.1 (channelEq.trans known)
  · exact unexpected.2.2.2 (channelEq.trans known)

omit [Fact (2 ^ 24 < p)] in
private theorem interactionsWith_rowOperations_eq_nil_of_only
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (onlyChannel channel : RawChannel (ZMod p))
    (only : ∀ candidate ∈ circuit.channels, candidate = onlyChannel)
    (different : channel ≠ onlyChannel) :
    Operations.interactionsWith channel
        (⟨circuit⟩ : Component (ZMod p)).rowOperations = [] := by
  unfold Operations.interactionsWith
  apply List.filter_eq_nil_iff.mpr
  intro interaction interactionMem
  simp only [decide_eq_true_eq]
  intro channelEq
  have interactionMem' : interaction ∈
      ((circuit.main (varFromOffset Input 0)).operations (size Input)).interactions := by
    simpa only [Air.Flat.Component.rowOperations_mk] using interactionMem
  have channelMem : interaction.channel ∈
      ((circuit.main (varFromOffset Input 0)).operations (size Input)).channels :=
    List.mem_map.mpr ⟨interaction, interactionMem', rfl⟩
  apply different
  rw [← channelEq]
  exact only interaction.channel
    (circuit.channels_subset (varFromOffset Input 0) (size Input) channelMem)

omit [Fact (2 ^ 24 < p)] in
private theorem interactionsWith_rowOperations_eq_self_of_only
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (channel : RawChannel (ZMod p))
    (only : ∀ candidate ∈ circuit.channels, candidate = channel) :
    Operations.interactionsWith channel
        (⟨circuit⟩ : Component (ZMod p)).rowOperations =
      (⟨circuit⟩ : Component (ZMod p)).rowOperations.interactions := by
  unfold Operations.interactionsWith
  apply List.filter_eq_self.mpr
  intro interaction interactionMem
  simp only [decide_eq_true_eq]
  have channelMem : interaction.channel ∈
      ((circuit.main (varFromOffset Input 0)).operations (size Input)).channels :=
    List.mem_map.mpr ⟨interaction, interactionMem, rfl⟩
  exact only interaction.channel
    (circuit.channels_subset (varFromOffset Input 0) (size Input) channelMem)

omit [Fact (2 ^ 24 < p)] in
private theorem nativeAccesses_byteOnly
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (only : ∀ candidate ∈ circuit.channels,
      candidate = Channels.byteChannel.toRaw)
    (env : Environment (ZMod p)) :
    Faithful.nativeAccesses env
        (⟨circuit⟩ : Component (ZMod p)).rowOperations =
      ((⟨circuit⟩ : Component (ZMod p)).rowOperations.interactionsWith
        Channels.byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have stateNil := interactionsWith_rowOperations_eq_nil_of_only circuit
    Channels.byteChannel.toRaw Channels.stateChannel.toRaw only
    (of_eq_false Channels.stateChannel_eq_byteChannel_false)
  have memoryNil := interactionsWith_rowOperations_eq_nil_of_only circuit
    Channels.byteChannel.toRaw Channels.memoryChannel.toRaw only
    (of_eq_false Channels.memoryChannel_eq_byteChannel_false)
  have programNil := interactionsWith_rowOperations_eq_nil_of_only circuit
    Channels.byteChannel.toRaw Channels.programChannel.toRaw only
    (of_eq_false Channels.programChannel_eq_byteChannel_false)
  have unexpected := unexpectedInteractions_rowOperations_eq_nil circuit
    Channels.byteChannel.toRaw (Or.inr (Or.inl rfl)) only
  unfold Faithful.nativeAccesses
  rw [stateNil, memoryNil, programNil, unexpected]
  simp only [List.map_nil, List.nil_append, List.append_nil]

omit [Fact (2 ^ 24 < p)] in
private theorem nativeAccesses_programOnly
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (only : ∀ candidate ∈ circuit.channels,
      candidate = Channels.programChannel.toRaw)
    (env : Environment (ZMod p)) :
    Faithful.nativeAccesses env
        (⟨circuit⟩ : Component (ZMod p)).rowOperations =
      (((⟨circuit⟩ : Component (ZMod p)).rowOperations.interactionsWith
        Channels.programChannel.toRaw).map (AbstractInteraction.toAccess env)).map
          LookupAccessList.negMult := by
  have stateNil := interactionsWith_rowOperations_eq_nil_of_only circuit
    Channels.programChannel.toRaw Channels.stateChannel.toRaw only
    (of_eq_false Channels.stateChannel_eq_programChannel_false)
  have byteNil := interactionsWith_rowOperations_eq_nil_of_only circuit
    Channels.programChannel.toRaw Channels.byteChannel.toRaw only
    (of_eq_false Channels.byteChannel_eq_programChannel_false)
  have memoryNil := interactionsWith_rowOperations_eq_nil_of_only circuit
    Channels.programChannel.toRaw Channels.memoryChannel.toRaw only
    (of_eq_false Channels.memoryChannel_eq_programChannel_false)
  have unexpected := unexpectedInteractions_rowOperations_eq_nil circuit
    Channels.programChannel.toRaw (Or.inr (Or.inr (Or.inr rfl))) only
  unfold Faithful.nativeAccesses
  rw [stateNil, byteNil, memoryNil, unexpected]
  simp only [List.map_nil, List.nil_append, List.append_nil]

omit [Fact (2 ^ 24 < p)] in
private theorem cleanAccesses_eq_nativeAccesses_byteOnly
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (only : ∀ candidate ∈ circuit.channels,
      candidate = Channels.byteChannel.toRaw)
    (env : Environment (ZMod p)) :
    ((⟨circuit⟩ : Component (ZMod p)).operations.interactions.map
        (AbstractInteraction.toAccess env)) =
      Faithful.nativeAccesses env
        (⟨circuit⟩ : Component (ZMod p)).operations := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations circuit,
    Air.Flat.Component.interactions_eq,
    nativeAccesses_byteOnly circuit only,
    interactionsWith_rowOperations_eq_self_of_only circuit
      Channels.byteChannel.toRaw only]

omit [Fact (2 ^ 24 < p)] in
private theorem cleanAccesses_eq_nativeAccesses_programOnly
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (only : ∀ candidate ∈ circuit.channels,
      candidate = Channels.programChannel.toRaw)
    (env : Environment (ZMod p)) :
    ((⟨circuit⟩ : Component (ZMod p)).operations.interactions.map
        (AbstractInteraction.toAccess env)) =
      (Faithful.nativeAccesses env
        (⟨circuit⟩ : Component (ZMod p)).operations).map
          LookupAccessList.negMult := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations circuit,
    Air.Flat.Component.interactions_eq,
    nativeAccesses_programOnly circuit only,
    interactionsWith_rowOperations_eq_self_of_only circuit
      Channels.programChannel.toRaw only,
    LookupAccessList.map_negMult_negMult]

omit [Fact (2 ^ 24 < p)] in
private theorem rangeCheck_interactionsWith (n : ℕ) (hn : 2 ^ n < p)
    (channel : RawChannel (ZMod p)) (offset : ℕ)
    (input : Expression (ZMod p)) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit ((Gadgets.ToBits.rangeCheck n hn).toSubcircuit
          offset input) :: ops) = Operations.interactionsWith channel ops := by
  apply InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil

private theorem rangeCheck8_interactionsWith
    (channel : RawChannel (ZMod p)) (offset : ℕ)
    (input : Expression (ZMod p)) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit ((Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).toSubcircuit
          offset input) :: ops) = Operations.interactionsWith channel ops :=
  rangeCheck_interactionsWith 8 ByteChip.two_pow_eight_lt channel offset input ops

omit [Fact (2 ^ 24 < p)] in
private theorem assertBool_interactionsWith
    (channel : RawChannel (ZMod p)) (offset : ℕ)
    (input : Expression (ZMod p)) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit (assertBool.toSubcircuit offset input) :: ops) =
      Operations.interactionsWith channel ops := by
  apply InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil

private theorem range_interactionsWith_byte (width : RangeChip.Width)
    (input : Var RangeChip.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith Channels.byteChannel.toRaw
        ((RangeChip.main width.val
          (RangeChip.two_pow_lt (Nat.le_of_lt_succ width.isLt)) input).operations offset) =
      [(pushedIf (channel := Channels.byteChannel) input.multiplicity
        (⟨6, input.a, Expression.const ((width.val : ℕ) : ZMod p), 0⟩ :
          ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [RangeChip.main, Circuit.operations, Circuit.bind_def,
    assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck_interactionsWith]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm]

private theorem program_interactionsWith_program
    (input : Var ProgramProviderChip.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith Channels.programChannel.toRaw
        ((ProgramProviderChip.main input).operations offset) =
      [(pushedIf (channel := Channels.programChannel) input.multiplicity
        input.toMessage).toRaw] := by
  simp only [ProgramProviderChip.main, Circuit.operations, Circuit.bind_def,
    assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck_interactionsWith,
    assertBool_interactionsWith]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm]

private theorem and8_interactionsWith
    (channel : RawChannel (ZMod p)) (offset : ℕ)
    (input : Var Gadgets.And.And8.Inputs (ZMod p)) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit (Gadgets.And.And8.circuit.toSubcircuit offset input) :: ops) =
      Operations.interactionsWith channel ops := by
  apply InteractionRecovery.interactionsWith_formalSubcircuit_eq_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil

private theorem or8_interactionsWith
    (channel : RawChannel (ZMod p)) (offset : ℕ)
    (input : Var Gadgets.Or.Or8.Inputs (ZMod p)) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit (Gadgets.Or.Or8.circuit.toSubcircuit offset input) :: ops) =
      Operations.interactionsWith channel ops := by
  apply InteractionRecovery.interactionsWith_formalSubcircuit_eq_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil

private theorem and_interactionsWith_byte
    (input : Var ByteChip.AndByte.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith Channels.byteChannel.toRaw
      ((ByteChip.AndByte.main input).operations offset) =
      [(pushedIf (channel := Channels.byteChannel) input.multiplicity
        (⟨0,
          Gadgets.And.And8.circuit.output { x := input.b, y := input.c }
            (offset +
              (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
              (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c),
          input.b, input.c⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [ByteChip.AndByte.main, Circuit.operations, Circuit.bind_def,
    subcircuit, assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck8_interactionsWith,
    and8_interactionsWith]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm, Nat.add_zero]

private theorem or_interactionsWith_byte
    (input : Var ByteChip.OrByte.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith Channels.byteChannel.toRaw
      ((ByteChip.OrByte.main input).operations offset) =
      [(pushedIf (channel := Channels.byteChannel) input.multiplicity
        (⟨1,
          Gadgets.Or.Or8.circuit.output { x := input.b, y := input.c }
            (offset +
              (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
              (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c),
          input.b, input.c⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [ByteChip.OrByte.main, Circuit.operations, Circuit.bind_def,
    subcircuit, assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck8_interactionsWith,
    or8_interactionsWith]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm, Nat.add_zero]

private theorem xor_interactionsWith_byte
    (input : Var ByteChip.XorByte.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith Channels.byteChannel.toRaw
      ((ByteChip.XorByte.main input).operations offset) =
      [(pushedIf (channel := Channels.byteChannel) input.multiplicity
        (⟨2,
          var ⟨offset +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c⟩,
          input.b, input.c⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [ByteChip.XorByte.main, Circuit.operations, Circuit.bind_def,
    witnessField, lookup, assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck8_interactionsWith,
    Operations.interactionsWith_witness, Operations.interactionsWith_lookup]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm, Nat.add_zero]

private theorem ltu_interactionsWith_byte
    (input : Var ByteChip.Ltu.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith Channels.byteChannel.toRaw
      ((ByteChip.Ltu.main input).operations offset) =
      [(pushedIf (channel := Channels.byteChannel) input.multiplicity
        (⟨4,
          var ⟨offset +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c⟩,
          input.b, input.c⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [ByteChip.Ltu.main, Circuit.operations, Circuit.bind_def,
    witnessField, assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck8_interactionsWith,
    Operations.interactionsWith_witness, assertBool_interactionsWith]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm, Nat.add_zero]

private theorem u8Range_nativeAccesses_symbolic (env : Environment (ZMod p)) :
    Faithful.nativeAccesses env
        (⟨ByteChip.U8Range.circuit⟩ : Component (ZMod p)).operations =
      [AbstractInteraction.toAccess env
        (pushedIf (channel := Channels.byteChannel) (var ⟨2⟩)
          (⟨3, 0, var ⟨0⟩, var ⟨1⟩⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  have only : ∀ channel ∈ (ByteChip.U8Range.circuit (p := p)).channels,
      channel = Channels.byteChannel.toRaw := by
    intro channel h
    have h' : channel ∈ (ByteChip.U8Range.circuit (p := p)).channels := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.U8Range.circuit at h'
    simpa [circuit_norm] using h'
  rw [Faithful.nativeAccesses_component_eq_rowOperations ByteChip.U8Range.circuit]
  rw [nativeAccesses_byteOnly ByteChip.U8Range.circuit only]
  rw [Air.Flat.Component.rowOperations_mk]
  rw [show (ByteChip.U8Range.circuit (p := p)).main = ByteChip.U8Range.main from rfl]
  simp only [ByteChip.U8Range.main, Circuit.operations, Circuit.bind_def,
    assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append,
    rangeCheck8_interactionsWith, Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append]
  simp only [if_true, List.map_cons, List.map_nil]
  have hbVar :
      (varFromOffset ByteChip.U8Range.Inputs 0 :
        ByteChip.U8Range.Inputs (Expression (ZMod p))).b = var ⟨0⟩ := rfl
  have hcVar :
      (varFromOffset ByteChip.U8Range.Inputs 0 :
        ByteChip.U8Range.Inputs (Expression (ZMod p))).c = var ⟨1⟩ := rfl
  have hmVar :
      (varFromOffset ByteChip.U8Range.Inputs 0 :
        ByteChip.U8Range.Inputs (Expression (ZMod p))).multiplicity = var ⟨2⟩ := rfl
  rw [hbVar, hcVar, hmVar]
  rw [pushedIf_def]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem u8RangeInput_get_zero (input : ByteChip.U8Range.Inputs (ZMod p)) :
    (toElements input)[0] = input.b := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem u8RangeInput_get_one (input : ByteChip.U8Range.Inputs (ZMod p)) :
    (toElements input)[1] = input.c := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem u8RangeInput_get_two (input : ByteChip.U8Range.Inputs (ZMod p)) :
    (toElements input)[2] = input.multiplicity := by cases input; rfl

private theorem u8RangeRow_nativeAccesses
    (row : CoreAIR.Current.Row p .byteLookup)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨ByteChip.U8Range.circuit⟩ : Component (ZMod p)).buildRow
            (byteU8RangeInput row
              (providerRecount skeleton (sourceByteU8RangeKey row))) data hint) data)
        (⟨ByteChip.U8Range.circuit⟩ : Component (ZMod p)).operations =
      [recountedProviderFieldAccess (p := p) skeleton
        (sourceByteU8RangeKey row)] := by
  rw [u8Range_nativeAccesses_symbolic]
  simp only [toAccess_pushIf_byte]
  rw [eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 2 (by change 2 < 3; omega),
    u8RangeInput_get_zero, u8RangeInput_get_one, u8RangeInput_get_two]
  simp only [byteU8RangeInput, recountedProviderFieldAccess, providerRecountField,
    sourceByteU8RangeKey, exactByteU8RangeAccess,
    Extracted.Interaction.toAccess_byte_receive, LookupAccessList.keyOf,
    Expression.eval]

private theorem msb_interactionsWith_byte
    (input : Var ByteChip.MSB.Inputs (ZMod p)) (offset : ℕ) :
    ((ByteChip.MSB.main input).operations offset).interactionsWith
        Channels.byteChannel.toRaw =
      [(pushedIf (channel := Channels.byteChannel) input.multiplicity
        (⟨5,
          var ⟨offset +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b⟩,
          input.b, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [ByteChip.MSB.main, Circuit.operations, Circuit.bind_def, witnessField,
    assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
    rangeCheck8_interactionsWith, assertBool_interactionsWith,
    Channel.pushIf, Operations.interactionsWith_interact, Operations.interactionsWith_nil,
    ChannelInteraction.toRaw_channel, List.nil_append]
  simp only [if_true, circuit_norm, Nat.add_zero]

private theorem msb_main_output_eq
    (input : Var ByteChip.MSB.Inputs (ZMod p)) (offset : ℕ) :
    (ByteChip.MSB.main input).output offset =
      var ⟨offset +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b⟩ := by
  rfl

private theorem msb_buildRow_result
    (input : ByteChip.MSB.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bound : input.b.val < 2 ^ 8) :
    let component := (⟨ByteChip.MSB.circuit⟩ : Component (ZMod p))
    let inputVar : Var ByteChip.MSB.Inputs (ZMod p) :=
      varFromOffset ByteChip.MSB.Inputs 0
    let result : Expression (ZMod p) := var ⟨size ByteChip.MSB.Inputs +
      (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength inputVar.b⟩
    Expression.eval
      (Environment.fromArray (component.buildRow input data hint) data) result =
      if 128 ≤ input.b.val then 1 else 0 := by
  dsimp only
  let component := (⟨ByteChip.MSB.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have hspec := (component.buildRow_spec_requirements input data hint
    ByteChip.MSB.computableWitnesses bound (by trivial)).1
  have hinput : component.rowInput env = input := by
    exact component.rowInput_buildRow input data data hint
  simp only [Air.Flat.Component.Spec] at hspec
  rw [hinput] at hspec
  have hresult : Expression.eval env
      ((ByteChip.MSB.circuit (p := p)).output
        (varFromOffset ByteChip.MSB.Inputs 0) (size ByteChip.MSB.Inputs)) =
      if 128 ≤ input.b.val then 1 else 0 := by
    simpa only [component, Air.Flat.Component.rowOutput, circuit_norm] using hspec.2
  rw [← msb_main_output_eq]
  rw [← show (ByteChip.MSB.circuit (p := p)).main = ByteChip.MSB.main from rfl]
  rw [(ByteChip.MSB.circuit (p := p)).elaborated.output_eq]
  exact hresult

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem msbInput_get_zero (input : ByteChip.MSB.Inputs (ZMod p)) :
    (toElements input)[0] = input.b := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem msbInput_get_one (input : ByteChip.MSB.Inputs (ZMod p)) :
    (toElements input)[1] = input.multiplicity := by cases input; rfl

private theorem and_main_output_eq
    (input : Var ByteChip.AndByte.Inputs (ZMod p)) (offset : ℕ) :
    (ByteChip.AndByte.main input).output offset =
      Gadgets.And.And8.circuit.output { x := input.b, y := input.c }
        (offset +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c) := by
  rfl

private theorem and_buildRow_result_val
    (input : ByteChip.AndByte.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    let component := (⟨ByteChip.AndByte.circuit⟩ : Component (ZMod p))
    let inputVar : Var ByteChip.AndByte.Inputs (ZMod p) :=
      varFromOffset ByteChip.AndByte.Inputs 0
    let result := Gadgets.And.And8.circuit.output
      { x := inputVar.b, y := inputVar.c }
      (size ByteChip.AndByte.Inputs +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength inputVar.b +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength inputVar.c)
    (Expression.eval
      (Environment.fromArray (component.buildRow input data hint) data) result).val =
      input.b.val &&& input.c.val := by
  dsimp only
  let component := (⟨ByteChip.AndByte.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have hspec := (component.buildRow_spec_requirements input data hint
    ByteChip.AndByte.computableWitnesses bounds (by trivial)).1
  have hinput : component.rowInput env = input := by
    exact component.rowInput_buildRow input data data hint
  simp only [Air.Flat.Component.Spec] at hspec
  rw [hinput] at hspec
  have hresult : (Expression.eval env
      ((ByteChip.AndByte.circuit (p := p)).output
        (varFromOffset ByteChip.AndByte.Inputs 0) (size ByteChip.AndByte.Inputs))).val =
      input.b.val &&& input.c.val := by
    simpa only [component, Air.Flat.Component.rowOutput, circuit_norm] using hspec.2
  rw [← and_main_output_eq]
  rw [← show (ByteChip.AndByte.circuit (p := p)).main = ByteChip.AndByte.main from rfl]
  rw [(ByteChip.AndByte.circuit (p := p)).elaborated.output_eq]
  exact hresult

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem andInput_get_zero (input : ByteChip.AndByte.Inputs (ZMod p)) :
    (toElements input)[0] = input.b := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem andInput_get_one (input : ByteChip.AndByte.Inputs (ZMod p)) :
    (toElements input)[1] = input.c := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem andInput_get_two (input : ByteChip.AndByte.Inputs (ZMod p)) :
    (toElements input)[2] = input.multiplicity := by cases input; rfl

private theorem or_main_output_eq
    (input : Var ByteChip.OrByte.Inputs (ZMod p)) (offset : ℕ) :
    (ByteChip.OrByte.main input).output offset =
      Gadgets.Or.Or8.circuit.output { x := input.b, y := input.c }
        (offset +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c) := by
  rfl

private theorem or_buildRow_result_val
    (input : ByteChip.OrByte.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    let component := (⟨ByteChip.OrByte.circuit⟩ : Component (ZMod p))
    let inputVar : Var ByteChip.OrByte.Inputs (ZMod p) :=
      varFromOffset ByteChip.OrByte.Inputs 0
    let result := Gadgets.Or.Or8.circuit.output
      { x := inputVar.b, y := inputVar.c }
      (size ByteChip.OrByte.Inputs +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength inputVar.b +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength inputVar.c)
    (Expression.eval
      (Environment.fromArray (component.buildRow input data hint) data) result).val =
      input.b.val ||| input.c.val := by
  dsimp only
  let component := (⟨ByteChip.OrByte.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have hspec := (component.buildRow_spec_requirements input data hint
    ByteChip.OrByte.computableWitnesses bounds (by trivial)).1
  have hinput : component.rowInput env = input := by
    exact component.rowInput_buildRow input data data hint
  simp only [Air.Flat.Component.Spec] at hspec
  rw [hinput] at hspec
  have hresult : (Expression.eval env
      ((ByteChip.OrByte.circuit (p := p)).output
        (varFromOffset ByteChip.OrByte.Inputs 0) (size ByteChip.OrByte.Inputs))).val =
      input.b.val ||| input.c.val := by
    simpa only [component, Air.Flat.Component.rowOutput, circuit_norm] using hspec.2
  rw [← or_main_output_eq]
  rw [← show (ByteChip.OrByte.circuit (p := p)).main = ByteChip.OrByte.main from rfl]
  rw [(ByteChip.OrByte.circuit (p := p)).elaborated.output_eq]
  exact hresult

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem orInput_get_zero (input : ByteChip.OrByte.Inputs (ZMod p)) :
    (toElements input)[0] = input.b := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem orInput_get_one (input : ByteChip.OrByte.Inputs (ZMod p)) :
    (toElements input)[1] = input.c := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem orInput_get_two (input : ByteChip.OrByte.Inputs (ZMod p)) :
    (toElements input)[2] = input.multiplicity := by cases input; rfl

private theorem xor_main_output_eq
    (input : Var ByteChip.XorByte.Inputs (ZMod p)) (offset : ℕ) :
    (ByteChip.XorByte.main input).output offset =
      var ⟨offset +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c⟩ := by
  rfl

private theorem xor_buildRow_result_val
    (input : ByteChip.XorByte.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    let component := (⟨ByteChip.XorByte.circuit⟩ : Component (ZMod p))
    let inputVar : Var ByteChip.XorByte.Inputs (ZMod p) :=
      varFromOffset ByteChip.XorByte.Inputs 0
    let result : Expression (ZMod p) := var ⟨size ByteChip.XorByte.Inputs +
      (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength inputVar.b +
      (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength inputVar.c⟩
    (Expression.eval
      (Environment.fromArray (component.buildRow input data hint) data) result).val =
      input.b.val ^^^ input.c.val := by
  dsimp only
  let component := (⟨ByteChip.XorByte.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have hspec := (component.buildRow_spec_requirements input data hint
    ByteChip.XorByte.computableWitnesses bounds (by trivial)).1
  have hinput : component.rowInput env = input := by
    exact component.rowInput_buildRow input data data hint
  simp only [Air.Flat.Component.Spec] at hspec
  rw [hinput] at hspec
  have hresult : (Expression.eval env
      ((ByteChip.XorByte.circuit (p := p)).output
        (varFromOffset ByteChip.XorByte.Inputs 0) (size ByteChip.XorByte.Inputs))).val =
      input.b.val ^^^ input.c.val := by
    simpa only [component, Air.Flat.Component.rowOutput, circuit_norm] using hspec.2
  rw [← xor_main_output_eq]
  rw [← show (ByteChip.XorByte.circuit (p := p)).main = ByteChip.XorByte.main from rfl]
  rw [(ByteChip.XorByte.circuit (p := p)).elaborated.output_eq]
  exact hresult

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem xorInput_get_zero (input : ByteChip.XorByte.Inputs (ZMod p)) :
    (toElements input)[0] = input.b := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem xorInput_get_one (input : ByteChip.XorByte.Inputs (ZMod p)) :
    (toElements input)[1] = input.c := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem xorInput_get_two (input : ByteChip.XorByte.Inputs (ZMod p)) :
    (toElements input)[2] = input.multiplicity := by cases input; rfl

private theorem ltu_main_output_eq
    (input : Var ByteChip.Ltu.Inputs (ZMod p)) (offset : ℕ) :
    (ByteChip.Ltu.main input).output offset =
      var ⟨offset +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c⟩ := by
  rfl

private theorem ltu_buildRow_result
    (input : ByteChip.Ltu.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    let component := (⟨ByteChip.Ltu.circuit⟩ : Component (ZMod p))
    let inputVar : Var ByteChip.Ltu.Inputs (ZMod p) :=
      varFromOffset ByteChip.Ltu.Inputs 0
    let result : Expression (ZMod p) := var ⟨size ByteChip.Ltu.Inputs +
      (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength inputVar.b +
      (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength inputVar.c⟩
    Expression.eval
      (Environment.fromArray (component.buildRow input data hint) data) result =
      if input.b.val < input.c.val then 1 else 0 := by
  dsimp only
  let component := (⟨ByteChip.Ltu.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have hspec := (component.buildRow_spec_requirements input data hint
    ByteChip.Ltu.computableWitnesses bounds (by trivial)).1
  have hinput : component.rowInput env = input := by
    exact component.rowInput_buildRow input data data hint
  simp only [Air.Flat.Component.Spec] at hspec
  rw [hinput] at hspec
  have hresult : Expression.eval env
      ((ByteChip.Ltu.circuit (p := p)).output
        (varFromOffset ByteChip.Ltu.Inputs 0) (size ByteChip.Ltu.Inputs)) =
      if input.b.val < input.c.val then 1 else 0 := by
    simpa only [component, Air.Flat.Component.rowOutput, circuit_norm] using hspec.2
  rw [← ltu_main_output_eq]
  rw [← show (ByteChip.Ltu.circuit (p := p)).main = ByteChip.Ltu.main from rfl]
  rw [(ByteChip.Ltu.circuit (p := p)).elaborated.output_eq]
  exact hresult

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem ltuInput_get_zero (input : ByteChip.Ltu.Inputs (ZMod p)) :
    (toElements input)[0] = input.b := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem ltuInput_get_one (input : ByteChip.Ltu.Inputs (ZMod p)) :
    (toElements input)[1] = input.c := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem ltuInput_get_two (input : ByteChip.Ltu.Inputs (ZMod p)) :
    (toElements input)[2] = input.multiplicity := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem rangeInput_get_zero (input : RangeChip.Inputs (ZMod p)) :
    (toElements input)[0] = input.a := by cases input; rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem rangeInput_get_one (input : RangeChip.Inputs (ZMod p)) :
    (toElements input)[1] = input.multiplicity := by cases input; rfl

private theorem msbRow_nativeAccesses
    (contract : PreprocessedProviderContract witness)
    (row : CoreAIR.Current.Row p .byteLookup)
    (hrow : row ∈ witness.trace.rows .byteLookup)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨ByteChip.MSB.circuit⟩ : Component (ZMod p)).buildRow
            (byteMsbInput row
              (providerRecount skeleton (sourceByteMsbKey row))) data hint) data)
        (⟨ByteChip.MSB.circuit⟩ : Component (ZMod p)).operations =
      [recountedProviderFieldAccess (p := p) skeleton
        (sourceByteMsbKey row)] := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations ByteChip.MSB.circuit]
  have only : ∀ channel ∈ (ByteChip.MSB.circuit (p := p)).channels,
      channel = Channels.byteChannel.toRaw := by
    intro channel h
    have h' : channel ∈ (ByteChip.MSB.circuit (p := p)).channels := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.MSB.circuit at h'
    simpa [circuit_norm] using h'
  rw [nativeAccesses_byteOnly ByteChip.MSB.circuit only]
  rw [Air.Flat.Component.rowOperations_mk]
  rw [show (ByteChip.MSB.circuit (p := p)).main = ByteChip.MSB.main from rfl]
  rw [msb_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  rw [msb_buildRow_result _ _ _ (contract.byteOperandBounds hrow).1]
  have hbVar :
      (varFromOffset ByteChip.MSB.Inputs 0 :
        ByteChip.MSB.Inputs (Expression (ZMod p))).b = var ⟨0⟩ := rfl
  have hmVar :
      (varFromOffset ByteChip.MSB.Inputs 0 :
        ByteChip.MSB.Inputs (Expression (ZMod p))).multiplicity = var ⟨1⟩ := rfl
  rw [hbVar, hmVar,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 2; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 2; omega),
    msbInput_get_zero, msbInput_get_one]
  simp only [byteMsbInput, recountedProviderFieldAccess, providerRecountField,
    sourceByteMsbKey, exactByteMsbAccess, LookupAccessList.keyOf,
    Extracted.Interaction.toAccess_byte_receive, Expression.eval,
    PreprocessedProviderContract.byteMsbValue contract hrow]

private theorem andRow_nativeAccesses
    (contract : PreprocessedProviderContract witness)
    (row : CoreAIR.Current.Row p .byteLookup)
    (hrow : row ∈ witness.trace.rows .byteLookup)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨ByteChip.AndByte.circuit⟩ : Component (ZMod p)).buildRow
            (byteAndInput row
              (providerRecount skeleton (sourceByteAndKey row))) data hint) data)
        (⟨ByteChip.AndByte.circuit⟩ : Component (ZMod p)).operations =
      [recountedProviderFieldAccess (p := p) skeleton
        (sourceByteAndKey row)] := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations ByteChip.AndByte.circuit]
  have only : ∀ channel ∈ (ByteChip.AndByte.circuit (p := p)).channels,
      channel = Channels.byteChannel.toRaw := by
    intro channel h
    have h' : channel ∈ (ByteChip.AndByte.circuit (p := p)).channels := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.AndByte.circuit at h'
    simpa [circuit_norm] using h'
  rw [nativeAccesses_byteOnly ByteChip.AndByte.circuit only]
  rw [Air.Flat.Component.rowOperations_mk]
  rw [show (ByteChip.AndByte.circuit (p := p)).main = ByteChip.AndByte.main from rfl]
  rw [and_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  rw [and_buildRow_result_val _ _ _ (contract.byteOperandBounds hrow)]
  have hbVar :
      (varFromOffset ByteChip.AndByte.Inputs 0 :
        ByteChip.AndByte.Inputs (Expression (ZMod p))).b = var ⟨0⟩ := rfl
  have hcVar :
      (varFromOffset ByteChip.AndByte.Inputs 0 :
        ByteChip.AndByte.Inputs (Expression (ZMod p))).c = var ⟨1⟩ := rfl
  have hmVar :
      (varFromOffset ByteChip.AndByte.Inputs 0 :
        ByteChip.AndByte.Inputs (Expression (ZMod p))).multiplicity = var ⟨2⟩ := rfl
  rw [hbVar, hcVar, hmVar,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 2 (by change 2 < 3; omega),
    andInput_get_zero, andInput_get_one, andInput_get_two]
  simp only [byteAndInput, recountedProviderFieldAccess, providerRecountField,
    sourceByteAndKey, exactByteAndAccess, LookupAccessList.keyOf,
    Extracted.Interaction.toAccess_byte_receive, Expression.eval]
  rw [PreprocessedProviderContract.byteAndValue contract hrow]

private theorem orRow_nativeAccesses
    (contract : PreprocessedProviderContract witness)
    (row : CoreAIR.Current.Row p .byteLookup)
    (hrow : row ∈ witness.trace.rows .byteLookup)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨ByteChip.OrByte.circuit⟩ : Component (ZMod p)).buildRow
            (byteOrInput row
              (providerRecount skeleton (sourceByteOrKey row))) data hint) data)
        (⟨ByteChip.OrByte.circuit⟩ : Component (ZMod p)).operations =
      [recountedProviderFieldAccess (p := p) skeleton
        (sourceByteOrKey row)] := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations ByteChip.OrByte.circuit]
  have only : ∀ channel ∈ (ByteChip.OrByte.circuit (p := p)).channels,
      channel = Channels.byteChannel.toRaw := by
    intro channel h
    have h' : channel ∈ (ByteChip.OrByte.circuit (p := p)).channels := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.OrByte.circuit at h'
    simpa [circuit_norm] using h'
  rw [nativeAccesses_byteOnly ByteChip.OrByte.circuit only]
  rw [Air.Flat.Component.rowOperations_mk]
  rw [show (ByteChip.OrByte.circuit (p := p)).main = ByteChip.OrByte.main from rfl]
  rw [or_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  rw [or_buildRow_result_val _ _ _ (contract.byteOperandBounds hrow)]
  have hbVar :
      (varFromOffset ByteChip.OrByte.Inputs 0 :
        ByteChip.OrByte.Inputs (Expression (ZMod p))).b = var ⟨0⟩ := rfl
  have hcVar :
      (varFromOffset ByteChip.OrByte.Inputs 0 :
        ByteChip.OrByte.Inputs (Expression (ZMod p))).c = var ⟨1⟩ := rfl
  have hmVar :
      (varFromOffset ByteChip.OrByte.Inputs 0 :
        ByteChip.OrByte.Inputs (Expression (ZMod p))).multiplicity = var ⟨2⟩ := rfl
  rw [hbVar, hcVar, hmVar,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 2 (by change 2 < 3; omega),
    orInput_get_zero, orInput_get_one, orInput_get_two]
  simp only [byteOrInput, recountedProviderFieldAccess, providerRecountField,
    sourceByteOrKey, exactByteOrAccess, LookupAccessList.keyOf,
    Extracted.Interaction.toAccess_byte_receive, Expression.eval]
  rw [PreprocessedProviderContract.byteOrValue contract hrow]

private theorem xorRow_nativeAccesses
    (contract : PreprocessedProviderContract witness)
    (row : CoreAIR.Current.Row p .byteLookup)
    (hrow : row ∈ witness.trace.rows .byteLookup)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨ByteChip.XorByte.circuit⟩ : Component (ZMod p)).buildRow
            (byteXorInput row
              (providerRecount skeleton (sourceByteXorKey row))) data hint) data)
        (⟨ByteChip.XorByte.circuit⟩ : Component (ZMod p)).operations =
      [recountedProviderFieldAccess (p := p) skeleton
        (sourceByteXorKey row)] := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations ByteChip.XorByte.circuit]
  have only : ∀ channel ∈ (ByteChip.XorByte.circuit (p := p)).channels,
      channel = Channels.byteChannel.toRaw := by
    intro channel h
    have h' : channel ∈ (ByteChip.XorByte.circuit (p := p)).channels := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.XorByte.circuit at h'
    simpa [circuit_norm] using h'
  rw [nativeAccesses_byteOnly ByteChip.XorByte.circuit only]
  rw [Air.Flat.Component.rowOperations_mk]
  rw [show (ByteChip.XorByte.circuit (p := p)).main = ByteChip.XorByte.main from rfl]
  rw [xor_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  rw [xor_buildRow_result_val _ _ _ (contract.byteOperandBounds hrow)]
  have hbVar :
      (varFromOffset ByteChip.XorByte.Inputs 0 :
        ByteChip.XorByte.Inputs (Expression (ZMod p))).b = var ⟨0⟩ := rfl
  have hcVar :
      (varFromOffset ByteChip.XorByte.Inputs 0 :
        ByteChip.XorByte.Inputs (Expression (ZMod p))).c = var ⟨1⟩ := rfl
  have hmVar :
      (varFromOffset ByteChip.XorByte.Inputs 0 :
        ByteChip.XorByte.Inputs (Expression (ZMod p))).multiplicity = var ⟨2⟩ := rfl
  rw [hbVar, hcVar, hmVar,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 2 (by change 2 < 3; omega),
    xorInput_get_zero, xorInput_get_one, xorInput_get_two]
  simp only [byteXorInput, recountedProviderFieldAccess, providerRecountField,
    sourceByteXorKey, exactByteXorAccess, LookupAccessList.keyOf,
    Extracted.Interaction.toAccess_byte_receive, Expression.eval]
  rw [PreprocessedProviderContract.byteXorValue contract hrow]

private theorem ltuRow_nativeAccesses
    (contract : PreprocessedProviderContract witness)
    (row : CoreAIR.Current.Row p .byteLookup)
    (hrow : row ∈ witness.trace.rows .byteLookup)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨ByteChip.Ltu.circuit⟩ : Component (ZMod p)).buildRow
            (byteLtuInput row
              (providerRecount skeleton (sourceByteLtuKey row))) data hint) data)
        (⟨ByteChip.Ltu.circuit⟩ : Component (ZMod p)).operations =
      [recountedProviderFieldAccess (p := p) skeleton
        (sourceByteLtuKey row)] := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations ByteChip.Ltu.circuit]
  have only : ∀ channel ∈ (ByteChip.Ltu.circuit (p := p)).channels,
      channel = Channels.byteChannel.toRaw := by
    intro channel h
    have h' : channel ∈ (ByteChip.Ltu.circuit (p := p)).channels := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.Ltu.circuit at h'
    simpa [circuit_norm] using h'
  rw [nativeAccesses_byteOnly ByteChip.Ltu.circuit only]
  rw [Air.Flat.Component.rowOperations_mk]
  rw [show (ByteChip.Ltu.circuit (p := p)).main = ByteChip.Ltu.main from rfl]
  rw [ltu_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  rw [ltu_buildRow_result _ _ _ (contract.byteOperandBounds hrow)]
  have hbVar :
      (varFromOffset ByteChip.Ltu.Inputs 0 :
        ByteChip.Ltu.Inputs (Expression (ZMod p))).b = var ⟨0⟩ := rfl
  have hcVar :
      (varFromOffset ByteChip.Ltu.Inputs 0 :
        ByteChip.Ltu.Inputs (Expression (ZMod p))).c = var ⟨1⟩ := rfl
  have hmVar :
      (varFromOffset ByteChip.Ltu.Inputs 0 :
        ByteChip.Ltu.Inputs (Expression (ZMod p))).multiplicity = var ⟨2⟩ := rfl
  rw [hbVar, hcVar, hmVar,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 2 (by change 2 < 3; omega),
    ltuInput_get_zero, ltuInput_get_one, ltuInput_get_two]
  simp only [byteLtuInput, recountedProviderFieldAccess, providerRecountField,
    sourceByteLtuKey, exactByteLtuAccess, LookupAccessList.keyOf,
    Extracted.Interaction.toAccess_byte_receive, Expression.eval,
    PreprocessedProviderContract.byteLtuValue contract hrow]

private theorem rangeRow_nativeAccesses (width : RangeChip.Width)
    (row : CoreAIR.Current.Row p .rangeLookup)
    (widthEq : row.preprocessed[1].val = width.val)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨RangeChip.circuitFor width⟩ : Component (ZMod p)).buildRow
            (rangeProviderInput row
              (providerRecount skeleton (sourceRangeKey row))) data hint) data)
        (⟨RangeChip.circuitFor width⟩ : Component (ZMod p)).operations =
      [recountedProviderFieldAccess (p := p) skeleton
        (sourceRangeKey row)] := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations (RangeChip.circuitFor width)]
  have only : ∀ channel ∈ (RangeChip.circuitFor width (p := p)).channels,
      channel = Channels.byteChannel.toRaw := by
    intro channel h
    have h' : channel ∈ (RangeChip.circuitFor width (p := p)).channels := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold RangeChip.circuitFor RangeChip.circuit at h'
    simpa [circuit_norm] using h'
  rw [nativeAccesses_byteOnly (RangeChip.circuitFor width) only]
  rw [Air.Flat.Component.rowOperations_mk]
  rw [show (RangeChip.circuitFor width (p := p)).main =
      RangeChip.main width.val
        (RangeChip.two_pow_lt (Nat.le_of_lt_succ width.isLt)) from rfl]
  rw [range_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  have haVar :
      (varFromOffset RangeChip.Inputs 0 :
        RangeChip.Inputs (Expression (ZMod p))).a = var ⟨0⟩ := rfl
  have hmVar :
      (varFromOffset RangeChip.Inputs 0 :
        RangeChip.Inputs (Expression (ZMod p))).multiplicity = var ⟨1⟩ := rfl
  rw [haVar, hmVar,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 2; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 2; omega),
    rangeInput_get_zero, rangeInput_get_one]
  have nlt : width.val < p := lt_trans Nat.lt_two_pow_self
    (RangeChip.two_pow_lt (Nat.le_of_lt_succ width.isLt))
  simp only [rangeProviderInput, recountedProviderFieldAccess, providerRecountField,
    sourceRangeKey, exactRangeAccess, LookupAccessList.keyOf,
    Extracted.Interaction.toAccess_byte_receive, Expression.eval,
    ZMod.val_natCast_of_lt nlt,
    widthEq]

private def programInputAccess
    (input : ProgramProviderChip.Inputs (ZMod p)) : LookupAccess :=
  (InteractionKind.Program, "SP1Program",
    [input.pc0.val, input.pc1.val, input.pc2.val, input.opcode.val,
      input.op_a.val, input.op_b[0].val, input.op_b[1].val,
      input.op_b[2].val, input.op_b[3].val, input.op_c[0].val,
      input.op_c[1].val, input.op_c[2].val, input.op_c[3].val,
      input.op_a_0.val, input.imm_b.val, input.imm_c.val],
    signedVal input.multiplicity)

private theorem program_nativeAccesses_symbolic
    (env : Environment (ZMod p)) :
    Faithful.nativeAccesses env
        (⟨ProgramProviderChip.circuit⟩ : Component (ZMod p)).operations =
      [LookupAccessList.negMult
        (AbstractInteraction.toAccess env
          (pushedIf (channel := Channels.programChannel)
            (varFromOffset ProgramProviderChip.Inputs 0 :
              Var ProgramProviderChip.Inputs (ZMod p)).multiplicity
            (varFromOffset ProgramProviderChip.Inputs 0 :
              Var ProgramProviderChip.Inputs (ZMod p)).toMessage).toRaw)] := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations ProgramProviderChip.circuit]
  have only : ∀ channel ∈ (ProgramProviderChip.circuit (p := p)).channels,
      channel = Channels.programChannel.toRaw := by
    intro channel h
    have h' : channel ∈ (ProgramProviderChip.circuit (p := p)).channels := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ProgramProviderChip.circuit at h'
    simpa [circuit_norm] using h'
  rw [nativeAccesses_programOnly ProgramProviderChip.circuit only]
  rw [Air.Flat.Component.rowOperations_mk]
  rw [show (ProgramProviderChip.circuit (p := p)).main =
      ProgramProviderChip.main from rfl]
  rw [program_interactionsWith_program]
  simp only [List.map_cons, List.map_nil]

omit [Fact (2 ^ 24 < p)] in
private theorem program_toAccess_eq_inputAccess
    (env : Environment (ZMod p))
    (input : Var ProgramProviderChip.Inputs (ZMod p)) :
    AbstractInteraction.toAccess env
        (pushedIf (channel := Channels.programChannel) input.multiplicity
          input.toMessage).toRaw =
      programInputAccess (Eval.eval env input) := by
  rw [toAccess_pushIf_program]
  simp only [programInputAccess, ProgramProviderChip.Inputs.toMessage, circuit_norm]

private theorem programInput_nativeAccesses
    (input : ProgramProviderChip.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨ProgramProviderChip.circuit⟩ : Component (ZMod p)).buildRow
            input data hint) data)
        (⟨ProgramProviderChip.circuit⟩ : Component (ZMod p)).operations =
      [LookupAccessList.negMult (programInputAccess input)] := by
  rw [program_nativeAccesses_symbolic]
  rw [program_toAccess_eq_inputAccess]
  let component := (⟨ProgramProviderChip.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have inputEq : Eval.eval env
      (varFromOffset ProgramProviderChip.Inputs 0 :
        Var ProgramProviderChip.Inputs (ZMod p)) = input := by
    rw [eval_varFromOffset_valueFromOffset]
    exact component.rowInput_buildRow input data data hint
  rw [inputEq]

private theorem programRow_nativeAccesses
    (row : CoreAIR.Current.Row p .program)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨ProgramProviderChip.circuit⟩ : Component (ZMod p)).buildRow
            (programProviderInput row
              (providerRecount skeleton (sourceProgramKey row))) data hint) data)
        (⟨ProgramProviderChip.circuit⟩ : Component (ZMod p)).operations =
      [LookupAccessList.negMult
        (recountedProviderFieldAccess (p := p) skeleton
          (sourceProgramKey row))] := by
  rw [programInput_nativeAccesses]
  simp only [programInputAccess, programProviderInput, recountedProviderFieldAccess,
    providerRecountField, sourceProgramKey, exactProgramAccess,
    LookupAccessList.keyOf, Extracted.Interaction.toAccess, Extracted.Dir.sign,
    Opcode.ofNat]
  rfl

private theorem transportU8RangeTable_cleanAccesses
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tableCleanAccesses (transportU8RangeTable witness inventory skeleton data hint) =
      (canonicalByteU8RangeRows inventory).map fun row =>
        recountedProviderFieldAccess (p := p) skeleton
          (sourceByteU8RangeKey row) := by
  apply tableCleanAccesses_build_map_singleton
    (⟨ByteChip.U8Range.circuit⟩ : Component (ZMod p))
    (canonicalByteU8RangeRows inventory)
    (fun row => byteU8RangeInput row
      (providerRecount skeleton (sourceByteU8RangeKey row)))
    (fun row => recountedProviderFieldAccess (p := p) skeleton
      (sourceByteU8RangeKey row)) data hint
  intro row _
  rw [cleanAccesses_eq_nativeAccesses_byteOnly ByteChip.U8Range.circuit]
  · exact u8RangeRow_nativeAccesses row skeleton data hint
  · intro channel h
    have h' := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.U8Range.circuit at h'
    simpa [circuit_norm] using h'

private theorem transportMsbTable_cleanAccesses
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tableCleanAccesses (transportMsbTable witness inventory skeleton data hint) =
      (canonicalByteMsbRows inventory).map fun row =>
        recountedProviderFieldAccess (p := p) skeleton
          (sourceByteMsbKey row) := by
  apply tableCleanAccesses_build_map_singleton
    (⟨ByteChip.MSB.circuit⟩ : Component (ZMod p))
    (canonicalByteMsbRows inventory)
    (fun row => byteMsbInput row
      (providerRecount skeleton (sourceByteMsbKey row)))
    (fun row => recountedProviderFieldAccess (p := p) skeleton
      (sourceByteMsbKey row)) data hint
  intro row hrow
  rw [cleanAccesses_eq_nativeAccesses_byteOnly ByteChip.MSB.circuit]
  · exact msbRow_nativeAccesses contract row
      (canonicalByteRows_mem_source witness inventory row (Or.inr (Or.inl hrow)))
      skeleton data hint
  · intro channel h
    have h' := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.MSB.circuit at h'
    simpa [circuit_norm] using h'

private theorem transportAndTable_cleanAccesses
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tableCleanAccesses (transportAndTable witness inventory skeleton data hint) =
      (canonicalByteAndRows inventory).map fun row =>
        recountedProviderFieldAccess (p := p) skeleton
          (sourceByteAndKey row) := by
  apply tableCleanAccesses_build_map_singleton
    (⟨ByteChip.AndByte.circuit⟩ : Component (ZMod p))
    (canonicalByteAndRows inventory)
    (fun row => byteAndInput row
      (providerRecount skeleton (sourceByteAndKey row)))
    (fun row => recountedProviderFieldAccess (p := p) skeleton
      (sourceByteAndKey row)) data hint
  intro row hrow
  rw [cleanAccesses_eq_nativeAccesses_byteOnly ByteChip.AndByte.circuit]
  · exact andRow_nativeAccesses contract row
      (canonicalByteRows_mem_source witness inventory row (Or.inr (Or.inr (Or.inl hrow))))
      skeleton data hint
  · intro channel h
    have h' := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.AndByte.circuit at h'
    simpa [circuit_norm] using h'

private theorem transportOrTable_cleanAccesses
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tableCleanAccesses (transportOrTable witness inventory skeleton data hint) =
      (canonicalByteOrRows inventory).map fun row =>
        recountedProviderFieldAccess (p := p) skeleton
          (sourceByteOrKey row) := by
  apply tableCleanAccesses_build_map_singleton
    (⟨ByteChip.OrByte.circuit⟩ : Component (ZMod p))
    (canonicalByteOrRows inventory)
    (fun row => byteOrInput row
      (providerRecount skeleton (sourceByteOrKey row)))
    (fun row => recountedProviderFieldAccess (p := p) skeleton
      (sourceByteOrKey row)) data hint
  intro row hrow
  rw [cleanAccesses_eq_nativeAccesses_byteOnly ByteChip.OrByte.circuit]
  · exact orRow_nativeAccesses contract row
      (canonicalByteRows_mem_source witness inventory row
        (Or.inr (Or.inr (Or.inr (Or.inl hrow)))))
      skeleton data hint
  · intro channel h
    have h' := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.OrByte.circuit at h'
    simpa [circuit_norm] using h'

private theorem transportXorTable_cleanAccesses
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tableCleanAccesses (transportXorTable witness inventory skeleton data hint) =
      (canonicalByteXorRows inventory).map fun row =>
        recountedProviderFieldAccess (p := p) skeleton
          (sourceByteXorKey row) := by
  apply tableCleanAccesses_build_map_singleton
    (⟨ByteChip.XorByte.circuit⟩ : Component (ZMod p))
    (canonicalByteXorRows inventory)
    (fun row => byteXorInput row
      (providerRecount skeleton (sourceByteXorKey row)))
    (fun row => recountedProviderFieldAccess (p := p) skeleton
      (sourceByteXorKey row)) data hint
  intro row hrow
  rw [cleanAccesses_eq_nativeAccesses_byteOnly ByteChip.XorByte.circuit]
  · exact xorRow_nativeAccesses contract row
      (canonicalByteRows_mem_source witness inventory row
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hrow))))))
      skeleton data hint
  · intro channel h
    have h' := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.XorByte.circuit at h'
    simpa [circuit_norm] using h'

private theorem transportLtuTable_cleanAccesses
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tableCleanAccesses (transportLtuTable witness inventory skeleton data hint) =
      (canonicalByteLtuRows inventory).map fun row =>
        recountedProviderFieldAccess (p := p) skeleton
          (sourceByteLtuKey row) := by
  apply tableCleanAccesses_build_map_singleton
    (⟨ByteChip.Ltu.circuit⟩ : Component (ZMod p))
    (canonicalByteLtuRows inventory)
    (fun row => byteLtuInput row
      (providerRecount skeleton (sourceByteLtuKey row)))
    (fun row => recountedProviderFieldAccess (p := p) skeleton
      (sourceByteLtuKey row)) data hint
  intro row hrow
  rw [cleanAccesses_eq_nativeAccesses_byteOnly ByteChip.Ltu.circuit]
  · exact ltuRow_nativeAccesses contract row
      (canonicalByteRows_mem_source witness inventory row
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrow))))))
      skeleton data hint
  · intro channel h
    have h' := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ByteChip.Ltu.circuit at h'
    simpa [circuit_norm] using h'

private theorem transportRangeTable_cleanAccesses (width : RangeChip.Width)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tableCleanAccesses (transportRangeTable width witness inventory skeleton data hint) =
      (canonicalRangeRows width inventory).map fun row =>
        recountedProviderFieldAccess (p := p) skeleton
          (sourceRangeKey row) := by
  apply tableCleanAccesses_build_map_singleton
    (⟨RangeChip.circuitFor width⟩ : Component (ZMod p))
    (canonicalRangeRows width inventory)
    (fun row => rangeProviderInput row
      (providerRecount skeleton (sourceRangeKey row)))
    (fun row => recountedProviderFieldAccess (p := p) skeleton
      (sourceRangeKey row)) data hint
  intro row hrow
  rw [cleanAccesses_eq_nativeAccesses_byteOnly (RangeChip.circuitFor width)]
  · exact rangeRow_nativeAccesses width row
      (by
        obtain ⟨-, widthEq⟩ := List.mem_filter.mp
          (canonicalRangeRows_mem_source width witness inventory row hrow)
        simpa only [decide_eq_true_eq] using widthEq)
      skeleton data hint
  · intro channel h
    have h' := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold RangeChip.circuitFor RangeChip.circuit at h'
    simpa [circuit_norm] using h'

private theorem transportProgramTable_cleanAccesses
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tableCleanAccesses (transportProgramTable witness inventory skeleton data hint) =
      (canonicalProgramRows inventory).map fun row =>
        recountedProviderFieldAccess (p := p) skeleton
          (sourceProgramKey row) := by
  apply tableCleanAccesses_build_map_singleton
    (⟨ProgramProviderChip.circuit⟩ : Component (ZMod p))
    (canonicalProgramRows inventory)
    (fun row => programProviderInput row
      (providerRecount skeleton (sourceProgramKey row)))
    (fun row => recountedProviderFieldAccess (p := p) skeleton
      (sourceProgramKey row)) data hint
  intro row _
  rw [cleanAccesses_eq_nativeAccesses_programOnly ProgramProviderChip.circuit]
  · rw [programRow_nativeAccesses row skeleton data hint]
    simp only [List.map_cons, List.map_nil, LookupAccessList.negMult_negMult]
  · intro channel h
    have h' := h
    simp only [GeneralFormalCircuit.channels] at h'
    unfold ProgramProviderChip.circuit at h'
    simpa [circuit_norm] using h'

/-- Literal Clean ledger of the constructed preprocessing prefix before decoding centered field
counts.  This is a circuit theorem: it uses only per-row source-key semantics and makes no
claim about the exact source main columns. -/
private theorem extractedPreprocessedProviderTables_fieldAccesses
    (contract : PreprocessedProviderContract witness)
    (inventory : CanonicalPreprocessedInventory witness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tablesCleanAccesses
        (extractedPreprocessedProviderTables witness inventory skeleton data hint) =
      (inventoryPreprocessedKeys inventory).map
        (recountedProviderFieldAccess (p := p) skeleton) := by
  have rangeTables :
      ((RangeChip.allWidths.map fun width =>
          transportRangeTable width witness inventory skeleton data hint).flatMap
        tableCleanAccesses) =
      RangeChip.allWidths.flatMap fun width =>
        (canonicalRangeRows width inventory).map fun row =>
          recountedProviderFieldAccess (p := p) skeleton
            (sourceRangeKey row) := by
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro width widthMem
    exact transportRangeTable_cleanAccesses width witness inventory skeleton data hint
  simp only [tablesCleanAccesses, extractedPreprocessedProviderTables,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [transportU8RangeTable_cleanAccesses, transportMsbTable_cleanAccesses contract,
    transportAndTable_cleanAccesses contract, transportOrTable_cleanAccesses contract,
    transportXorTable_cleanAccesses contract, transportLtuTable_cleanAccesses contract,
    rangeTables, transportProgramTable_cleanAccesses]
  simp only [inventoryPreprocessedKeys, List.map_append, List.map_map,
    List.map_flatMap, Function.comp_def, List.append_assoc]

/-- **Native-consumer recount theorem.**  The twenty-four constructed preprocessing tables emit
exactly one literal Clean access per inventory key, with the integer multiplicity reconstructed
from the non-preprocessed skeleton.  Source main-column multiplicities do not occur in either side. -/
theorem extractedPreprocessedProviderTables_cleanAccesses
    (contract : PreprocessedProviderRecountContract witness inventory skeleton)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tablesCleanAccesses
        (extractedPreprocessedProviderTables witness inventory skeleton data hint) =
      recountedPreprocessedProviderAccesses inventory skeleton := by
  rw [extractedPreprocessedProviderTables_fieldAccesses contract.localSemantics inventory]
  unfold recountedPreprocessedProviderAccesses
  apply List.map_congr_left
  intro key keyMem
  exact contract.fieldAccess_eq_recounted keyMem

private theorem multiplicitySum_map_recountedProviderAccess
    (keys : List LookupKey) (keysNodup : keys.Nodup)
    (skeleton : LookupAccessList) (key : LookupKey) :
    LookupAccessList.multiplicitySum
        (keys.map (recountedProviderAccess skeleton)) key =
      if key ∈ keys then (providerRecount skeleton key : ℤ) else 0 := by
  induction keys with
  | nil => simp only [List.map_nil, LookupAccessList.multiplicitySum_nil, List.not_mem_nil,
      if_false]
  | cons head tail ih =>
    obtain ⟨headNotMem, tailNodup⟩ := List.nodup_cons.mp keysNodup
    rw [List.map_cons, LookupAccessList.multiplicitySum_cons, ih tailNodup]
    simp only [recountedProviderAccess, LookupAccessList.keyOf,
      LookupAccessList.multOf, List.mem_cons]
    by_cases headEq : head = key
    · subst head
      simp [headNotMem]
    · simp [headEq, Ne.symm headEq]

omit [Fact (2 ^ 24 < p)] in
/-- The explicit recount obligations are exactly sufficient to balance every Byte/Program key of
the skeleton against the constructed provider prefix. -/
theorem skeleton_append_recountedPreprocessedProviderAccesses_balanced
    (contract : PreprocessedProviderRecountContract witness inventory skeleton)
    (key : LookupKey) (keyKind : IsPreprocessedProviderKey key) :
    LookupAccessList.multiplicitySum
        (skeleton ++ recountedPreprocessedProviderAccesses inventory skeleton) key = 0 := by
  rw [LookupAccessList.multiplicitySum_append]
  unfold recountedPreprocessedProviderAccesses
  rw [multiplicitySum_map_recountedProviderAccess _
    (inventoryPreprocessedKeys_nodup inventory)]
  by_cases skeletonZero : LookupAccessList.multiplicitySum skeleton key = 0
  · have recountZero : providerRecount skeleton key = 0 := by
      simp only [providerRecount, skeletonZero, neg_zero, Int.toNat_zero]
    simp only [skeletonZero, zero_add, recountZero, Nat.cast_zero]
    split <;> rfl
  · have keyMem := contract.coverage key keyKind skeletonZero
    rw [if_pos keyMem, contract.recount_eq_neg keyMem]
    omega

end SP1Clean.Composition
