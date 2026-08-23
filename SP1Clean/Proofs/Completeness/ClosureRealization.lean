import SP1Clean.Proofs.Completeness.Closure
import SP1Clean.Soundness.EnsembleChannels

/-!
# Realizing the closure: the provider entry lists a shard's demand determines

`Closure.lean` has both halves of the ledger — the demand side (`closingAccesses`, a recount
against a provider-free skeleton) and the supply side (`providerLedger`, what the twenty-four
preprocessed provider tables emit). What it does not have is any reason for the two to agree: the
eight occurrence lists are free fields of `SupportedCoreTraceWitness`, so a trace may populate them
with anything.

This module closes that. It **derives** the eight lists from the demand: each is the closing key
list, filtered to the keys that family serves, with each key's own recount as its multiplicity.
`providerLedger_eq_closingAccesses` is then a theorem rather than a hypothesis, and Byte/Program
balance follows for any trace whose entry fields are the derived ones.

## What "servable" means, and why it is a real premise

A provider does not merely *carry* a key — it *computes* part of it. The `AND` table's second cell
is `b &&& c`, derived in-circuit from the two operand cells; the `MSB` table's is the high bit of
its single operand. So a key like `(Byte, "SP1Byte", [0, 5, 3, 3])` — a consumer claiming
`3 AND 3 = 5` — is one **no honest provider row can supply**, and no closure can rescue it. The
same holds for a Range demand outside its width and for a Program key whose limbs exceed 16 bits.

`Servable` names exactly that condition, per key. It is a genuine completeness premise, not a
technicality: a shard whose chips pull an arithmetically wrong byte key is not completable, and
this is where that shows up. Every satisfying trace meets it, because a satisfied consumer row's
byte pull is computed by the same arithmetic the provider recomputes.

The second premise, `DemandFits`, is the capacity contract already familiar from `CountsFit`: a
recount is carried in one field element and read back through the centered ledger, so it must stay
under half the field. Here it is stated on the demand rather than on supplied entries, because the
entries are no longer supplied.
-/

namespace SP1Clean.Soundness

open Air.Flat (Table)
open LookupAccessList (LookupKey accessAt closingAccesses closingKeys keyOf multOf
  multiplicitySum providerRecount)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-! ## Reading a key -/

/-- One cell of a key's entry, defaulting outside the row. Total so the builders below need no
length side condition; `Servable` supplies the shape. -/
def cell (k : LookupKey) (i : ℕ) : ℕ := k.2.2.getD i 0

/-- A well-shaped Byte key: the byte bus, SP1's single byte table, four cells. -/
def IsByteKey (k : LookupKey) : Bool :=
  decide (k.1 = InteractionKind.Byte ∧ k.2.1 = "SP1Byte" ∧ k.2.2.length = 4)

/-- A well-shaped Program key: the program bus, SP1's ROM table, sixteen cells. -/
def IsProgramKey (k : LookupKey) : Bool :=
  decide (k.1 = InteractionKind.Program ∧ k.2.1 = "SP1Program" ∧ k.2.2.length = 16)

/-- A Byte key claimed by the byte-opcode table `s`. -/
def selByte (s : ℕ) (k : LookupKey) : Bool := IsByteKey k && decide (cell k 0 = s)

/-- A Byte key claimed by the fixed-width range table at `width`: opcode `6`, with the width in
its third cell. -/
def selRange (width : RangeChip.Width) (k : LookupKey) : Bool :=
  IsByteKey k && decide (cell k 0 = 6 ∧ cell k 2 = width.val)

/-! ## Building the entry a key asks for -/

/-- The byte occurrence a key names: its two operand cells, at the demanded multiplicity. Serves
all six byte tables — `MSB` reads only the first operand, and its key's fourth cell is `0`, so the
same builder produces its occurrence too. -/
def byteEntryOfKey (k : LookupKey) (m : ℕ) : TraceGen.ByteEntry := ⟨cell k 2, cell k 3, m⟩

/-- The range occurrence a key names. Note the value is the *second* cell: a range key is
`[6, value, width, 0]`, so the width occupies the slot a byte key uses for its second operand. -/
def rangeEntryOfKey (k : LookupKey) (m : ℕ) : TraceGen.RangeEntry := ⟨cell k 1, m⟩

/-- The committed ROM entry a key names, reassembling the two 64-bit operand slots and the fetch
address from the limbs the key carries. -/
def romEntryOfKey (k : LookupKey) (m : ℕ) : TraceGen.RomEntry where
  pc := cell k 0 + 2 ^ 16 * cell k 1 + 2 ^ 32 * cell k 2
  opcode := cell k 3
  opA := cell k 4
  opB := cell k 5 + 2 ^ 16 * cell k 6 + 2 ^ 32 * cell k 7 + 2 ^ 48 * cell k 8
  opC := cell k 9 + 2 ^ 16 * cell k 10 + 2 ^ 32 * cell k 11 + 2 ^ 48 * cell k 12
  opA0 := cell k 13
  immB := cell k 14
  immC := cell k 15
  multiplicity := m

/-! ## The generic step

Every family's ledger is the same shape: filter the closing keys to the ones this family serves,
build an occurrence per key at that key's recount, and map it back through the family's access.
The one thing that differs is the round trip — that mapping an occurrence back reproduces the key
it came from — and that is exactly what `Servable` buys.
-/

/-- **A family's supplied ledger is the closure restricted to the keys it serves**, given only that
the round trip holds on those keys. -/
theorem family_ledger_eq {Entry : Type} (skeleton : LookupAccessList)
    (keys : List LookupKey) (sel : LookupKey → Bool)
    (build : LookupKey → ℕ → Entry) (access : Entry → LookupAccess)
    (hround : ∀ k ∈ keys, sel k = true →
      access (build k (providerRecount skeleton k)) = accessAt k (providerRecount skeleton k)) :
    ((keys.filter sel).map fun k => build k (providerRecount skeleton k)).map access =
      closingAccesses skeleton (keys.filter sel) := by
  rw [List.map_map, closingAccesses]
  refine List.map_congr_left fun k hk => ?_
  rw [List.mem_filter] at hk
  exact hround k hk.1 hk.2

/-- **A family supplies exactly its own keys**, and nothing anywhere else. -/
theorem family_multiplicitySum {Entry : Type} (skeleton : LookupAccessList)
    {keys : List LookupKey} (hnodup : keys.Nodup) (sel : LookupKey → Bool)
    (build : LookupKey → ℕ → Entry) (access : Entry → LookupAccess)
    (hround : ∀ k ∈ keys, sel k = true →
      access (build k (providerRecount skeleton k)) = accessAt k (providerRecount skeleton k))
    (k : LookupKey) :
    multiplicitySum
        (((keys.filter sel).map fun key => build key (providerRecount skeleton key)).map access)
        k =
      if k ∈ keys ∧ sel k = true then (providerRecount skeleton k : ℤ) else 0 := by
  rw [family_ledger_eq skeleton keys sel build access hround]
  by_cases hmem : k ∈ keys ∧ sel k = true
  · rw [if_pos hmem,
      LookupAccessList.multiplicitySum_closingAccesses skeleton (hnodup.filter sel)
        (List.mem_filter.mpr ⟨hmem.1, hmem.2⟩)]
  · rw [if_neg hmem,
      LookupAccessList.multiplicitySum_closingAccesses_of_not_mem skeleton
        (fun h => hmem (by rw [List.mem_filter] at h; exact ⟨h.1, h.2⟩))]


/-! ## Servability

What an honest preprocessed provider can supply. Each case pins the key's whole entry, because the
provider *derives* the second cell rather than carrying it: the `AND` table computes `b &&& c`, the
`MSB` table the high bit of its single operand, the `LTU` table the comparison. A key whose derived
cell disagrees is unservable, and no closure can rescue it.
-/

/-- A Byte key an honest byte or range provider can supply. -/
def ByteServable (k : LookupKey) : Prop :=
  match cell k 0 with
  | 0 => k.2.2 = [0, cell k 2 &&& cell k 3, cell k 2, cell k 3] ∧
           cell k 2 < 2 ^ 8 ∧ cell k 3 < 2 ^ 8
  | 1 => k.2.2 = [1, cell k 2 ||| cell k 3, cell k 2, cell k 3] ∧
           cell k 2 < 2 ^ 8 ∧ cell k 3 < 2 ^ 8
  | 2 => k.2.2 = [2, cell k 2 ^^^ cell k 3, cell k 2, cell k 3] ∧
           cell k 2 < 2 ^ 8 ∧ cell k 3 < 2 ^ 8
  | 3 => k.2.2 = [3, 0, cell k 2, cell k 3] ∧ cell k 2 < 2 ^ 8 ∧ cell k 3 < 2 ^ 8
  | 4 => k.2.2 = [4, if cell k 2 < cell k 3 then 1 else 0, cell k 2, cell k 3] ∧
           cell k 2 < 2 ^ 8 ∧ cell k 3 < 2 ^ 8
  | 5 => k.2.2 = [5, if 128 ≤ cell k 2 then 1 else 0, cell k 2, 0] ∧ cell k 2 < 2 ^ 8
  | 6 => k.2.2 = [6, cell k 1, cell k 2, 0] ∧ cell k 2 ≤ 16 ∧ cell k 1 < 2 ^ cell k 2
  | _ => False

/-- Reading a selector back off a Byte key. -/
theorem cell_zero_of_selByte {s : ℕ} {k : LookupKey} (h : selByte s k = true) : cell k 0 = s := by
  simp only [selByte, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem isByteKey_of_selByte {s : ℕ} {k : LookupKey} (h : selByte s k = true) :
    IsByteKey k = true := by
  simp only [selByte, Bool.and_eq_true] at h
  exact h.1

theorem byteKey_kind {k : LookupKey} (h : IsByteKey k = true) : k.1 = InteractionKind.Byte := by
  simp only [IsByteKey, decide_eq_true_eq] at h
  exact h.1

theorem byteKey_table {k : LookupKey} (h : IsByteKey k = true) : k.2.1 = "SP1Byte" := by
  simp only [IsByteKey, decide_eq_true_eq] at h
  exact h.2.1

/-! ## The round trips

Mapping the occurrence a key names back through its family's access reproduces the key. This is the
only thing `family_ledger_eq` asks of a family, and the only place `Servable` is used.
-/

/-- `U8Range`: the occurrence a served key names maps back to that key. -/
theorem u8Range_round (k : LookupKey) (m : ℕ)
    (hsel : selByte 3 k = true) (hserv : ByteServable k) :
    u8RangeAccess (byteEntryOfKey k m) = accessAt k (m : ℤ) := by
  simp only [ByteServable, cell_zero_of_selByte hsel] at hserv
  rw [u8RangeAccess, byteEntryOfKey, accessAt, byteKey_kind (isByteKey_of_selByte hsel),
    byteKey_table (isByteKey_of_selByte hsel), hserv.1]

/-- `MSB`: the occurrence a served key names maps back to that key. -/
theorem msb_round (k : LookupKey) (m : ℕ)
    (hsel : selByte 5 k = true) (hserv : ByteServable k) :
    msbAccess (byteEntryOfKey k m) = accessAt k (m : ℤ) := by
  simp only [ByteServable, cell_zero_of_selByte hsel] at hserv
  rw [msbAccess, byteEntryOfKey, accessAt, byteKey_kind (isByteKey_of_selByte hsel),
    byteKey_table (isByteKey_of_selByte hsel), hserv.1]

/-- `AND`: the occurrence a served key names maps back to that key. -/
theorem and_round (k : LookupKey) (m : ℕ)
    (hsel : selByte 0 k = true) (hserv : ByteServable k) :
    andAccess (byteEntryOfKey k m) = accessAt k (m : ℤ) := by
  simp only [ByteServable, cell_zero_of_selByte hsel] at hserv
  rw [andAccess, byteEntryOfKey, accessAt, byteKey_kind (isByteKey_of_selByte hsel),
    byteKey_table (isByteKey_of_selByte hsel), hserv.1]

/-- `OR`: the occurrence a served key names maps back to that key. -/
theorem or_round (k : LookupKey) (m : ℕ)
    (hsel : selByte 1 k = true) (hserv : ByteServable k) :
    orAccess (byteEntryOfKey k m) = accessAt k (m : ℤ) := by
  simp only [ByteServable, cell_zero_of_selByte hsel] at hserv
  rw [orAccess, byteEntryOfKey, accessAt, byteKey_kind (isByteKey_of_selByte hsel),
    byteKey_table (isByteKey_of_selByte hsel), hserv.1]

/-- `XOR`: the occurrence a served key names maps back to that key. -/
theorem xor_round (k : LookupKey) (m : ℕ)
    (hsel : selByte 2 k = true) (hserv : ByteServable k) :
    xorAccess (byteEntryOfKey k m) = accessAt k (m : ℤ) := by
  simp only [ByteServable, cell_zero_of_selByte hsel] at hserv
  rw [xorAccess, byteEntryOfKey, accessAt, byteKey_kind (isByteKey_of_selByte hsel),
    byteKey_table (isByteKey_of_selByte hsel), hserv.1]

/-- `LTU`: the occurrence a served key names maps back to that key. -/
theorem ltu_round (k : LookupKey) (m : ℕ)
    (hsel : selByte 4 k = true) (hserv : ByteServable k) :
    ltuAccess (byteEntryOfKey k m) = accessAt k (m : ℤ) := by
  simp only [ByteServable, cell_zero_of_selByte hsel] at hserv
  rw [ltuAccess, byteEntryOfKey, accessAt, byteKey_kind (isByteKey_of_selByte hsel),
    byteKey_table (isByteKey_of_selByte hsel), hserv.1]

/-- `Range` at one width: same round trip, with the width read out of the key's third cell. -/
theorem range_round (width : RangeChip.Width) (k : LookupKey) (m : ℕ)
    (hsel : selRange width k = true) (hserv : ByteServable k) :
    rangeAccess width (rangeEntryOfKey k m) = accessAt k (m : ℤ) := by
  simp only [selRange, Bool.and_eq_true, decide_eq_true_eq] at hsel
  obtain ⟨hbyte, hzero, hwidth⟩ := hsel
  simp only [ByteServable, hzero] at hserv
  rw [rangeAccess, rangeEntryOfKey, accessAt, byteKey_kind hbyte, byteKey_table hbyte,
    hserv.1, hwidth]

/-! ## `Program`

The wide family. Its key carries the fetch address and the two 64-bit operand slots already limbed,
so serving it means reassembling them and checking the limbs really are limbs.
-/

/-- A key entry of sixteen cells is its own cell list. -/
theorem cells_eq_sixteen {k : LookupKey} (h : k.2.2.length = 16) :
    k.2.2 = [cell k 0, cell k 1, cell k 2, cell k 3, cell k 4, cell k 5, cell k 6, cell k 7, cell k 8, cell k 9, cell k 10, cell k 11, cell k 12, cell k 13, cell k 14, cell k 15] := by
  obtain ⟨kind, name, l⟩ := k
  simp only [cell] at h ⊢
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15], _ => rfl

/-- A Program key an honest ROM provider can supply: its pc and operand limbs really are 16-bit
limbs, and the five cells the provider passes through unchecked fit the field's headroom. -/
def ProgramServable (k : LookupKey) : Prop :=
  (cell k 0 < 2 ^ 16 ∧
    cell k 1 < 2 ^ 16 ∧
    cell k 2 < 2 ^ 16 ∧
    cell k 5 < 2 ^ 16 ∧
    cell k 6 < 2 ^ 16 ∧
    cell k 7 < 2 ^ 16 ∧
    cell k 8 < 2 ^ 16 ∧
    cell k 9 < 2 ^ 16 ∧
    cell k 10 < 2 ^ 16 ∧
    cell k 11 < 2 ^ 16 ∧
    cell k 12 < 2 ^ 16) ∧
    (cell k 3 < 2 ^ 24 ∧ cell k 4 < 2 ^ 24 ∧ cell k 13 < 2 ^ 24 ∧ cell k 14 < 2 ^ 24 ∧ cell k 15 < 2 ^ 24)

theorem programKey_kind {k : LookupKey} (h : IsProgramKey k = true) :
    k.1 = InteractionKind.Program := by
  simp only [IsProgramKey, decide_eq_true_eq] at h
  exact h.1

theorem programKey_table {k : LookupKey} (h : IsProgramKey k = true) : k.2.1 = "SP1Program" := by
  simp only [IsProgramKey, decide_eq_true_eq] at h
  exact h.2.1

theorem programKey_length {k : LookupKey} (h : IsProgramKey k = true) : k.2.2.length = 16 := by
  simp only [IsProgramKey, decide_eq_true_eq] at h
  exact h.2.2

/-- Three 16-bit limbs recover the pc they were split from. -/
theorem pcLimbs {a b c : ℕ} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) (hc : c < 2 ^ 16) :
    (a + 2 ^ 16 * b + 2 ^ 32 * c) % 2 ^ 16 = a ∧
      (a + 2 ^ 16 * b + 2 ^ 32 * c) / 2 ^ 16 % 2 ^ 16 = b ∧
      (a + 2 ^ 16 * b + 2 ^ 32 * c) / 2 ^ 32 % 2 ^ 16 = c :=
  ⟨by omega, by omega, by omega⟩

/-- Four 16-bit limbs recover the 64-bit operand slot they were split from. -/
theorem wordLimbs {a b c d : ℕ} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) (hc : c < 2 ^ 16)
    (hd : d < 2 ^ 16) :
    (a + 2 ^ 16 * b + 2 ^ 32 * c + 2 ^ 48 * d) % 2 ^ 16 = a ∧
      (a + 2 ^ 16 * b + 2 ^ 32 * c + 2 ^ 48 * d) / 2 ^ 16 % 2 ^ 16 = b ∧
      (a + 2 ^ 16 * b + 2 ^ 32 * c + 2 ^ 48 * d) / 2 ^ 32 % 2 ^ 16 = c ∧
      (a + 2 ^ 16 * b + 2 ^ 32 * c + 2 ^ 48 * d) / 2 ^ 48 % 2 ^ 16 = d :=
  ⟨by omega, by omega, by omega, by omega⟩

/-- `Program`: the committed entry a served key names maps back to that key. -/
theorem program_round (k : LookupKey) (m : ℕ)
    (hsel : IsProgramKey k = true) (hserv : ProgramServable k) :
    programEntryAccess (romEntryOfKey k m) = accessAt k (m : ℤ) := by
  obtain ⟨⟨h0, h1, h2, h5, h6, h7, h8, h9, h10, h11, h12⟩, _⟩ := hserv
  obtain ⟨p0, p1, p2⟩ := pcLimbs h0 h1 h2
  obtain ⟨b0, b1, b2, b3⟩ := wordLimbs h5 h6 h7 h8
  obtain ⟨c0, c1, c2, c3⟩ := wordLimbs h9 h10 h11 h12
  simp only [programEntryAccess, romEntryOfKey, accessAt, programKey_kind hsel,
    programKey_table hsel, cells_eq_sixteen (programKey_length hsel),
    p0, p1, p2, b0, b1, b2, b3, c0, c1, c2, c3]


namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-! ## The entry lists a shard's demand determines -/

/-- The keys this trace's consumers demand, on the buses a preprocessed provider may supply. -/
def closingKeyList : List LookupKey :=
  closingKeys trace.skeletonLedger preprocessedKey

/-- The `U8Range` occurrences the shard's demand determines. -/
def closureU8RangeEntries : List TraceGen.ByteEntry :=
  (trace.closingKeyList.filter (selByte 3)).map fun k => byteEntryOfKey k (trace.providerDemand k)

/-- The `Msb` occurrences the shard's demand determines. -/
def closureMsbEntries : List TraceGen.ByteEntry :=
  (trace.closingKeyList.filter (selByte 5)).map fun k => byteEntryOfKey k (trace.providerDemand k)

/-- The `AndByte` occurrences the shard's demand determines. -/
def closureAndByteEntries : List TraceGen.ByteEntry :=
  (trace.closingKeyList.filter (selByte 0)).map fun k => byteEntryOfKey k (trace.providerDemand k)

/-- The `OrByte` occurrences the shard's demand determines. -/
def closureOrByteEntries : List TraceGen.ByteEntry :=
  (trace.closingKeyList.filter (selByte 1)).map fun k => byteEntryOfKey k (trace.providerDemand k)

/-- The `XorByte` occurrences the shard's demand determines. -/
def closureXorByteEntries : List TraceGen.ByteEntry :=
  (trace.closingKeyList.filter (selByte 2)).map fun k => byteEntryOfKey k (trace.providerDemand k)

/-- The `Ltu` occurrences the shard's demand determines. -/
def closureLtuEntries : List TraceGen.ByteEntry :=
  (trace.closingKeyList.filter (selByte 4)).map fun k => byteEntryOfKey k (trace.providerDemand k)

/-- The range occurrences at one width the shard's demand determines. -/
def closureRangeEntries (width : RangeChip.Width) : List TraceGen.RangeEntry :=
  (trace.closingKeyList.filter (selRange width)).map fun k =>
    rangeEntryOfKey k (trace.providerDemand k)

/-- The committed ROM entries the shard's demand determines. -/
def closureRomEntries : List TraceGen.RomEntry :=
  (trace.closingKeyList.filter IsProgramKey).map fun k => romEntryOfKey k (trace.providerDemand k)

/-- **A trace whose provider occurrence lists are the ones its own demand determines.**

Not a constraint on the shard: it is what an honest trace generator produces, since the only
multiplicity that can balance a key is that key's recount. Stating it as a predicate rather than
rebuilding the record keeps `SupportedCoreTraceWitness` and every existing construction of it
untouched. -/
structure ClosureRealized : Prop where
  u8Range : trace.u8RangeEntries = trace.closureU8RangeEntries
  msb : trace.msbEntries = trace.closureMsbEntries
  andByte : trace.andByteEntries = trace.closureAndByteEntries
  orByte : trace.orByteEntries = trace.closureOrByteEntries
  xorByte : trace.xorByteEntries = trace.closureXorByteEntries
  ltu : trace.ltuEntries = trace.closureLtuEntries
  range : ∀ width, trace.rangeEntries width = trace.closureRangeEntries width
  rom : trace.romEntries = trace.closureRomEntries

/-- **Every key the shard demands is one an honest provider can supply.**

The real completeness premise. A satisfied consumer row's byte pull carries the value that row's
own circuit computed, which is the value the provider recomputes — so any trace that actually
satisfies the AIR meets this. A trace that does not is genuinely uncompletable: no provider row
exists at a key claiming `3 AND 3 = 5`. -/
structure DemandServable : Prop where
  byte : ∀ k ∈ trace.closingKeyList, k.1 = InteractionKind.Byte →
    IsByteKey k = true ∧ ByteServable k
  program : ∀ k ∈ trace.closingKeyList, k.1 = InteractionKind.Program →
    IsProgramKey k = true ∧ ProgramServable k

/-- A demanded key is on one of the two buses a preprocessed provider supplies. -/
theorem kind_of_mem_closingKeyList {k : LookupKey} (hk : k ∈ trace.closingKeyList) :
    k.1 = InteractionKind.Byte ∨ k.1 = InteractionKind.Program := by
  have := LookupAccessList.select_of_mem_closingKeys hk
  simp only [preprocessedKey] at this
  cases hkind : k.1 <;> rw [hkind] at this <;> simp at this ⊢

end SupportedCoreTraceWitness


/-! ## Each family's contribution

One `family_multiplicitySum` per family: it supplies exactly the demanded multiplicity at the keys
it serves, and nothing anywhere else.
-/

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

theorem closureU8Range_contribution (hserv : trace.DemandServable) (k : LookupKey) :
    multiplicitySum (trace.closureU8RangeEntries.map u8RangeAccess) k =
      if k ∈ trace.closingKeyList ∧ selByte 3 k = true then (trace.providerDemand k : ℤ)
      else 0 :=
  family_multiplicitySum trace.skeletonLedger (LookupAccessList.closingKeys_nodup _ _)
    (selByte 3) byteEntryOfKey u8RangeAccess
    (fun key hk hsel => u8Range_round key _ hsel
      (hserv.byte key hk (byteKey_kind (isByteKey_of_selByte hsel))).2) k

theorem closureMsb_contribution (hserv : trace.DemandServable) (k : LookupKey) :
    multiplicitySum (trace.closureMsbEntries.map msbAccess) k =
      if k ∈ trace.closingKeyList ∧ selByte 5 k = true then (trace.providerDemand k : ℤ)
      else 0 :=
  family_multiplicitySum trace.skeletonLedger (LookupAccessList.closingKeys_nodup _ _)
    (selByte 5) byteEntryOfKey msbAccess
    (fun key hk hsel => msb_round key _ hsel
      (hserv.byte key hk (byteKey_kind (isByteKey_of_selByte hsel))).2) k

theorem closureAndByte_contribution (hserv : trace.DemandServable) (k : LookupKey) :
    multiplicitySum (trace.closureAndByteEntries.map andAccess) k =
      if k ∈ trace.closingKeyList ∧ selByte 0 k = true then (trace.providerDemand k : ℤ)
      else 0 :=
  family_multiplicitySum trace.skeletonLedger (LookupAccessList.closingKeys_nodup _ _)
    (selByte 0) byteEntryOfKey andAccess
    (fun key hk hsel => and_round key _ hsel
      (hserv.byte key hk (byteKey_kind (isByteKey_of_selByte hsel))).2) k

theorem closureOrByte_contribution (hserv : trace.DemandServable) (k : LookupKey) :
    multiplicitySum (trace.closureOrByteEntries.map orAccess) k =
      if k ∈ trace.closingKeyList ∧ selByte 1 k = true then (trace.providerDemand k : ℤ)
      else 0 :=
  family_multiplicitySum trace.skeletonLedger (LookupAccessList.closingKeys_nodup _ _)
    (selByte 1) byteEntryOfKey orAccess
    (fun key hk hsel => or_round key _ hsel
      (hserv.byte key hk (byteKey_kind (isByteKey_of_selByte hsel))).2) k

theorem closureXorByte_contribution (hserv : trace.DemandServable) (k : LookupKey) :
    multiplicitySum (trace.closureXorByteEntries.map xorAccess) k =
      if k ∈ trace.closingKeyList ∧ selByte 2 k = true then (trace.providerDemand k : ℤ)
      else 0 :=
  family_multiplicitySum trace.skeletonLedger (LookupAccessList.closingKeys_nodup _ _)
    (selByte 2) byteEntryOfKey xorAccess
    (fun key hk hsel => xor_round key _ hsel
      (hserv.byte key hk (byteKey_kind (isByteKey_of_selByte hsel))).2) k

theorem closureLtu_contribution (hserv : trace.DemandServable) (k : LookupKey) :
    multiplicitySum (trace.closureLtuEntries.map ltuAccess) k =
      if k ∈ trace.closingKeyList ∧ selByte 4 k = true then (trace.providerDemand k : ℤ)
      else 0 :=
  family_multiplicitySum trace.skeletonLedger (LookupAccessList.closingKeys_nodup _ _)
    (selByte 4) byteEntryOfKey ltuAccess
    (fun key hk hsel => ltu_round key _ hsel
      (hserv.byte key hk (byteKey_kind (isByteKey_of_selByte hsel))).2) k

theorem closureRange_contributionAt (hserv : trace.DemandServable)
    (width : RangeChip.Width) (k : LookupKey) :
    multiplicitySum ((trace.closureRangeEntries width).map (rangeAccess width)) k =
      if k ∈ trace.closingKeyList ∧ selRange width k = true then (trace.providerDemand k : ℤ)
      else 0 :=
  family_multiplicitySum trace.skeletonLedger (LookupAccessList.closingKeys_nodup _ _)
    (selRange width) rangeEntryOfKey (rangeAccess width)
    (fun key hk hsel => range_round width key _ hsel
      (hserv.byte key hk (byteKey_kind (by
        simp only [selRange, Bool.and_eq_true] at hsel
        exact hsel.1))).2) k

theorem closureRom_contribution (hserv : trace.DemandServable) (k : LookupKey) :
    multiplicitySum (trace.closureRomEntries.map programEntryAccess) k =
      if k ∈ trace.closingKeyList ∧ IsProgramKey k = true then (trace.providerDemand k : ℤ)
      else 0 :=
  family_multiplicitySum trace.skeletonLedger (LookupAccessList.closingKeys_nodup _ _)
    IsProgramKey romEntryOfKey programEntryAccess
    (fun key hk hsel => program_round key _ hsel
      (hserv.program key hk (programKey_kind hsel)).2) k

end SupportedCoreTraceWitness


/-! ## The range family across all seventeen widths

The one family that is a *list* of tables. A range key names its own width in its third cell, so
exactly one of the seventeen serves it; the sum over widths collapses to that one.
-/

/-- A `Nodup` list's indicator sum picks out its single hit. -/
theorem sum_map_ite_eq_of_mem {α : Type*} [DecidableEq α] {l : List α} (hnd : l.Nodup)
    {a : α} (ha : a ∈ l) (r : ℤ) : (l.map fun x => if x = a then r else 0).sum = r := by
  induction l with
  | nil => cases ha
  | cons head tail ih =>
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnd
      rw [List.map_cons, List.sum_cons]
      by_cases hha : head = a
      · subst hha
        have hzero : (tail.map fun x => if x = head then r else 0).sum = 0 := by
          refine List.sum_eq_zero fun z hz => ?_
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
          refine if_neg fun hxa => hhead ?_
          rwa [hxa] at hx
        rw [if_pos rfl, hzero, add_zero]
      · rw [if_neg hha, zero_add]
        exact ih htail ((List.mem_cons.mp ha).resolve_left fun h => hha h.symm)

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-- **The seventeen range tables together supply exactly the range keys**, each at the one width
its own third cell names. -/
theorem closureRange_contribution (hserv : trace.DemandServable) (k : LookupKey) :
    multiplicitySum (RangeChip.allWidths.flatMap fun width =>
        (trace.closureRangeEntries width).map (rangeAccess width)) k =
      if k ∈ trace.closingKeyList ∧ IsByteKey k = true ∧ cell k 0 = 6 ∧ cell k 2 < 17
        then (trace.providerDemand k : ℤ) else 0 := by
  rw [LookupAccessList.multiplicitySum_flatMap]
  simp only [closureRange_contributionAt trace hserv]
  by_cases hc : k ∈ trace.closingKeyList ∧ IsByteKey k = true ∧ cell k 0 = 6 ∧ cell k 2 < 17
  · obtain ⟨hk, hbyte, h0, h2⟩ := hc
    rw [if_pos ⟨hk, hbyte, h0, h2⟩]
    have hconv : ∀ width : RangeChip.Width,
        (if k ∈ trace.closingKeyList ∧ selRange width k = true
          then (trace.providerDemand k : ℤ) else 0) =
          if width = (⟨cell k 2, h2⟩ : RangeChip.Width) then (trace.providerDemand k : ℤ)
          else 0 := by
      intro width
      by_cases hw : width = (⟨cell k 2, h2⟩ : RangeChip.Width)
      · subst hw
        have hsel : selRange (⟨cell k 2, h2⟩ : RangeChip.Width) k = true := by
          simp [selRange, hbyte, h0]
        rw [if_pos ⟨hk, hsel⟩, if_pos rfl]
      · refine (if_neg ?_).trans (if_neg hw).symm
        rintro ⟨-, hsel⟩
        simp only [selRange, Bool.and_eq_true, decide_eq_true_eq] at hsel
        exact hw (Fin.ext hsel.2.2.symm)
    rw [List.map_congr_left fun width _ => hconv width, RangeChip.allWidths]
    exact sum_map_ite_eq_of_mem (List.nodup_finRange 17) (List.mem_finRange _) _
  · rw [if_neg hc]
    refine List.sum_eq_zero fun z hz => ?_
    obtain ⟨width, -, rfl⟩ := List.mem_map.mp hz
    refine if_neg fun h => hc ⟨h.1, ?_⟩
    simp only [selRange, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.2.1, h.2.2.1, h.2.2.2 ▸ width.isLt⟩

end SupportedCoreTraceWitness


/-! ## The closure is realized

The eight contributions add up to the closure, so a trace whose provider lists are the ones its own
demand determines supplies exactly `closingAccesses` — and Byte/Program balance follows from
`closingAccesses_balances` with no per-shard evaluation.
-/

theorem selByte_eq_true_iff {s : ℕ} {k : LookupKey} :
    selByte s k = true ↔ IsByteKey k = true ∧ cell k 0 = s := by
  simp only [selByte, Bool.and_eq_true, decide_eq_true_eq]

theorem isProgramKey_false_of_isByteKey {k : LookupKey} (h : IsByteKey k = true) :
    IsProgramKey k = false := by
  simp only [IsProgramKey, decide_eq_false_iff_not, not_and]
  intro hkind
  exact absurd (byteKey_kind h) (by rw [hkind]; simp)

theorem isByteKey_false_of_isProgramKey {k : LookupKey} (h : IsProgramKey k = true) :
    IsByteKey k = false := by
  simp only [IsByteKey, decide_eq_false_iff_not, not_and]
  intro hkind
  exact absurd (programKey_kind h) (by rw [hkind]; simp)

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-- **The provider ledger a realized trace supplies is the closure**, key by key. -/
theorem providerLedger_multiplicitySum (hreal : trace.ClosureRealized)
    (hserv : trace.DemandServable) (k : LookupKey) :
    multiplicitySum trace.providerLedger k =
      if k ∈ trace.closingKeyList then (trace.providerDemand k : ℤ) else 0 := by
  rw [providerLedger, hreal.u8Range, hreal.msb, hreal.andByte, hreal.orByte, hreal.xorByte,
    hreal.ltu, hreal.rom]
  simp only [hreal.range, LookupAccessList.multiplicitySum_append,
    closureU8Range_contribution trace hserv, closureMsb_contribution trace hserv,
    closureAndByte_contribution trace hserv, closureOrByte_contribution trace hserv,
    closureXorByte_contribution trace hserv, closureLtu_contribution trace hserv,
    closureRange_contribution trace hserv, closureRom_contribution trace hserv]
  by_cases hk : k ∈ trace.closingKeyList
  · rw [if_pos hk]
    rcases trace.kind_of_mem_closingKeyList hk with hkind | hkind
    · obtain ⟨hbyte, hserve⟩ := hserv.byte k hk hkind
      have hprog : IsProgramKey k = false := isProgramKey_false_of_isByteKey hbyte
      rcases hb : cell k 0 with _ | _ | _ | _ | _ | _ | _ | n
      · simp [hk, selByte_eq_true_iff, hbyte, hb, hprog]
      · simp [hk, selByte_eq_true_iff, hbyte, hb, hprog]
      · simp [hk, selByte_eq_true_iff, hbyte, hb, hprog]
      · simp [hk, selByte_eq_true_iff, hbyte, hb, hprog]
      · simp [hk, selByte_eq_true_iff, hbyte, hb, hprog]
      · simp [hk, selByte_eq_true_iff, hbyte, hb, hprog]
      · simp only [ByteServable, hb] at hserve
        have hwidth : cell k 2 < 17 := by omega
        simp [hk, selByte_eq_true_iff, hbyte, hb, hprog, hwidth]
      · simp only [ByteServable, hb] at hserve
    · obtain ⟨hprog, -⟩ := hserv.program k hk hkind
      have hbyte : IsByteKey k = false := isByteKey_false_of_isProgramKey hprog
      simp [hk, selByte_eq_true_iff, hbyte, hprog]
  · simp [hk]


/-! ## The payoff: Byte and Program balance without evaluating a shard -/

/-- The trace's whole Clean ledger: the verifier row plus all 53 tables. -/
def fullLedger : LookupAccessList :=
  tableCleanAccesses trace.skeletonVerifierTable ++ tablesCleanAccesses trace.tables

/-- The assembled table list really is the skeleton's two pieces with the provider window between
them. -/
theorem tables_split :
    trace.tables =
      trace.tables.take instructionTableCount ++ trace.preprocessedProviderTables ++
        trace.tables.drop (instructionTableCount + preprocessedProviderTableCount) := by
  exact List.take_append_take_drop_append_drop trace.tables instructionTableCount
    preprocessedProviderTableCount

/-- Splitting the ledger the ensemble actually sees into the consumer skeleton and the provider
window: the same accesses, in a different order, so every per-key sum agrees. -/
theorem fullLedger_multiplicitySum (hwf : trace.WellFormed) (hfit : trace.CountsFit)
    (k : LookupKey) :
    multiplicitySum trace.fullLedger k =
      multiplicitySum (trace.skeletonLedger ++ trace.providerLedger) k := by
  rw [fullLedger, skeletonLedger_eq, trace.preprocessedProviderLedger_eq hwf hfit |>.symm]
  conv_lhs => rw [tables_split trace]
  simp only [tablesCleanAccesses_append, LookupAccessList.multiplicitySum_append]
  ring

/-- **Byte and Program balance, for a realized trace.**

The theorem this whole file exists for: given only that the shard's demand is servable and that no
consumer key is already net-supplied, the ledger the ensemble sees cancels on both preprocessed
buses. No compiled evaluation, no concrete shard. State and Memory are untouched and remain
explicit — `closingAccesses_state` / `closingAccesses_memory` record that. -/
theorem byteProgram_balanced (hwf : trace.WellFormed) (hfit : trace.CountsFit)
    (hreal : trace.ClosureRealized) (hserv : trace.DemandServable)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      multiplicitySum trace.skeletonLedger key ≤ 0)
    {k : LookupKey} (hsel : preprocessedKey k = true) :
    multiplicitySum trace.fullLedger k = 0 := by
  rw [fullLedger_multiplicitySum trace hwf hfit,
    LookupAccessList.multiplicitySum_append,
    providerLedger_multiplicitySum trace hreal hserv]
  by_cases hk : k ∈ trace.closingKeyList
  · rw [if_pos hk]
    have hbal := trace.closingAccesses_balances hnonpos hsel
    rw [LookupAccessList.multiplicitySum_append, closingAccesses,
      LookupAccessList.multiplicitySum_closingAccesses _
        (LookupAccessList.closingKeys_nodup _ _) hk] at hbal
    exact hbal
  · rw [if_neg hk, add_zero]
    have hk' : k ∉ LookupAccessList.closingKeys trace.skeletonLedger preprocessedKey := hk
    have hbal := trace.closingAccesses_balances hnonpos hsel
    rw [LookupAccessList.multiplicitySum_append, closingAccesses,
      LookupAccessList.multiplicitySum_closingAccesses_of_not_mem _ hk', add_zero] at hbal
    exact hbal


/-! ## From the whole ledger to one channel's

`byteProgram_balanced` is about `fullLedger` — every table's accesses at once.
`AIRCompleteness.lean`'s `BalancedOn` is about one channel's evaluated interactions. Both are
`multiplicitySum` over a `LookupAccessList`, and `tableCleanAccesses` projects through the very same
`Interaction.toAccess`, so what separates them is orientation, not vocabulary.

The bridge is that a key already names its channel: `Interaction.toAccess` puts the emitting
channel's `name` in the key's table slot. Given that the ensemble's tables speak only on the
ensemble's channels (`sp1Ensemble_allTables_channels_subset`) and that those four names are
distinct (`channel_eq_of_name_eq`), an access landing on a key with `channel.name` can only have
come from `channel` — so filtering to that channel drops nothing the key could see.
-/

/-- The assembled witness's tables are the ensemble's components — verifier row included. -/
theorem allTables_component_mem (table : Table (ZMod p)) (h : table ∈ trace.witness.allTables) :
    table.component ∈ (sp1Ensemble (p := p)).allTables := by
  rw [Air.Flat.EnsembleWitness.allTables, List.mem_cons] at h
  rw [Air.Flat.Ensemble.allTables, List.mem_cons]
  rcases h with rfl | h
  · exact Or.inl rfl
  · refine Or.inr ?_
    rw [← trace.tables_map_component]
    exact List.mem_map_of_mem (by rwa [witness_tables] at h)

/-- The whole ledger is every table's ledger, verifier row included. -/
theorem tablesCleanAccesses_allTables :
    tablesCleanAccesses trace.witness.allTables = trace.fullLedger := by
  rw [Air.Flat.EnsembleWitness.allTables, tablesCleanAccesses, List.flatMap_cons,
    witness_verifierTable, witness_tables, fullLedger, skeletonVerifierTable, tablesCleanAccesses]

/-- **One channel's ledger and the whole ledger agree at every key that channel could produce.** -/
theorem fullLedger_multiplicitySum_channel (channel : RawChannel (ZMod p))
    (hchannel : channel ∈ (sp1Ensemble (p := p)).channels)
    {k : LookupKey} (hname : k.2.1 = channel.name) :
    multiplicitySum ((trace.witness.interactionsWith channel).map Interaction.toAccess) k =
      multiplicitySum trace.fullLedger k := by
  have hlhs : (trace.witness.interactionsWith channel).map Interaction.toAccess =
      trace.witness.allTables.flatMap
        fun table => (table.interactionsWith channel).map Interaction.toAccess := by
    rw [Air.Flat.EnsembleWitness.interactionsWith, List.map_flatMap]
  rw [hlhs, ← trace.tablesCleanAccesses_allTables, tablesCleanAccesses,
    LookupAccessList.multiplicitySum_flatMap, LookupAccessList.multiplicitySum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun table htable => ?_)
  refine multiplicitySum_interactionsWith_eq table channel fun i hi hkey => ?_
  refine channel_eq_of_name_eq ?_ hchannel ?_
  · exact sp1Ensemble_allTables_channels_subset _
      (trace.allTables_component_mem table htable)
      (Air.Flat.Table.channel_mem_channels_of_mem_interactions table i hi)
  · rw [channel_name_of_keyOf_toAccess hkey, hname]


/-- Every access in one channel's ledger carries that channel's kind and name — because
`Interaction.toAccess` reads both off the emitting channel, and a channel-filtered list emits only
on that channel. -/
theorem keyOf_mem_channelLedger (channel : RawChannel (ZMod p)) {a : LookupAccess}
    (ha : a ∈ (trace.witness.interactionsWith channel).map Interaction.toAccess) :
    (LookupAccessList.keyOf a).1 = kindOf channel.name ∧
      (LookupAccessList.keyOf a).2.1 = channel.name := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  have hchannel : i.channel = channel :=
    Air.Flat.EnsembleWitness.channel_eq_of_mem_interactionsWith hi
  rw [← hchannel]
  exact ⟨rfl, rfl⟩

/-- **A preprocessed bus's ledger balances at every key.**

The `isConsistentBalanced` half of `AIRCompleteness.lean`'s `BalancedOn`, for the two channels a
provider closure can supply. Keys of the wrong kind or table name are vacuous; keys of the right
shape go through the orientation bridge to `byteProgram_balanced`. -/
theorem channelLedger_isConsistentBalanced (hwf : trace.WellFormed) (hfit : trace.CountsFit)
    (hreal : trace.ClosureRealized) (hserv : trace.DemandServable)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      multiplicitySum trace.skeletonLedger key ≤ 0)
    (channel : RawChannel (ZMod p))
    (hchannel : channel ∈ (sp1Ensemble (p := p)).channels)
    (hkind : kindOf channel.name = InteractionKind.Byte ∨
      kindOf channel.name = InteractionKind.Program) :
    LookupAccessList.isConsistentBalanced
      ((trace.witness.interactionsWith channel).map Interaction.toAccess) := by
  intro k
  by_cases hname : k.2.1 = channel.name
  · by_cases hkey : k.1 = kindOf channel.name
    · rw [trace.fullLedger_multiplicitySum_channel channel hchannel hname]
      refine trace.byteProgram_balanced hwf hfit hreal hserv hnonpos ?_
      rw [preprocessedKey, hkey]
      rcases hkind with h | h <;> rw [h]
    · exact LookupAccessList.multiplicitySum_eq_zero_of_keyOf_ne fun a ha hka =>
        hkey (by rw [← hka]; exact (trace.keyOf_mem_channelLedger channel ha).1)
  · exact LookupAccessList.multiplicitySum_eq_zero_of_keyOf_ne fun a ha hka =>
        hname (by rw [← hka]; exact (trace.keyOf_mem_channelLedger channel ha).2)

end SupportedCoreTraceWitness

end SP1Clean.Soundness
