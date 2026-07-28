import SP1Clean.Model.ByteTable
import SP1Clean.Model.InteractionBus

/-! # The `ByteChip` receiver — discharging byte membership from bus balance

SP1's `ByteChip` (`crates/core/machine/src/bytes/`) is the **preprocessed receiver** of the Byte bus:
every consumer `send_byte(op, a, b, c, is_real)`s a byte row, the `ByteChip` *receives* each with a count
multiplicity, and the LogUp argument balances them. Its preprocessed trace contains **only valid byte-op
rows** (`ByteRowSpec`), so a balanced Byte bus forces every real send to be a valid row — which is exactly
what `Soundness/ByteConsistency.lean`'s `TraceByteLink` threads.

This module models the receiver's side of that argument *natively*, shrinking the threaded assumption to
the lone `isConsistentBalanced` (the LogUp/GKR fact Clean cannot model). The receiver is characterized by
the **`ByteRowSpec` predicate**, not the `7 · 2^16`-row enumeration (the `decide` blow-up `ByteTable`
already sidesteps): a `ByteProvider` is any contribution list whose every entry sits at the val-projected
key of some `ByteRowSpec` row. The key fact that makes this work is that a byte key is the *full*
`ZMod.val`-projection of all four fields, so (val injective) **the key determines the row**. -/

namespace SP1Clean.ByteChip

open SP1Clean
open SP1Clean.LookupAccessList

variable {p : ℕ} [NeZero p]

/-- The val-projected Byte-bus key of a byte row — `(.Byte, "SP1Byte", [op.val, a.val, b.val, c.val])`,
the grouping key of the row's `send_byte` (matching `Soundness/ByteConsistency.lean`'s `byteSend`). -/
def byteRowKey (row : ByteRow (ZMod p)) : LookupKey :=
  (.Byte, "SP1Byte", [row.opcode.val, row.a.val, row.b.val, row.c.val])

/-- **The key determines the row.** A byte key is the full `ZMod.val`-projection of all four fields, and
`ZMod.val` is injective (`[NeZero p]`), so two rows with the same key are equal. This is what lets the
provider's *membership* (it carries only valid rows) transfer to the *consumer's* sent row. -/
theorem byteRow_eq_of_key {r1 r2 : ByteRow (ZMod p)} (h : byteRowKey r1 = byteRowKey r2) : r1 = r2 := by
  cases r1; cases r2
  simpa only [byteRowKey, Prod.mk.injEq, List.cons.injEq, and_true, true_and, ByteRow.mk.injEq,
    (ZMod.val_injective p).eq_iff] using h

/-- The **`ByteChip` provider**: any Byte-bus contribution list whose every entry sits at the key of some
valid (`ByteRowSpec`) byte row. This is the native, predicate-characterized content of SP1's preprocessed
`ByteChip` — its trace carries *only* valid byte-op rows (`bytes/trace.rs` generates the 6 ops over all
byte pairs). No enumeration: the property is stated by `ByteRowSpec`, exactly like `ByteTable.Contains`. -/
def ByteProvider (prov : LookupAccessList) : Prop :=
  ∀ b ∈ prov, ∃ row : ByteRow (ZMod p), ByteRowSpec row ∧ keyOf b = byteRowKey row

/-- A byte send whose key a `ByteProvider` carries is a valid byte row. (The provider has a valid row at
that key; the key determines the row, so the sent row *is* that valid row.) -/
theorem byteRowSpec_of_provider {row : ByteRow (ZMod p)} {prov : LookupAccessList}
    (h_prov : ByteProvider (p := p) prov) {b : LookupAccess} (hb : b ∈ prov)
    (hk : keyOf b = byteRowKey row) : ByteRowSpec row := by
  obtain ⟨row', h_spec, h_key⟩ := h_prov b hb
  rw [hk] at h_key
  rwa [byteRow_eq_of_key h_key]

/-! ## The `Range` vs `Byte` receiver split (two preprocessed chips, one Byte bus)

SP1's Byte bus (`InteractionKind.Byte`) is received by **two** preprocessed chips, *both* via
`receive_byte` — there is no separate `Range` interaction kind. `ByteChip` (`bytes/`) covers
`AND`/`OR`/`XOR`/`U8Range`/`LTU`/`MSB`; `RangeChip` (`range/air.rs`: `receive_byte(ByteOpcode::Range,
a, bits, 0, mult)`) covers *only* `Range` (opcode 6). So the `ByteRowSpec` table partitions by opcode:
a row is valid iff it is a valid non-`Range` byte op (the `ByteChip`'s rows) *or* a valid `Range` check
(the `RangeChip`'s rows). The two sub-providers below model that attribution; their union is exactly a
`ByteProvider` (`byteProvider_of_split`), so the single-provider discharge is preserved. -/

/-- A valid `Range` (opcode-6) byte-table row — SP1's `RangeChip` preprocessed content. -/
def RangeRowSpec (row : ByteRow (ZMod p)) : Prop :=
  ((ByteOpcode.Range.idx : ℕ) : ZMod p) = row.opcode ∧ ByteOpcode.Range.constrain row.a row.b row.c

/-- A valid **non-`Range`** byte-op row — SP1's `ByteChip` preprocessed content (it never covers
opcode 6; that is the `RangeChip`'s job). -/
def ByteOpRowSpec (row : ByteRow (ZMod p)) : Prop :=
  ∃ op : ByteOpcode, op ≠ ByteOpcode.Range ∧
    ((op.idx : ℕ) : ZMod p) = row.opcode ∧ op.constrain row.a row.b row.c

/-- **The Byte table is exactly the `ByteChip` rows ⊕ the `RangeChip` rows.** `ByteRowSpec`'s opcode
existential partitions on whether the opcode is `Range`. -/
theorem byteRowSpec_iff (row : ByteRow (ZMod p)) :
    ByteRowSpec row ↔ ByteOpRowSpec row ∨ RangeRowSpec row := by
  constructor
  · rintro ⟨op, ho, hc⟩
    by_cases hr : op = ByteOpcode.Range
    · exact Or.inr ⟨hr ▸ ho, hr ▸ hc⟩
    · exact Or.inl ⟨op, hr, ho, hc⟩
  · rintro (⟨op, _, ho, hc⟩ | ⟨ho, hc⟩)
    · exact ⟨op, ho, hc⟩
    · exact ⟨ByteOpcode.Range, ho, hc⟩

theorem byteRowSpec_of_byteOpRowSpec {row : ByteRow (ZMod p)} (h : ByteOpRowSpec row) :
    ByteRowSpec row := (byteRowSpec_iff row).mpr (Or.inl h)

theorem byteRowSpec_of_rangeRowSpec {row : ByteRow (ZMod p)} (h : RangeRowSpec row) :
    ByteRowSpec row := (byteRowSpec_iff row).mpr (Or.inr h)

/-- SP1's `RangeChip`: a Byte-bus contribution list carrying only valid `Range` (opcode-6) rows. -/
def RangeProvider (prov : LookupAccessList) : Prop :=
  ∀ b ∈ prov, ∃ row : ByteRow (ZMod p), RangeRowSpec row ∧ keyOf b = byteRowKey row

/-- SP1's `ByteChip` (the non-`Range` half): a Byte-bus contribution list carrying only valid non-`Range`
byte-op rows. -/
def ByteOpProvider (prov : LookupAccessList) : Prop :=
  ∀ b ∈ prov, ∃ row : ByteRow (ZMod p), ByteOpRowSpec row ∧ keyOf b = byteRowKey row

/-- **The two receivers' union is a `ByteProvider`.** Appending SP1's `ByteChip` and `RangeChip`
contribution lists yields a list every entry of which sits at a valid `ByteRowSpec` key — so the
single-provider byte-bus discharge applies unchanged to the faithful two-chip receiver. -/
theorem byteProvider_of_split {byteOpProv rangeProv : LookupAccessList}
    (h_byte : ByteOpProvider (p := p) byteOpProv) (h_range : RangeProvider (p := p) rangeProv) :
    ByteProvider (p := p) (byteOpProv ++ rangeProv) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨row, hspec, hk⟩ := h_byte b hb
    exact ⟨row, byteRowSpec_of_byteOpRowSpec hspec, hk⟩
  · obtain ⟨row, hspec, hk⟩ := h_range b hb
    exact ⟨row, byteRowSpec_of_rangeRowSpec hspec, hk⟩

end SP1Clean.ByteChip
