import SP1Clean.Model.SP1Constraint
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Lookup
import Clean.Circuit.Provable
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import Mathlib.Tactic.IntervalCases

/-! # The static byte-lookup table (SP1's preprocessed `ByteChip`, as a Clean `Table`)

SP1's `ByteChip` (`crates/core/machine/src/bytes/`) is a **preprocessed** table whose rows are fixed,
generated once independent of the program. It covers the six byte opcodes
(`AND`/`OR`/`XOR`/`U8Range`/`LTU`/`MSB`, `byte_table()` in `events/byte.rs`); every chip that needs a
byte operation does **not** range-check in-circuit but instead `send_byte(opcode, a, b, c, mult)` into
the Byte bus, and the `ByteChip` *receives* each with a count multiplicity.

This module is the Lean analog of that preprocessed table, modelled on Clean's own `ByteXorTable`
(`Clean/Tables/Xor/ByteXorTable.lean`): a `Table` whose membership is a **defining `Contains`
predicate**, not an enumeration of all `7 * 2^16` rows — so there is no `decide` over a giant table and
the well-formedness obligations are two-line. The defining predicate is exactly SP1's per-opcode byte
semantics, `ByteOpcode.constrain` (`Foundations/SP1Constraint.lean`), keyed by the opcode column. A
consuming circuit emits a lookup with `Circuit.lookup ByteTable ⟨opcode, a, b, c⟩` (the in-circuit half
of `send_byte`); the matching Byte `Channel` (`Foundations/Channels.lean`) carries the multiplicity for
the trace-level multiset balance against the `ByteChip` receiver. -/

namespace SP1Clean

open SP1Clean (ByteOpcode)

namespace ByteOpcode

/-- The opcode's table index as a `ℕ` — the inverse of the auto-generated `ofNat`
(AND=0, OR=1, XOR=2, U8Range=3, LTU=4, MSB=5, Range=6), matching SP1's `ByteOpcode` numbering. Used as
the opcode column of a byte-table row. -/
def idx : ByteOpcode → ℕ
  | AND => 0 | OR => 1 | XOR => 2 | U8Range => 3 | LTU => 4 | MSB => 5 | Range => 6

@[simp] lemma ofNat_idx (op : ByteOpcode) : ofNat op.idx = op := by cases op <;> rfl

end ByteOpcode

/-- One byte-table row: the opcode column plus the three operand columns — SP1's
`AirInteraction.byte (op a b c)` shape (arity 4). -/
structure ByteRow (F : Type) where
  opcode : F
  a : F
  b : F
  c : F
deriving ProvableStruct

/-- The byte-table membership predicate: the row is a valid byte-op tuple — some `ByteOpcode` whose
index matches the `opcode` column and whose `constrain` semantics hold on `(a, b, c)`. This *is* SP1's
preprocessed `ByteChip` content, stated semantically. -/
def ByteRowSpec {p : ℕ} [NeZero p] (row : ByteRow (ZMod p)) : Prop :=
  ∃ op : ByteOpcode, ((op.idx : ℕ) : ZMod p) = row.opcode ∧ op.constrain row.a row.b row.c

/-- The static byte table as a Clean `Table` (SP1's preprocessed `ByteChip`). Membership is the
defining `ByteRowSpec`; `Soundness`/`Completeness` are the class defaults (`= Contains`), so the two
well-formedness obligations close by `assumption`, axiom-clean — no enumeration of the `7 * 2^16` rows.
A consumer looks up with `Circuit.lookup ByteTable ⟨opcode, a, b, c⟩`. -/
def ByteTable {p : ℕ} [NeZero p] : Table (ZMod p) ByteRow where
  name := "SP1Byte"
  Contains _ row := ByteRowSpec row

/-! ## Byte range checks via the table (the faithful replacement for `rangeCheck n`)

SP1 does not range-check in-circuit; it `send_byte(op, …)` into the Byte bus, whose provider is the
preprocessed `ByteChip`. SP1's `ByteOpcode` numbers `Range`/`U8Range` among its six table ops, so a
range check *is* a byte-table lookup. The readers use two forms (`Extracted/{CPUState,RTypeReader}`):

- **`Range`** (`send_byte(Range, x, n, 0)`, `Range.constrain a b c := a.val < 2^b.val`) — the `n`-bit
  check used by all three RTypeReader access-timestamp checks (`< 2^16`, `< 2^8`) and CPUState's
  shifted `clk_0_16` (`< 2^13`). Modeled by `byteRangeCheckBits n`.
- **`U8Range`** (`send_byte(U8Range, …)`, all three operands `< 256`) — CPUState's `clk_16_24`.
  Modeled by `byteRangeCheck`.

Each is a `FormalAssertion` mirroring `Gadgets.ToBits.rangeCheck`'s `(n) (hn) (x)` / `(x)` call shape,
so it drops into the reader call sites; its meaning is *table membership* rather than a
bit-decomposition. -/

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- `local` so this convenience instance does not leak into importing files (a global `NeZero p`
-- derived from `Fact (2^17 < p)` would make downstream `omit [Fact (2^17 < p)] in` clauses illegal).
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The opcode indices `0..6` are distinct mod `p` (since `p > 2^17 > 6`): two indices `≤ 6` equal mod
`p` are equal as naturals. The injectivity that lets a row's opcode column pin the `ByteOpcode`. -/
lemma cast_le6_inj {j k : ℕ} (hj : j ≤ 6) (hk : k ≤ 6)
    (h : ((j : ℕ) : ZMod p) = ((k : ℕ) : ZMod p)) : j = k := by
  have h17 := Fact.out (p := 2 ^ 17 < p)
  have hjp : j < p := by omega
  have hkp : k < p := by omega
  have hmod := (ZMod.natCast_eq_natCast_iff j k p).mp h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hjp, Nat.mod_eq_of_lt hkp] at hmod

/-- A `U8Range` byte-table row `⟨3, x, 0, 0⟩` is in the table **iff** `x` is a byte (`x.val < 2^8`).
Forward: `cast_le6_inj` turns the opcode column `= 3` into the *natural* index equation `op.idx = 3`,
which (by cases) forces `op = U8Range` and rules out the other six (`omega` on the false index
equations); then `U8Range.constrain` gives `x.val < 256 = 2^8`. Backward: provide `U8Range`. This is
the byte-bus meaning of the `clk_16_24`-style `< 256` check. -/
lemma byteRowSpec_u8range (x : ZMod p) :
    ByteRowSpec (⟨(3 : ZMod p), x, 0, 0⟩ : ByteRow (ZMod p)) ↔ x.val < 2 ^ 8 := by
  have h256 : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [h256]
  constructor
  · rintro ⟨op, hop, hc⟩
    have hk : op.idx = 3 := cast_le6_inj (by cases op <;> decide) (by norm_num) (by rw [hop]; norm_cast)
    cases op <;> simp only [ByteOpcode.idx] at hk <;>
      first
        | omega
        | (simp only [ByteOpcode.constrain] at hc; exact hc.1)
  · intro hx
    exact ⟨ByteOpcode.U8Range, by norm_cast, ⟨hx, by norm_num, by norm_num⟩⟩

/-- A `Range` byte-table row `⟨6, x, (n : ZMod p), 0⟩` is in the table **iff** `x.val < 2^n`
(`Range.constrain a b c := a.val < 2^b.val`). The `n`-bit check, SP1's `send_byte(Range, x, n, 0)` —
the form the timestamp (`< 2^16`/`< 2^8`) and shifted-clock (`< 2^13`) checks use. Needs `n < p` so the
bit-width column round-trips (`((n:ZMod p)).val = n`). -/
lemma byteRowSpec_range (x : ZMod p) {n : ℕ} (hnp : n < p) :
    ByteRowSpec (⟨(6 : ZMod p), x, ((n : ℕ) : ZMod p), 0⟩ : ByteRow (ZMod p)) ↔ x.val < 2 ^ n := by
  have hvaln : ((n : ℕ) : ZMod p).val = n := ZMod.val_natCast_of_lt hnp
  constructor
  · rintro ⟨op, hop, hc⟩
    have hk : op.idx = 6 := cast_le6_inj (by cases op <;> decide) (by norm_num) (by rw [hop]; norm_cast)
    cases op <;> simp only [ByteOpcode.idx] at hk <;>
      first
        | omega
        | (simp only [ByteOpcode.constrain] at hc; rwa [hvaln] at hc)
  · intro hx
    exact ⟨ByteOpcode.Range, by norm_cast, by simp only [ByteOpcode.constrain, hvaln]; exact hx⟩

omit [Fact p.Prime] in
/-- An AND/OR/XOR byte-table row `⟨op, r, b, c⟩` (dynamic opcode, `op.val < 3`) is in the table
**iff** `b`/`c`/`r` are bytes and `r` is the per-byte `byteOp` of `b`, `c`. This is the byte-bus
meaning of SP1's `send_byte(opcode, result, b, c)` in `bitwise.rs` — the fact `BitwiseOperation`'s
soundness projects through (replacing the `ByteXorTable` + Lagrange-selector algebra). Forward: the
opcode column pins `op.idx = op.val` (`< 7 < p` round-trip), then `cases` on the opcode resolves the
three live arms (`byteOp_{zero,one,two}`) and `omega` rules out `U8Range`/`LTU`/`MSB`/`Range` against
`op.val < 3`. Backward: the witness is `ByteOpcode.ofNat op.val`. -/
lemma byteRowSpec_byteOp {op : ZMod p} (r b c : ZMod p) (hop : op.val < 3) :
    ByteRowSpec (⟨op, r, b, c⟩ : ByteRow (ZMod p)) ↔
      (r.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ r.val = byteOp op.val b.val c.val := by
  have hp : 2 ^ 17 < p := Fact.out
  constructor
  · rintro ⟨o, hidx, hc⟩
    have ho6 : o.idx ≤ 6 := by cases o <;> decide
    have hidxlt : o.idx < p := by omega
    have hidxval : o.idx = op.val := by
      have h := congrArg ZMod.val hidx
      rwa [ZMod.val_natCast_of_lt hidxlt] at h
    cases o <;> simp only [ByteOpcode.idx] at hidxval <;>
      first
        | omega
        | (rw [← hidxval]; simpa only [ByteOpcode.constrain, byteOp_zero, byteOp_one, byteOp_two] using hc)
  · rintro h
    refine ⟨ByteOpcode.ofNat op.val, ?_, ?_⟩
    · have hidx : (ByteOpcode.ofNat op.val).idx = op.val := by interval_cases op.val <;> rfl
      rw [hidx, ZMod.natCast_zmod_val]
    · interval_cases op.val <;>
        simpa only [ByteOpcode.ofNat_zero, ByteOpcode.ofNat_one, ByteOpcode.ofNat_two,
          ByteOpcode.constrain, byteOp_zero, byteOp_one, byteOp_two] using h

/-- A paired `U8Range` byte-table row `⟨3, 0, b, c⟩` is in the table **iff** both `b` and `c` are
bytes (`< 2^8`). SP1's `add_u8_range_check(b, c)` (`u16_operation.rs`, `mul.rs`) range-checks two
bytes per send — so the byte split / product checks pull this form. Proof mirrors
`byteRowSpec_u8range` with the bytes in the `b`/`c` slots. -/
lemma byteRowSpec_u8range_pair (b c : ZMod p) :
    ByteRowSpec (⟨(3 : ZMod p), 0, b, c⟩ : ByteRow (ZMod p)) ↔ (b.val < 2 ^ 8 ∧ c.val < 2 ^ 8) := by
  have h256 : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [h256]
  constructor
  · rintro ⟨op, hop, hc⟩
    have hk : op.idx = 3 := cast_le6_inj (by cases op <;> decide) (by norm_num) (by rw [hop]; norm_cast)
    cases op <;> simp only [ByteOpcode.idx] at hk <;>
      first
        | omega
        | (simp only [ByteOpcode.constrain] at hc; exact ⟨hc.2.1, hc.2.2⟩)
  · rintro ⟨hb, hc⟩
    exact ⟨ByteOpcode.U8Range, by norm_cast, ⟨by simp, hb, hc⟩⟩

/-- An `MSB` byte-table row `⟨5, m, x, 0⟩` is in the table **iff** `m`/`x` are bytes, `m` is binary,
and `m = 1` exactly when `x`'s top bit is set (`128 ≤ x.val`). SP1's `send_byte(MSB, msb, byte, 0)`
in `mul.rs`/signed-Lt sign extraction. Proof mirrors `byteRowSpec_u8range`/`byteRowSpec_range`. -/
lemma byteRowSpec_msb (m x : ZMod p) :
    ByteRowSpec (⟨(5 : ZMod p), m, x, 0⟩ : ByteRow (ZMod p)) ↔
      (m.val < 256 ∧ x.val < 256) ∧ (m = 0 ∨ m = 1) ∧ (m = 1 ↔ 128 ≤ x.val) := by
  constructor
  · rintro ⟨op, hop, hc⟩
    have hk : op.idx = 5 := cast_le6_inj (by cases op <;> decide) (by norm_num) (by rw [hop]; norm_cast)
    cases op <;> simp only [ByteOpcode.idx] at hk <;>
      first
        | omega
        | (simp only [ByteOpcode.constrain] at hc; exact ⟨⟨hc.1.1, hc.1.2.1⟩, hc.2.1, hc.2.2⟩)
  · rintro ⟨⟨hm, hx⟩, hbin, hiff⟩
    exact ⟨ByteOpcode.MSB, by norm_cast, ⟨⟨hm, hx, by simp⟩, hbin, hiff⟩⟩

/-! The in-circuit byte-op correctness is the byte channel's `Guarantees = ByteRowSpec` —
`byteRowSpec_u8range`/`byteRowSpec_range` above are what consumers project the pull guarantee through.
`ByteTable` is the conceptual preprocessed-`ByteChip` analog and the semantic backing for
`byteChannel.Guarantees`. -/

end SP1Clean
