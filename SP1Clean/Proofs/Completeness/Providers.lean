import SP1Clean.Proofs.Completeness.ProviderWitgen
import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Soundness.SP1Ensemble
import ToClean.Air.TableBuild

/-! # From provider occurrences to valid AIR tables

The provider-segment counterpart of the twenty-five `Proofs/Chips/<Chip>/Complete.lean` files: for
each entry of `sp1ProviderTables` (`Soundness/SP1Ensemble.lean`) and for the ensemble verifier row,
a semantic input type, a total builder into the component's `Inputs`, the honest-prover contract on
a built row, and the three `Air.Flat.Table.build` theorems (`Constraints`, `Guarantees`, and the
closed form of the per-channel interaction list).

## Where the builders live

The chips' builders sit on the audit surface (`FormalModel/TraceGen/`) because the chips' `Inputs`
and `Spec`s do (`FormalModel/Contracts/Chips.lean`). The provider `Inputs` types do **not**: the six
`ByteChip` opcode providers and the `RangeChip` family declare theirs inside their own
`Proofs/Chips/` modules, so a `FormalModel/TraceGen/Providers.lean` would have to import `Proofs/`
and invert the layering. The builders therefore live here, beside the theorems that consume them,
until the "Spec homing" backlog item moves the provider contracts onto the Contracts surface (the
same deliberate exception `docs/architecture.md` records for the memory/x0 chips).

## The semantic input, per family

* **Byte providers** (opcodes 0–5) — a `ByteEntry`: the operand byte pair the consumer asked about
  and the aggregate count for that key. `MSB` reads only `b`.
* **Range providers** (every width 0 through 16) — a `RangeEntry`: the value being range-checked
  and its aggregate count.
* **Program-ROM provider** — a `RomEntry`: one committed instruction, as plain naturals, limbed by
  the builder exactly as the fetch messages are, plus its fetch count.
* **Memory boundary tables** — a `MemRecordEntry`: an address, a 64-bit value, and an access clock
  (pinned to `0` for the init side, the chain's last access clock for the finalize side), with an
  explicit boolean activity selector. The
  finalize side needs **no** well-formedness premise at all: limbing is what makes the pulled
  record's `isU64 ∧ ClkBound` guarantee true, so the builder supplies it rather than demanding it.
* **The two W3 system tables** — the canonicalization/refresh rows themselves
  (`FormalModel/Contracts/SystemChips.lean`), which is the shape their `ProverAssumptions := Spec`
  already fixes: `Spec` is the row's full evidence-form content, so a "semantic event" for these
  tables *is* a row satisfying it. A concrete `(clk, pc)`-to-row builder is a separate, arithmetic
  piece of work and is not attempted here; the zero row is built and proved below, which is what a
  padded table needs.
* **The ensemble verifier row** — the committed initial and final `(clk, pc)`, as naturals.

## Multiplicity: explicit, aggregatable, and paddable

Every provider row carries its multiplicity as an explicit circuit input. Consequently
`Component.buildRow` preserves the builder's count rather than overwriting it with a constant local
witness. Byte, Range, and Program entries accept natural counts: `0` gives a bus-neutral padding row,
`1` retains the per-occurrence representation, and `m > 1` aggregates repeated equal keys. As usual
for a field-valued LogUp count, the trace-level capacity contract keeps every intended natural
count in the nonnegative half of the field.  This both rejects aliases such as `m` versus `m + p` and
makes the centered integer projection used by the machine ledger recover the original natural.

Memory init/finalize deliberately expose only a `Bool` selector. Their circuits retain the shallow
`m * (m - 1) = 0` gate needed by the field-to-integer memory-balance proof, while the builders now
reach both the active (`1`) and padding (`0`) branches.
-/

namespace SP1Clean

open Circuit
open Air.Flat (Component Table)

/-! ## Semantic occurrence types -/

namespace TraceGen

/-- One byte-table occurrence: the operand pair a consumer's `byteChannel` pull names. The `MSB`
provider reads only `b`, and the derived result column (`AND`/`OR`/`XOR`/`LTU`/`MSB`) is not part of
the occurrence — the provider computes it in-circuit. -/
structure ByteEntry where
  b : ℕ
  c : ℕ
  multiplicity : ℕ
deriving DecidableEq

/-- A byte-table occurrence is well-formed when both slots really are bytes. -/
def ByteEntry.WellFormed (e : ByteEntry) : Prop := e.b < 2 ^ 8 ∧ e.c < 2 ^ 8

/-- The aggregate count is represented canonically and nonnegatively by `signedVal`.  The
half-field bound is the trace-generator capacity contract, not a local Byte-circuit constraint. -/
def ByteEntry.MultiplicityFits (p : ℕ) (e : ByteEntry) : Prop :=
  2 * e.multiplicity ≤ p

/-- One range-table occurrence at a fixed width: the value being checked. -/
structure RangeEntry where
  a : ℕ
  multiplicity : ℕ
deriving DecidableEq

/-- A range occurrence is well-formed at width `n` when the value fits in `n` bits. -/
def RangeEntry.WellFormed (n : ℕ) (e : RangeEntry) : Prop := e.a < 2 ^ n

/-- The aggregate count is represented canonically and nonnegatively by `signedVal`. -/
def RangeEntry.MultiplicityFits (p : ℕ) (e : RangeEntry) : Prop :=
  2 * e.multiplicity ≤ p

/-- One committed program-ROM entry, as plain naturals: the fetch address, the decoded opcode and
operand slots, and the three flags. `opB`/`opC` are 64-bit values (register contents or
immediates); the builder limbs them exactly as the fetch message carries them. -/
structure RomEntry where
  pc : ℕ
  opcode : ℕ
  opA : ℕ
  opB : ℕ
  opC : ℕ
  opA0 : ℕ
  immB : ℕ
  immC : ℕ
  multiplicity : ℕ
deriving DecidableEq

/-- A ROM entry is well-formed when its write-register index is a real register index and its
`op_a = x0` flag is a bit. The pc needs no premise: the builder limbs it, so every limb is `< 2^16`
by construction. -/
def RomEntry.WellFormed (e : RomEntry) : Prop := e.opA < 32 ∧ (e.opA0 = 0 ∨ e.opA0 = 1)

/-- The aggregate fetch count is represented canonically and nonnegatively by `signedVal`. -/
def RomEntry.MultiplicityFits (p : ℕ) (e : RomEntry) : Prop :=
  2 * e.multiplicity ≤ p

/-- One memory-boundary record: a byte address, the 64-bit value, the access clock, and an explicit
boolean activity selector. The init side uses `clk = 0` (SP1's memory-init interaction passes
literal zeros for both clock limbs); the finalize side uses the chain's last access clock. -/
structure MemRecordEntry where
  addr : ℕ
  value : ℕ
  clk : ℕ
  multiplicity : Bool
deriving DecidableEq

/-- An init record is well-formed when its clock is zero, which is what the provider circuit pins
both limbs to. -/
def MemRecordEntry.WellFormedInit (e : MemRecordEntry) : Prop := e.clk = 0

end TraceGen

section Casts

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- A natural below a bound that fits the field round-trips through `ZMod.val`. The one arithmetic
step every builder obligation below reduces to. -/
lemma val_natCast_lt {n b : ℕ} (h : n < b) (hb : b ≤ 2 ^ 24) : ((n : ℕ) : ZMod p).val < b := by
  have := Fact.out (p := 2 ^ 24 < p)
  rw [ZMod.val_natCast_of_lt (by omega)]
  exact h

/-- The zero/one flag naturals cast to the field's zero/one. -/
lemma natCast_isBool {n : ℕ} (h : n = 0 ∨ n = 1) :
    ((n : ℕ) : ZMod p) = 0 ∨ ((n : ℕ) : ZMod p) = 1 := by
  rcases h with h | h <;> rw [h] <;> simp

namespace TraceGen

omit [Fact (2 ^ 24 < p)] in
/-- A capacity-bounded Byte count is recovered exactly by the machine's centered ledger. -/
lemma ByteEntry.signedVal_multiplicity (e : ByteEntry) (h : e.MultiplicityFits p) :
    signedVal (e.multiplicity : ZMod p) = (e.multiplicity : ℤ) :=
  signedVal_natCast_of_twice_le e.multiplicity h

omit [Fact (2 ^ 24 < p)] in
/-- A capacity-bounded Range count is recovered exactly by the machine's centered ledger. -/
lemma RangeEntry.signedVal_multiplicity (e : RangeEntry) (h : e.MultiplicityFits p) :
    signedVal (e.multiplicity : ZMod p) = (e.multiplicity : ℤ) :=
  signedVal_natCast_of_twice_le e.multiplicity h

omit [Fact (2 ^ 24 < p)] in
/-- A capacity-bounded ROM count is recovered exactly by the machine's centered ledger. -/
lemma RomEntry.signedVal_multiplicity (e : RomEntry) (h : e.MultiplicityFits p) :
    signedVal (e.multiplicity : ZMod p) = (e.multiplicity : ℤ) :=
  signedVal_natCast_of_twice_le e.multiplicity h

end TraceGen

end Casts

/-! ## The six byte-table providers

All six take the same occurrence type and prove the same two byte bounds; `MSB` uses only the
first. -/

namespace ByteChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

namespace U8Range

/-- The `U8Range` provider's row for one byte-table occurrence. -/
def ofEntry (e : TraceGen.ByteEntry) : Inputs (ZMod p) :=
  ⟨(e.b : ZMod p), (e.c : ZMod p), (e.multiplicity : ZMod p)⟩

/-- The `U8Range` provider as a flat-AIR component. A plain `def`, deliberately not an `abbrev`
(see the note on `AddChip.component`). -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The rows a list of occurrences builds. -/
def traceInputs (entries : List TraceGen.ByteEntry) : List (Inputs (ZMod p)) :=
  entries.map ofEntry

/-- A well-formed occurrence builds a row the honest prover can complete. -/
theorem proverAssumptions_of_entry {e : TraceGen.ByteEntry} (h : e.WellFormed)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    circuit.ProverAssumptions (ofEntry (p := p) e) data hint :=
  ⟨val_natCast_lt h.1 (by norm_num), val_natCast_lt h.2 (by norm_num)⟩

theorem proverAssumptions_of_mem_traceInputs {entries : List TraceGen.ByteEntry}
    (h : ∀ e ∈ entries, e.WellFormed) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) entries, circuit.ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_entry (h e he) data hint

theorem traceTable_constraints (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_guarantees (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_interactionsWith (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).interactionsWith channel =
      (traceInputs (p := p) entries).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end U8Range

namespace MSB

/-- The `MSB` provider's row for one byte-table occurrence (only the `b` slot is committed; the
high bit is derived in-circuit). -/
def ofEntry (e : TraceGen.ByteEntry) : Inputs (ZMod p) :=
  ⟨(e.b : ZMod p), (e.multiplicity : ZMod p)⟩

/-- The `MSB` provider as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The rows a list of occurrences builds. -/
def traceInputs (entries : List TraceGen.ByteEntry) : List (Inputs (ZMod p)) :=
  entries.map ofEntry

theorem proverAssumptions_of_entry {e : TraceGen.ByteEntry} (h : e.WellFormed)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    circuit.ProverAssumptions (ofEntry (p := p) e) data hint :=
  val_natCast_lt h.1 (by norm_num)

theorem proverAssumptions_of_mem_traceInputs {entries : List TraceGen.ByteEntry}
    (h : ∀ e ∈ entries, e.WellFormed) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) entries, circuit.ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_entry (h e he) data hint

theorem traceTable_constraints (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_guarantees (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_interactionsWith (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).interactionsWith channel =
      (traceInputs (p := p) entries).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end MSB

namespace AndByte

/-- The `AND` provider's row for one byte-table occurrence. -/
def ofEntry (e : TraceGen.ByteEntry) : Inputs (ZMod p) :=
  ⟨(e.b : ZMod p), (e.c : ZMod p), (e.multiplicity : ZMod p)⟩

/-- The `AND` provider as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The rows a list of occurrences builds. -/
def traceInputs (entries : List TraceGen.ByteEntry) : List (Inputs (ZMod p)) :=
  entries.map ofEntry

theorem proverAssumptions_of_entry {e : TraceGen.ByteEntry} (h : e.WellFormed)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    circuit.ProverAssumptions (ofEntry (p := p) e) data hint :=
  ⟨val_natCast_lt h.1 (by norm_num), val_natCast_lt h.2 (by norm_num)⟩

theorem proverAssumptions_of_mem_traceInputs {entries : List TraceGen.ByteEntry}
    (h : ∀ e ∈ entries, e.WellFormed) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) entries, circuit.ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_entry (h e he) data hint

theorem traceTable_constraints (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_guarantees (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_interactionsWith (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).interactionsWith channel =
      (traceInputs (p := p) entries).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end AndByte

namespace OrByte

/-- The `OR` provider's row for one byte-table occurrence. -/
def ofEntry (e : TraceGen.ByteEntry) : Inputs (ZMod p) :=
  ⟨(e.b : ZMod p), (e.c : ZMod p), (e.multiplicity : ZMod p)⟩

/-- The `OR` provider as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The rows a list of occurrences builds. -/
def traceInputs (entries : List TraceGen.ByteEntry) : List (Inputs (ZMod p)) :=
  entries.map ofEntry

theorem proverAssumptions_of_entry {e : TraceGen.ByteEntry} (h : e.WellFormed)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    circuit.ProverAssumptions (ofEntry (p := p) e) data hint :=
  ⟨val_natCast_lt h.1 (by norm_num), val_natCast_lt h.2 (by norm_num)⟩

theorem proverAssumptions_of_mem_traceInputs {entries : List TraceGen.ByteEntry}
    (h : ∀ e ∈ entries, e.WellFormed) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) entries, circuit.ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_entry (h e he) data hint

theorem traceTable_constraints (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_guarantees (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_interactionsWith (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).interactionsWith channel =
      (traceInputs (p := p) entries).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end OrByte

namespace XorByte

/-- The `XOR` provider's row for one byte-table occurrence. -/
def ofEntry (e : TraceGen.ByteEntry) : Inputs (ZMod p) :=
  ⟨(e.b : ZMod p), (e.c : ZMod p), (e.multiplicity : ZMod p)⟩

/-- The `XOR` provider as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The rows a list of occurrences builds. -/
def traceInputs (entries : List TraceGen.ByteEntry) : List (Inputs (ZMod p)) :=
  entries.map ofEntry

theorem proverAssumptions_of_entry {e : TraceGen.ByteEntry} (h : e.WellFormed)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    circuit.ProverAssumptions (ofEntry (p := p) e) data hint :=
  ⟨val_natCast_lt h.1 (by norm_num), val_natCast_lt h.2 (by norm_num)⟩

theorem proverAssumptions_of_mem_traceInputs {entries : List TraceGen.ByteEntry}
    (h : ∀ e ∈ entries, e.WellFormed) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) entries, circuit.ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_entry (h e he) data hint

theorem traceTable_constraints (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_guarantees (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_interactionsWith (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).interactionsWith channel =
      (traceInputs (p := p) entries).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end XorByte

namespace Ltu

/-- The `LTU` provider's row for one byte-table occurrence. -/
def ofEntry (e : TraceGen.ByteEntry) : Inputs (ZMod p) :=
  ⟨(e.b : ZMod p), (e.c : ZMod p), (e.multiplicity : ZMod p)⟩

/-- The `LTU` provider as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The rows a list of occurrences builds. -/
def traceInputs (entries : List TraceGen.ByteEntry) : List (Inputs (ZMod p)) :=
  entries.map ofEntry

theorem proverAssumptions_of_entry {e : TraceGen.ByteEntry} (h : e.WellFormed)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    circuit.ProverAssumptions (ofEntry (p := p) e) data hint :=
  ⟨val_natCast_lt h.1 (by norm_num), val_natCast_lt h.2 (by norm_num)⟩

theorem proverAssumptions_of_mem_traceInputs {entries : List TraceGen.ByteEntry}
    (h : ∀ e ∈ entries, e.WellFormed) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) entries, circuit.ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_entry (h e he) data hint

theorem traceTable_constraints (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_guarantees (entries : List TraceGen.ByteEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_interactionsWith (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).interactionsWith channel =
      (traceInputs (p := p) entries).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end Ltu

end ByteChip

/-! ## The complete fixed-width range-provider family

Stated once at an arbitrary compile-time width `n`; `componentFor` indexes the complete SP1
preprocessed profile by `Fin 17`. -/

namespace RangeChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The range provider's row for one occurrence. -/
def ofEntry (e : TraceGen.RangeEntry) : Inputs (ZMod p) :=
  ⟨(e.a : ZMod p), (e.multiplicity : ZMod p)⟩

/-- The fixed-width range provider as a flat-AIR component. -/
def component (n : ℕ) (hn : 2 ^ n < p) : Component (ZMod p) := ⟨circuit n hn⟩

/-- The flat-AIR component at one width in SP1's complete `0, …, 16` profile. -/
def componentFor (width : Width) : Component (ZMod p) := ⟨circuitFor width⟩

/-- The rows a list of occurrences builds. -/
def traceInputs (entries : List TraceGen.RangeEntry) : List (Inputs (ZMod p)) :=
  entries.map ofEntry

theorem proverAssumptions_of_entry {n : ℕ} (hn : 2 ^ n < p) (hle : n ≤ 16)
    {e : TraceGen.RangeEntry} (h : e.WellFormed n)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (circuit n hn).ProverAssumptions (ofEntry (p := p) e) data hint :=
  val_natCast_lt h (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem proverAssumptions_of_mem_traceInputs {n : ℕ} (hn : 2 ^ n < p) (hle : n ≤ 16)
    {entries : List TraceGen.RangeEntry} (h : ∀ e ∈ entries, e.WellFormed n)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) entries,
      (circuit n hn).ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_entry hn hle (h e he) data hint

theorem traceTable_constraints {n : ℕ} (hn : 2 ^ n < p) (hle : n ≤ 16)
    (entries : List TraceGen.RangeEntry) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ entries, e.WellFormed n) :
    (Table.build (component (p := p) n hn) (traceInputs entries) data hint).Constraints :=
  Table.build_constraints _ _ _ _ (computableWitnesses n hn)
    (proverAssumptions_of_mem_traceInputs hn hle h data hint)

theorem traceTable_guarantees {n : ℕ} (hn : 2 ^ n < p) (hle : n ≤ 16)
    (entries : List TraceGen.RangeEntry) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ entries, e.WellFormed n) :
    (Table.build (component (p := p) n hn) (traceInputs entries) data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ (computableWitnesses n hn)
    (proverAssumptions_of_mem_traceInputs hn hle h data hint)

theorem traceTable_interactionsWith {n : ℕ} (hn : 2 ^ n < p)
    (entries : List TraceGen.RangeEntry) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p) n hn) (traceInputs entries) data
        hint).interactionsWith channel =
      (traceInputs (p := p) entries).flatMap fun input =>
        (component (p := p) n hn).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p) n hn).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end RangeChip

/-! ## The Program-ROM provider -/

namespace ProgramProviderChip

open SP1Clean.Channels (ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The Program-ROM provider's row for one committed instruction: the fetch pc as three 16-bit
limbs, the two operand slots as `Word`s, the decode flags, and its explicit fetch count. -/
def ofEntry (e : TraceGen.RomEntry) : Inputs (ZMod p) where
  pc0 := ((e.pc % 2 ^ 16 : ℕ) : ZMod p)
  pc1 := ((e.pc / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p)
  pc2 := ((e.pc / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p)
  opcode := (e.opcode : ZMod p)
  op_a := (e.opA : ZMod p)
  op_b := TraceGen.wordOfNat e.opB
  op_c := TraceGen.wordOfNat e.opC
  op_a_0 := (e.opA0 : ZMod p)
  imm_b := (e.immB : ZMod p)
  imm_c := (e.immC : ZMod p)
  multiplicity := (e.multiplicity : ZMod p)

/-- The Program-ROM provider as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The rows a committed program builds: one per instruction. -/
def traceInputs (entries : List TraceGen.RomEntry) : List (Inputs (ZMod p)) :=
  entries.map ofEntry

theorem proverAssumptions_of_entry {e : TraceGen.RomEntry} (h : e.WellFormed)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    circuit.ProverAssumptions (ofEntry (p := p) e) data hint :=
  ⟨val_natCast_lt h.1 (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    natCast_isBool h.2⟩

theorem proverAssumptions_of_mem_traceInputs {entries : List TraceGen.RomEntry}
    (h : ∀ e ∈ entries, e.WellFormed) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) entries, circuit.ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_entry (h e he) data hint

theorem traceTable_constraints (entries : List TraceGen.RomEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_guarantees (entries : List TraceGen.RomEntry) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ entries, e.WellFormed) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_interactionsWith (entries : List TraceGen.RomEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).interactionsWith channel =
      (traceInputs (p := p) entries).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end ProgramProviderChip

/-! ## The two memory boundary tables

Both take the same record type; the init side pins the clock to `0` (SP1's memory-init interaction
passes literal zeros) and the finalize side carries the chain's last access clock. -/

namespace TraceGen

open SP1Clean.Channels (MemoryMsg)

/-- A memory-boundary record's Memory-bus message: the clock split at `2^24`, the byte address as
three 16-bit limbs, and the 64-bit value as a `Word`. -/
def MemRecordEntry.toMemoryMsg {p : ℕ} (e : MemRecordEntry) : MemoryMsg (ZMod p) where
  clk_high := ((e.clk / 2 ^ 24 : ℕ) : ZMod p)
  clk_low := ((e.clk % 2 ^ 24 : ℕ) : ZMod p)
  addr0 := ((e.addr % 2 ^ 16 : ℕ) : ZMod p)
  addr1 := ((e.addr / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p)
  addr2 := ((e.addr / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p)
  value := wordOfNat e.value

/-- The field selector carried by a memory-boundary row. Keeping the semantic source a `Bool`
makes the honest builder incapable of producing an aggregated memory-global row. -/
def MemRecordEntry.multiplicityField {p : ℕ} (e : MemRecordEntry) : ZMod p :=
  if e.multiplicity then 1 else 0

theorem MemRecordEntry.multiplicityField_isBool {p : ℕ} (e : MemRecordEntry) :
    e.multiplicityField (p := p) = 0 ∨ e.multiplicityField (p := p) = 1 := by
  cases h : e.multiplicity <;> simp [multiplicityField, h]

end TraceGen

namespace MemoryProviderChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The memory-init provider's row for one boundary record. -/
def ofEntry (e : TraceGen.MemRecordEntry) : Inputs (ZMod p) :=
  let message := e.toMemoryMsg
  { clk_high := message.clk_high
    clk_low := message.clk_low
    addr0 := message.addr0
    addr1 := message.addr1
    addr2 := message.addr2
    value := message.value
    multiplicity := e.multiplicityField }

/-- The memory-init provider as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The rows the genesis boundary builds: one per initialized address. -/
def traceInputs (entries : List TraceGen.MemRecordEntry) : List (Inputs (ZMod p)) :=
  entries.map ofEntry

theorem proverAssumptions_of_entry {e : TraceGen.MemRecordEntry} (h : e.WellFormedInit)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    circuit.ProverAssumptions (ofEntry (p := p) e) data hint := by
  haveI : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hclk : e.clk = 0 := h
  refine ⟨TraceGen.wordOfNat_isU64 _, ?_, ?_, e.multiplicityField_isBool⟩
  · simp only [ofEntry, TraceGen.MemRecordEntry.toMemoryMsg, hclk]
    norm_num
  · simp only [ofEntry, TraceGen.MemRecordEntry.toMemoryMsg, hclk]
    norm_num

theorem proverAssumptions_of_mem_traceInputs {entries : List TraceGen.MemRecordEntry}
    (h : ∀ e ∈ entries, e.WellFormedInit) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) entries, circuit.ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_entry (h e he) data hint

theorem traceTable_constraints (entries : List TraceGen.MemRecordEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ entries, e.WellFormedInit) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_guarantees (entries : List TraceGen.MemRecordEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ entries, e.WellFormedInit) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

theorem traceTable_interactionsWith (entries : List TraceGen.MemRecordEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).interactionsWith channel =
      (traceInputs (p := p) entries).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end MemoryProviderChip

namespace MemoryFinalizeChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The memory-finalize table's row for one boundary record. -/
def ofEntry (e : TraceGen.MemRecordEntry) : Inputs (ZMod p) :=
  let message := e.toMemoryMsg
  { clk_high := message.clk_high
    clk_low := message.clk_low
    addr0 := message.addr0
    addr1 := message.addr1
    addr2 := message.addr2
    value := message.value
    multiplicity := e.multiplicityField }

/-- The memory-finalize table as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The rows the finalize boundary builds: one per address chain. -/
def traceInputs (entries : List TraceGen.MemRecordEntry) : List (Inputs (ZMod p)) :=
  entries.map ofEntry

/-- **A finalize record needs no well-formedness premise.** The channel guarantee a finalize pull
must exhibit is `isU64 ∧ ClkBound`, and the builder establishes both by construction: it limbs the
value into a `Word` and splits the access clock at `2 ^ 24`, so the low limb is a genuine 24-bit
timestamp whatever the clock was. (The record still represents the full clock — the overflow lives
in `clk_high`, which `ClkBound` does not constrain.) -/
theorem proverAssumptions_of_entry (e : TraceGen.MemRecordEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    circuit.ProverAssumptions (ofEntry (p := p) e) data hint := by
  haveI : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  exact ⟨TraceGen.wordOfNat_isU64 _, val_natCast_lt (Nat.mod_lt _ (by norm_num)) le_rfl,
    e.multiplicityField_isBool⟩

theorem proverAssumptions_of_mem_traceInputs (entries : List TraceGen.MemRecordEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) entries, circuit.ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_entry e data hint

theorem traceTable_constraints (entries : List TraceGen.MemRecordEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs entries data hint)

theorem traceTable_guarantees (entries : List TraceGen.MemRecordEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs entries data hint)

set_option linter.unusedSectionVars false in
theorem traceTable_interactionsWith (entries : List TraceGen.MemRecordEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) (traceInputs entries) data hint).interactionsWith channel =
      (traceInputs (p := p) entries).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end MemoryFinalizeChip

/-! ## The two W3 system tables

Their `ProverAssumptions` is their `Spec`, and `Spec` is the row's whole evidence-form content, so
the semantic input for these two *is* a row satisfying `Spec`. The zero row is built and proved
below (it is the row a padded table repeats); a `(clk, pc)`-to-row builder is separate work. -/

namespace StateBumpChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The StateBump table as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The all-zero StateBump row: both selectors off, the pc cascade with zero borrows, the gated
tail vacuous. This is the padding row a shard's StateBump table repeats. -/
def paddingInputs : Inputs (ZMod p) where
  next_clk_32_48 := 0
  next_clk_24_32 := 0
  next_clk_16_24 := 0
  next_clk_0_16 := 0
  clk_high := 0
  clk_low := 0
  next_pc0 := 0
  next_pc1 := 0
  next_pc2 := 0
  pc0 := 0
  pc1 := 0
  pc2 := 0
  is_clk := 0
  is_real := 0

theorem spec_paddingInputs : Spec (paddingInputs (p := p)) := by
  haveI : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  refine ⟨Or.inl rfl, Or.inl rfl, ⟨0, 0, Or.inl rfl, Or.inl rfl, by simp [paddingInputs],
    by simp [paddingInputs], by simp [paddingInputs]⟩, fun h => absurd h ?_⟩
  simp [paddingInputs]

theorem traceTable_constraints (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ r ∈ rows, Spec r) :
    (Table.build (component (p := p)) rows data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses fun r hr => h r hr

theorem traceTable_guarantees (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ r ∈ rows, Spec r) :
    (Table.build (component (p := p)) rows data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses fun r hr => h r hr

theorem traceTable_interactionsWith (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) rows data hint).interactionsWith channel =
      rows.flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end StateBumpChip

namespace MemoryBumpChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The MemoryBump table as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The all-zero MemoryBump row: the selector off, so the whole gated contract is vacuous. This is
the padding row a shard's MemoryBump table repeats. -/
def paddingInputs : Inputs (ZMod p) where
  access :=
    { prev_value := #v[0, 0, 0, 0]
      access_timestamp :=
        { prev_high := 0, prev_low := 0, compare_low := 0,
          diff_low_limb := 0, diff_high_limb := 0 } }
  clk_32_48 := 0
  clk_24_32 := 0
  clk_16_24 := 0
  clk_0_16 := 0
  addr := 0
  is_real := 0

theorem spec_paddingInputs : Spec (paddingInputs (p := p)) := by
  haveI : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  refine ⟨Or.inl rfl, fun h => absurd h ?_⟩
  simp [paddingInputs]

theorem traceTable_constraints (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ r ∈ rows, Spec r) :
    (Table.build (component (p := p)) rows data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses fun r hr => h r hr

theorem traceTable_guarantees (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ r ∈ rows, Spec r) :
    (Table.build (component (p := p)) rows data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses fun r hr => h r hr

theorem traceTable_interactionsWith (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) rows data hint).interactionsWith channel =
      rows.flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end MemoryBumpChip

/-! ## The ensemble verifier row

`localLength = 0`, so witness generation contributes nothing and the built row is exactly the
committed public input. -/

namespace Soundness

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The boundary verifier has computable witnesses vacuously: the row declares no cells. -/
theorem sp1StateVerifier_computableWitnesses :
    (sp1StateVerifier (p := p)).base.ComputableWitnesses := fun k input env env' =>
  Operations.forAllFlat_witnessCongr_of_localLength_zero _ _
    (by simp [sp1StateVerifier, sp1StateVerifierMain, circuit_norm,
      Channels.stateChannel, Channels.byteChannel])

/-- The verifier row for a committed initial and final `(clk, pc)`: both endpoints in the upstream
`(16, 8, 8, 16)` clock limbs plus three 16-bit pc limbs. -/
def boundaryInputs (initClk initPc finalClk finalPc : ℕ) : SP1PublicIO (ZMod p) where
  init_clk_0_16 := ((initClk % 2 ^ 16 : ℕ) : ZMod p)
  init_clk_16_24 := ((initClk / 2 ^ 16 % 2 ^ 8 : ℕ) : ZMod p)
  init_clk_24_32 := ((initClk / 2 ^ 24 % 2 ^ 8 : ℕ) : ZMod p)
  init_clk_32_48 := ((initClk / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p)
  init_pc0 := ((initPc % 2 ^ 16 : ℕ) : ZMod p)
  init_pc1 := ((initPc / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p)
  init_pc2 := ((initPc / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p)
  final_clk_0_16 := ((finalClk % 2 ^ 16 : ℕ) : ZMod p)
  final_clk_16_24 := ((finalClk / 2 ^ 16 % 2 ^ 8 : ℕ) : ZMod p)
  final_clk_24_32 := ((finalClk / 2 ^ 24 % 2 ^ 8 : ℕ) : ZMod p)
  final_clk_32_48 := ((finalClk / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p)
  final_pc0 := ((finalPc % 2 ^ 16 : ℕ) : ZMod p)
  final_pc1 := ((finalPc / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p)
  final_pc2 := ((finalPc / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p)

/-- **The verifier row needs no premise**: limbing a natural is what makes every committed limb
canonical, so `LimbBounds` — the honest-prover contract and the row's whole `Spec` — holds for any
pair of clocks and pcs. -/
theorem boundaryInputs_limbBounds (initClk initPc finalClk finalPc : ℕ) :
    (boundaryInputs (p := p) initClk initPc finalClk finalPc).LimbBounds :=
  ⟨val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num),
    val_natCast_lt (Nat.mod_lt _ (by norm_num)) (by norm_num)⟩

/-- The boundary verifier as a flat-AIR component — the shape `EnsembleWitness.verifierTable`
carries. -/
def verifierComponent : Component (ZMod p) := ⟨sp1StateVerifier⟩

theorem verifierTable_constraints (pis : List (SP1PublicIO (ZMod p)))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (h : ∀ pi ∈ pis, pi.LimbBounds) :
    (Table.build (verifierComponent (p := p)) pis data hint).Constraints :=
  Table.build_constraints _ _ _ _ sp1StateVerifier_computableWitnesses fun pi hpi => h pi hpi

theorem verifierTable_guarantees (pis : List (SP1PublicIO (ZMod p)))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (h : ∀ pi ∈ pis, pi.LimbBounds) :
    (Table.build (verifierComponent (p := p)) pis data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ sp1StateVerifier_computableWitnesses fun pi hpi => h pi hpi

theorem verifierTable_interactionsWith (pis : List (SP1PublicIO (ZMod p)))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (verifierComponent (p := p)) pis data hint).interactionsWith channel =
      pis.flatMap fun input =>
        (verifierComponent (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((verifierComponent (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end Soundness

end SP1Clean
