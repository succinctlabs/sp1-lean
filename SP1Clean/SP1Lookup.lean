import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Circuit.Loops
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Primes
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import SP1Foundations.Field
import SP1Foundations.Constraint
import SP1Clean.ByteOpcodeTable

set_option linter.style.setOption false
set_option linter.style.docString false
set_option linter.style.longLine false

/-!
# Multiplicity-weighted lookup bus, parallel to `Clean/Utils/OfflineMemory.lean`

`Clean/OfflineMemory.lean` proves a "Memory in the Head" theorem for
ordered memory access lists `(timestamp, addr, readValue, writeValue)`:
the online consistency check (read returns last write) is equivalent to
an offline decision procedure (sort by address+timestamp; verify pairwise
read=writePrev / read=0).

SP1 generalizes that pattern: every cross-chip interaction — byte
lookups, program lookups, *and* memory access — flows through a
**multiplicity-weighted bus**. Each row contributes
`(table_id, entry, multiplicity)` triples; the bus is consistent iff for
every distinct `(table_id, entry)`, the **sum of multiplicities is zero**.
Sends are positive, receives are negative; static tables (like
`ByteOpcodeTable`) emit synthetic receives with multiplicity equal to the
total send count for each table entry.

This is the mechanism that lets SP1 emit gated lookups like
`send X with mult (is_real - imm_c)` — when the multiplicity is 0 on a
row, the lookup contributes nothing to the bus and is *semantically a
no-op*. Clean's current `lookup` primitive has no such gating
(multiplicity is implicitly 1), so we can't faithfully mirror SP1's
gated emissions inside the existing `Circuit` monad.

This file sketches the parallel construction: a `LookupAccess` data
type, sorting orderings, decidability instances, online/offline
consistency predicates, and the main `isConsistentOnline_iff_isConsistentOffline`
theorem — all mirroring `MemoryAccessList`'s structure.

It also sketches a multiplicity-aware lookup primitive (`Lookup'`,
`Operation'`, `lookupGated`) that chips can call to emit gated lookups,
plus the bridge between per-row Clean assertions and the trace-level
balanced-multiset bus.

## Scope of this sketch

- **Defined:** data types, orderings, decidability, online/offline
  consistency predicates, primitive lookup-with-multiplicity surface,
  main theorem statement.
- **Sorry'd:** the substantive correctness proofs (parallel to
  `OfflineMemory.lean` lines 200–931). Each `sorry` carries a comment
  pointing at the analog in `OfflineMemory.lean`.
- **Future work:** generalize the `Clean/Circuit/Basic.lean` framework
  to natively support multiplicity-weighted lookups so SP1Clean chips
  can compose `lookupGated` exactly like they compose `lookup` today.
-/

/-! ## Data model

Mirrors SP1's Rust `AirInteraction<E>` from
`/home/devontuma/Documents/sp1/crates/hypercube/src/air/interaction.rs`:
```rust
pub struct AirInteraction<E> {
    pub values: Vec<E>,
    pub multiplicity: E,
    pub kind: InteractionKind,
}
```

We split the kind into a discriminator enum so byte-bus and memory-bus
contributions are distinguishable at the trace-level aggregator. The
`String` table_id remains a fine-grained discriminator (mirrors
`RawTable.name`); a single chip may emit byte-bus interactions tagged
with several table names (`SP1ByteOpcode`, `SP1Program`, etc.).
-/

/--
  Tag for each cross-chip interaction. Mirrors SP1's `InteractionKind` enum.
  The numeric tags match SP1's Rust source:
  - `Memory = 1` — register and RAM bus (read/write pairs, multiset closure)
  - `Byte = 5` — byte lookup table (range checks, U8, MSB, etc.)
  - `Program = ...` — program-bus (trusted instruction stream)
  - `PageProt = 18` / `PageProtAccess = 19` — page protection
  - `State = ...` — state-bus interactions

  For SP1Clean we currently only need `Memory`, `Byte`, `Program`. Others
  are listed for completeness so the discriminator covers SP1's full bus
  topology.
-/
inductive InteractionKind where
  | Memory
  | Byte
  | Program
  | PageProt
  | PageProtAccess
  | State
  deriving DecidableEq, Repr, Inhabited

/--
  A single lookup-bus contribution: which kind of bus, which named table
  within that bus, the entry (as a list of field elements — the table's
  row), and the multiplicity.

  Multiplicity is `Int` (signed) so that sends (positive) and receives
  (negative) live in the same list. For a balanced bus, the sum of
  multiplicities for each distinct `(kind, table_id, entry)` is zero.
-/
abbrev LookupAccess := InteractionKind × String × List ℕ × ℤ
  -- (kind, table_id, entry, multiplicity)

/--
  A list of lookup accesses, canonically in trace-emission order
  (oldest at head, matching `OfflineMemory.MemoryAccessList`'s reverse-order
  convention). Each chip row contributes 0 or more entries.
-/
abbrev LookupAccessList := List LookupAccess

namespace LookupAccessList

/-! ## Keying

We project each access to its `(kind, table_id, entry)` key for grouping.
The lookup bus's consistency check is purely a function of these
keys and the associated multiplicities — there's no order dependence
(unlike the memory bus, where `last write wins` makes order
semantically essential). This makes most properties below
permutation-invariant by construction. -/

abbrev LookupKey := InteractionKind × String × List ℕ

@[reducible]
def keyOf (a : LookupAccess) : LookupKey := (a.1, a.2.1, a.2.2.1)

@[reducible]
def multOf (a : LookupAccess) : ℤ := a.2.2.2

/-! ## Filtering — restrict to a single `(kind, table_id, entry)`

Parallel to `MemoryAccessList.filterAddress`. -/

def filterKey (accesses : LookupAccessList) (k : LookupKey) :
    LookupAccessList :=
  accesses.filter (fun a => keyOf a = k)

/-! ## Multiplicity sum and basic properties -/

/--
  Sum of multiplicities for a specific `(table_id, entry)` key across
  the whole list. Bus is balanced if this is `0` for every observed key.

  Stated as a filter + map + sum to make permutation invariance and
  concatenation properties immediate from the `List.sum` API.
-/
def multiplicitySum (accesses : LookupAccessList) (k : LookupKey) : ℤ :=
  ((filterKey accesses k).map multOf).sum

theorem multiplicitySum_nil (k : LookupKey) :
    multiplicitySum [] k = 0 := rfl

theorem multiplicitySum_cons (head : LookupAccess) (tail : LookupAccessList)
    (k : LookupKey) :
    multiplicitySum (head :: tail) k =
      (if keyOf head = k then multOf head else 0) + multiplicitySum tail k := by
  simp only [multiplicitySum, filterKey, List.filter_cons]
  by_cases h : keyOf head = k
  · simp [h]
  · simp [h]

theorem multiplicitySum_append (l1 l2 : LookupAccessList) (k : LookupKey) :
    multiplicitySum (l1 ++ l2) k = multiplicitySum l1 k + multiplicitySum l2 k := by
  simp only [multiplicitySum, filterKey, List.filter_append, List.map_append,
             List.sum_append]

/--
  Permutation invariance of `multiplicitySum`: reordering rows does
  not change the per-key sum. This is the structural fact that makes
  the lookup-bus consistency check (`isConsistentBalanced`) trivially
  permutation-invariant — the analog of OfflineMemory's
  "address-timestamp-sort yields a fresh permutation" step is here
  built into `Perm` directly.
-/
theorem multiplicitySum_perm (l1 l2 : LookupAccessList) (h : l1.Perm l2)
    (k : LookupKey) :
    multiplicitySum l1 k = multiplicitySum l2 k := by
  simp only [multiplicitySum, filterKey]
  exact (h.filter _).map _ |>.sum_eq

/-! ## Consistency

The bus is consistent iff for every distinct `(table_id, entry)`, the
sum of multiplicities is zero. We give two parallel definitions:

- **Online consistency** (`isConsistentOnline`): the per-row trace check
  — "for each `(t, e)` that appears anywhere, the sum is zero". This is
  the form a single-pass trace analyzer can apply.

- **Balanced consistency** (`isConsistentBalanced`): the same predicate
  but quantified over *all* keys (whether observed or not). Equivalent
  since `multiplicitySum` is `0` on absent keys by construction.

These are pointwise equivalent — unlike the memory bus, the lookup bus
has no order dependence, so the online/offline distinction collapses.
We still expose both names to match the OfflineMemory pattern and to
keep the door open for an optimization-grade `isConsistentBlock` form
later (sort the list and walk maximal-equal-key blocks — same final
answer, but better suited for a decidable bus checker).
-/

def isConsistentOnline (accesses : LookupAccessList) : Prop :=
  ∀ (k : LookupKey),
    (∃ a ∈ accesses, keyOf a = k) →
    multiplicitySum accesses k = 0

def isConsistentBalanced (accesses : LookupAccessList) : Prop :=
  ∀ (k : LookupKey), multiplicitySum accesses k = 0

theorem isConsistentBalanced_implies_isConsistentOnline
    (accesses : LookupAccessList) :
    isConsistentBalanced accesses → isConsistentOnline accesses := by
  intro h k _; exact h k

theorem isConsistentBalanced_perm (l1 l2 : LookupAccessList)
    (h_perm : l1.Perm l2)
    (h_bal : isConsistentBalanced l1) :
    isConsistentBalanced l2 := by
  intro k
  rw [← multiplicitySum_perm l1 l2 h_perm k]
  exact h_bal k

/--
  Filtered to a single `(table_id, entry)`, balanced iff multiplicities
  literally sum to zero. Single-key analog of `isConsistentSingleAddress`
  from OfflineMemory.
-/
def isConsistentSingleEntry (accesses : LookupAccessList) : Prop :=
  (accesses.map multOf).sum = 0

/-! ## Equivalence theorems (main results) -/

/--
  Filtering preserves the per-key multiplicity sum: filtering on a
  key, then summing, equals summing the multiplicities of accesses
  whose key matches. Direct since `filterKey` is idempotent on
  the key it filters by.
-/
theorem multiplicitySum_filter (accesses : LookupAccessList) (k : LookupKey) :
    multiplicitySum accesses k = multiplicitySum (filterKey accesses k) k := by
  simp only [multiplicitySum, filterKey, List.filter_filter, Bool.and_self]

/--
  The "every observed key sums to zero" form is equivalent to the
  "every key (observed or not) sums to zero" form, because absent
  keys trivially sum to zero. This is the lookup-bus analog of
  `isConsistentSingleAddress_iff` from OfflineMemory: in the lookup
  setting, "online" and "balanced" collapse because the per-key sum
  is permutation-invariant.
-/
theorem isConsistentBalanced_iff_allBalanced (accesses : LookupAccessList) :
    isConsistentBalanced accesses ↔
    (∀ (k : LookupKey),
      (∃ a ∈ accesses, keyOf a = k) →
      multiplicitySum accesses k = 0) := by
  constructor
  · intro h k _; exact h k
  · intro h k
    by_cases h_mem : ∃ a ∈ accesses, keyOf a = k
    · exact h k h_mem
    · -- key k is not present, so filter is empty and sum is 0
      simp only [multiplicitySum, filterKey]
      rw [show (accesses.filter (fun a => keyOf a = k)) = [] from ?_]
      · rfl
      · apply List.filter_eq_nil_iff.mpr
        intro a h_a h_keq
        apply h_mem
        refine ⟨a, h_a, ?_⟩
        simpa using h_keq

/--
  Main theorem (parallel to OfflineMemory's
  `isConsistentOnline_iff_isConsistentOffline`):

  A lookup-access list is consistent online iff there exists *any*
  permutation on which the balanced-key check holds. Since
  `multiplicitySum` is permutation-invariant, the permutation can be
  taken as the identity — the online and balanced forms are pointwise
  equivalent.

  We state the theorem in the permutation-quantified form to mirror
  the OfflineMemory structure (which genuinely needs a *sorted*
  permutation because the memory bus is order-sensitive). For the
  lookup bus the permutation is structurally redundant; we expose it
  to keep API symmetry.
-/
theorem isConsistentOnline_iff_isConsistentBalanced
    (accesses : LookupAccessList) :
    isConsistentOnline accesses ↔
    ∃ permuted : LookupAccessList,
      permuted.Perm accesses ∧ isConsistentBalanced permuted := by
  constructor
  · intro h_online
    refine ⟨accesses, .refl _, ?_⟩
    exact (isConsistentBalanced_iff_allBalanced accesses).mpr h_online
  · rintro ⟨permuted, h_perm, h_bal⟩
    intro k _
    rw [← multiplicitySum_perm permuted accesses h_perm k]
    exact h_bal k

end LookupAccessList

/-! ## Circuit-level surface: multiplicity-weighted lookup primitive

These structures parallel Clean's `Lookup` / `Operation` / `Circuit`,
but with an explicit multiplicity `Expression F` on each lookup.

Once landed, chips can call `lookupGated mult table entry` to emit a
multiplicity-weighted lookup directly. The chip-level soundness/
completeness obligations carry the multiplicity through, so e.g.
ALUTypeReader can emit `lookupGated (is_real - imm_c) ByteOpcodeTable
op_c_diff_entry` — vacuous on rows where `is_real = imm_c`, active
where they differ.

The chip-level Clean `Spec` for a gated lookup is:
  `mult.eval env = 0 ∨ table.Soundness data (entry.map env)`
which directly mirrors the multiset-balance semantics.
-/

namespace SP1Lookup

variable {F : Type} [Field F]

/-! ## `HasDefaultRow` typeclass

To make `lookupGated` honest in completeness (closing the gap noted in
SP1Clean/AddwChip/Circuit.lean), the prover needs to supply a known-valid
table row when the multiplicity is zero. We expose this per-table via a
typeclass: each user of `lookupGated` registers a default row plus a
proof that it satisfies the table's `Completeness` predicate.

The hint-witness pattern in `lookupGated` (below) uses `defaultRow` as
the witness when `mult.eval env = 0` and `entry.map env` otherwise.
-/

/-- A typeclass providing a known-valid default row for a specific table.
The `defaultRow_in_table` invariant lets the hint-witness `lookupGated`
satisfy completeness uniformly when the multiplicity is zero. -/
class HasDefaultRow {F : Type} [Field F] {Row : TypeMap} [ProvableType Row]
    (table : Table F Row) where
  defaultRow : Row F
  defaultRow_in_table : ∀ data, table.Completeness data defaultRow

/-- Default row for `SP1Clean.ByteOpcodeTable`: the U8Range-opcode-0 row.
`U8Range 0 0 0` checks `0 < 256 ∧ 0 < 256 ∧ 0 < 256`, which holds under
`Fact (p > 512)` (then `(256 : ZMod p).val = 256`). -/
instance ByteOpcodeTable.hasDefaultRow
    {p : ℕ} [Fact p.Prime] [Fact (p > 512)] :
    HasDefaultRow (SP1Clean.ByteOpcodeTable : Table (ZMod p) (fields 4)) where
  defaultRow := #v[(3 : ZMod p), 0, 0, 0]
  defaultRow_in_table := by
    intro _
    -- Completeness = ByteOpcodeSpec. Witness bop = U8Range; toNat = 3; constraint
    -- is `0 < 256 ∧ 0 < 256 ∧ 0 < 256` on (0, 0, 0).
    refine ⟨.U8Range, ?_, ?_⟩
    · simp [ByteOpcode.toNat]
    · simp only [ByteOpcode.constrain]
      have hp : p > 512 := Fact.out
      have h_256 : (256 : ZMod p).val = 256 := by
        rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      refine ⟨?_, ?_, ?_⟩
      all_goals
        change (_ : ZMod p).val < (_ : ZMod p).val
        simp [ZMod.val_zero, h_256]

/--
  Multiplicity-aware lookup. Parallel to `Clean.Circuit.Lookup` but
  carries a `mult` field with the per-row multiplicity contribution.
-/
structure Lookup' (F : Type) where
  table : RawTable F
  entry : Vector (Expression F) table.arity
  mult : Expression F

namespace Lookup'

variable {F : Type} [Field F]

/--
  Per-row soundness for a multiplicity-weighted lookup: either the
  multiplicity evaluates to zero (the row contributes nothing), or
  the entry is in the table's Soundness predicate.
-/
def Soundness (lookup : Lookup' F) (env : Environment F) : Prop :=
  lookup.mult.eval env = 0 ∨
    lookup.table.Soundness (env.data lookup.table.name lookup.table.arity)
      (lookup.entry.map env)

/--
  Per-row completeness: prover can always satisfy the lookup
  contribution either by setting `mult = 0` or by witnessing a valid
  table entry. (Mirror of `Lookup.Completeness` from
  `Clean/Circuit/Lookup.lean` line 84, generalized.)
-/
def Completeness (lookup : Lookup' F) (env : Environment F) : Prop :=
  lookup.mult.eval env = 0 ∨
    lookup.table.Completeness (env.data lookup.table.name lookup.table.arity)
      (lookup.entry.map env)

end Lookup'

/-! ## Circuit-level integration

`Operation'` extends Clean's `Operation` with a fourth constructor for
gated lookups. To keep the sketch self-contained without forking the
entire `Circuit` monad, we expose just the new primitive as a thin
shim that emits a regular lookup *plus* a multiplicative gate
witnessing the multiplicity ≠ 0 case. The gate-based shim is
operationally equivalent for chips that only need the soundness
direction.

Production rollout (Phase 2 of this design) would extend
`Clean.Circuit.Operations.Operation` and re-thread `Circuit.Soundness`
to dispatch on the multiplicity. -/

/--
  Hint-witness `lookupGated`: emit a multiplicity-gated lookup that is
  vacuous when `mult.eval env = 0` and proves `entry ∈ table` when
  `mult.eval env ≠ 0`.

  **Mechanism:**
  1. Witness `hint : Vector F (size Row)` = `entry.map (·.eval env)` when
     `mult.eval env ≠ 0`, else the `HasDefaultRow.defaultRow` flattened to
     elements.
  2. Emit `Circuit.lookup table hint` (always — proves `hint ∈ table`).
  3. For each component i, emit `mult * (entry[i] - hint[i]) = 0` —
     forces `hint = entry` when `mult ≠ 0`, vacuous when `mult = 0`.

  **Soundness:** if `mult = 0`, left disjunct trivially holds. If `mult ≠ 0`,
  the per-component gates force `entry[i].eval = hint[i].eval`, so by the
  underlying lookup soundness, `entry.map env ∈ table`.

  **Completeness:** the prover supplies a valid table row regardless of
  `mult`: either `entry` itself (when `mult ≠ 0` and the chip's Spec
  guarantees `entry ∈ table`) or `defaultRow` (when `mult = 0`, validity
  comes from `HasDefaultRow.defaultRow_in_table`). The per-component
  gates' completeness obligation reduces to `mult * 0 = 0` or
  `0 * (entry - hint) = 0`, both trivial.
-/
@[circuit_norm]
def lookupGated
    {F : Type} [Field F] [DecidableEq F]
    {Row : TypeMap} [ProvableType Row]
    (table : Table F Row) [HasDefaultRow table]
    (entry : Row (Expression F))
    (mult : Expression F) :
    Circuit F Unit := do
  let n := size Row
  -- Witness the hint as a Vector of field elements.
  let hint ← witnessVector n (fun env =>
    if mult.eval env ≠ 0 then toElements (eval env entry)
    else toElements (HasDefaultRow.defaultRow (table := table)))
  -- Emit unconditional lookup of the hint via the underlying lookup table.
  Circuit.lookup table (fromElements hint)
  -- Per-component gates: mult * (entry[i] - hint[i]) === 0 for every i.
  -- We use `Circuit.forEach` over a zipped vector so the `circuit_norm`
  -- simp set's `forEach.soundness` / `forEach.completeness` lemmas fire,
  -- giving us per-`Fin n` access to each gate in the bridge lemmas below.
  let diffs := ((toElements entry).zip hint).map fun (e, h) => mult * (e - h)
  Circuit.forEach diffs assertZero

/-! ## Bridge lemmas: lookupGated ↔ disjunctive Spec

These let chip-level `Assertion` definitions that compose multiple
`lookupGated` calls (see `SP1Clean/Reader/OperandAccess.lean`'s
`AssertionGated`) discharge the chip-level soundness and completeness
obligations by case-splitting on `mult.eval env`. The bridge is one-way
syntactic: the disjunctive Spec is equivalent to the circuit's
constraints under appropriate witness-extension hypotheses.

The two lemmas correspond to the soundness and completeness directions
of a `FormalAssertion` whose `Spec` is the disjunctive form. -/

/-- **Soundness bridge.** If `lookupGated`'s circuit constraints hold,
then either the multiplicity is zero (and the row contributes nothing
to the bus) or the entry is in the table. -/
theorem lookupGated_implies_disjunctive
    {F : Type} [Field F] [DecidableEq F]
    {Row : TypeMap} [ProvableType Row]
    (table : Table F Row) [HasDefaultRow table]
    (entry : Row (Expression F)) (mult : Expression F)
    (env : Environment F) (offset : ℕ)
    (h_holds : Circuit.ConstraintsHold.Soundness env
        ((lookupGated table entry mult).operations offset)) :
    mult.eval env = 0 ∨
      table.Soundness (env.data.getTable table) (eval env entry) := by
  by_cases h_mult : mult.eval env = 0
  · exact Or.inl h_mult
  right
  -- Expose the witness/lookup/gates structure.
  simp only [lookupGated, circuit_norm] at h_holds
  obtain ⟨h_lookup, h_gates⟩ := h_holds
  -- The witnessed `hint` is `Vector.mapRange (size Row) fun i => var ⟨offset + i⟩`.
  -- From each gate (`mult * (entry[i] - hint[i]) = 0` with `mult ≠ 0`), get
  -- `hint[i].eval env = entry[i].eval env` elementwise.
  have h_hint_eq_entry :
      Vector.map (Expression.eval env)
          (Vector.mapRange (size Row) fun i => var (F := F) ⟨offset + i⟩) =
        Vector.map (Expression.eval env) (toElements entry) := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_map]
    have h := h_gates ⟨i, hi⟩
    simp only [Vector.getElem_map, Vector.getElem_zip, Fin.val_mk,
               Expression.eval] at h
    -- `h : mult.eval env * (entry[i].eval env + -hint[i].eval env) = 0`
    have h_diff : (toElements entry)[i].eval env +
        -(Vector.mapRange (size Row) fun i => var (F := F) ⟨offset + i⟩)[i].eval env
          = 0 :=
      (mul_eq_zero.mp h).resolve_left h_mult
    exact (add_neg_eq_zero.mp h_diff).symm
  -- Convert `h_lookup` from the underlying `Lookup.Soundness` form to the
  -- target `table.Soundness ...` form, then rewrite the hint vector to entry.
  simp only [Lookup.Soundness, Table.toRaw] at h_lookup
  -- `convert` matches `table.Soundness X Y` up to per-argument equality.
  -- Arg 1 (`env.data.getTable table`) reduces to the same form; only arg 2 differs.
  convert h_lookup using 2
  simp only [CircuitType.eval_expression]
  exact congrArg fromElements h_hint_eq_entry.symm

/-- **Completeness bridge.** From the disjunctive Spec plus the chip's
`UsesLocalWitnesses` hypothesis (so the witness compute function is
honored), `lookupGated`'s circuit constraints are satisfied. -/
theorem lookupGated_completeness_of_disjunctive
    {F : Type} [Field F] [DecidableEq F]
    {Row : TypeMap} [ProvableType Row]
    (table : Table F Row) [HasDefaultRow table]
    (entry : Row (Expression F)) (mult : Expression F)
    (env : ProverEnvironment F) (offset : ℕ)
    (h_env : env.UsesLocalWitnessesCompleteness offset
        ((lookupGated table entry mult).operations offset))
    (h_disj : mult.eval env.toEnvironment = 0 ∨
      table.Completeness (env.toEnvironment.data.getTable table)
        (eval env.toEnvironment entry)) :
    Circuit.ConstraintsHold.Completeness env
      ((lookupGated table entry mult).operations offset) := by
  simp only [lookupGated, circuit_norm] at h_env ⊢
  -- After circuit_norm:
  -- h_env : ∀ i : Fin n, env.get (offset + i) =
  --   (if mult.eval env ≠ 0 then toElements (eval env entry)
  --    else toElements defaultRow)[i.val]
  -- goal : Lookup.Completeness env ⟨table.toRaw, hint_vars⟩ ∧
  --        ∀ i : Fin n, (mult * (entry[i] - hint[i])).eval env = 0
  -- where hint_vars := Vector.mapRange n (fun i => var ⟨offset + i⟩).
  -- Lemma: each hint var evaluates to the compute function at that index.
  have h_hint_vals : ∀ (i : Fin (size Row)),
      (Vector.mapRange (size Row) fun i => var (F := F) ⟨offset + i⟩)[i.val].eval
          env.toEnvironment =
        (if mult.eval env.toEnvironment ≠ 0 then
            toElements (eval env.toEnvironment entry)
          else toElements (HasDefaultRow.defaultRow (table := table)))[i.val] := by
    intro i
    rw [Vector.getElem_mapRange]
    exact h_env i
  refine ⟨?_, ?_⟩
  · -- Lookup completeness.
    simp only [Lookup.Completeness, Table.toRaw]
    by_cases h_mult : mult.eval env.toEnvironment = 0
    · -- Hint witnesses `defaultRow`; HasDefaultRow.defaultRow_in_table closes it.
      have h_hint_eq_default :
          Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange (size Row) fun i => var (F := F) ⟨offset + i⟩) =
            toElements (HasDefaultRow.defaultRow (table := table)) := by
        apply Vector.ext
        intro i hi
        rw [Vector.getElem_map, h_hint_vals ⟨i, hi⟩, if_neg (by simp [h_mult])]
      rw [h_hint_eq_default, ProvableType.fromElements_toElements]
      exact HasDefaultRow.defaultRow_in_table _
    · -- Hint witnesses `entry`; h_disj's right branch closes it.
      have h_hint_eq_entry :
          Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange (size Row) fun i => var (F := F) ⟨offset + i⟩) =
            toElements (eval env.toEnvironment entry) := by
        apply Vector.ext
        intro i hi
        rw [Vector.getElem_map, h_hint_vals ⟨i, hi⟩, if_pos (by simp [h_mult])]
      rw [h_hint_eq_entry, ProvableType.fromElements_toElements]
      -- Goal: table.Completeness (data.map fromElements) (eval env entry)
      -- which matches h_disj's right branch after unfolding ProverData.getTable.
      exact h_disj.resolve_left h_mult
  · -- Each gate: `(mult * (entry[i] - hint[i])).eval env = 0`.
    intro i
    simp only [Vector.getElem_map, Vector.getElem_zip, Fin.val_mk, Expression.eval]
    by_cases h_mult : mult.eval env.toEnvironment = 0
    · rw [show Expression.eval env mult = mult.eval env.toEnvironment from rfl, h_mult]
      ring
    · -- hint[i] = entry[i] under env, so the difference is zero.
      have h := h_hint_vals i
      rw [if_pos (by simp [h_mult])] at h
      -- h : hint[i].eval env = (toElements (eval env entry))[i.val]
      -- Translate (toElements (eval env entry))[i.val] to (toElements entry)[i.val].eval env.
      have h_entry_unfold :
          (toElements (eval env.toEnvironment entry))[i.val] =
            (toElements entry)[i.val].eval env.toEnvironment :=
        (ProvableType.getElem_eval_toElements entry i.val i.isLt).symm
      rw [h_entry_unfold] at h
      rw [show Expression.eval env = Expression.eval env.toEnvironment from rfl]
      rw [← h]; ring

/-! ## `byteOpcodeGated` — `lookupGated` for `ByteOpcodeTable` as a `FormalAssertion`

Wraps a single `lookupGated` call on `ByteOpcodeTable` into a Clean
`FormalAssertion` so chips can compose it like any other subcircuit.
Specialized to `ByteOpcodeTable` because that table's `Soundness` /
`Completeness` predicates are data-independent (literally `ByteOpcodeSpec
row`), so the chip-level `Spec` is expressible as `Inputs → Prop`. -/

namespace ByteOpcodeGated

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- Inputs: the 4-element entry row and the shared multiplicity. -/
structure Inputs (F : Type) where
  entry : Vector F 4
  mult : F
deriving ProvableStruct

@[reducible, circuit_norm]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Lookup.lookupGated SP1Clean.ByteOpcodeTable input.entry input.mult

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.ByteOpcodeGated"
  main := main
  localLength _ := 4
  localLength_eq _ _ := by simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Disjunctive Spec: vacuous when `mult = 0`; otherwise asserts the
entry satisfies the byte-opcode spec. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨ SP1Clean.ByteOpcodeSpec input.entry

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  intro offset env input_var input h_input _ h_holds
  have h := SP1Lookup.lookupGated_implies_disjunctive
    SP1Clean.ByteOpcodeTable input_var.entry input_var.mult env offset h_holds
  subst h_input
  change (eval env input_var).mult = 0 ∨ SP1Clean.ByteOpcodeSpec (eval env input_var).entry
  simp only [circuit_norm]
  rcases h with h_zero | h_in_table
  · exact Or.inl h_zero
  · right; convert h_in_table; funext x; simp [circuit_norm]

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  intro offset env input_var h_env input h_input _ h_spec
  apply SP1Lookup.lookupGated_completeness_of_disjunctive
    SP1Clean.ByteOpcodeTable input_var.entry input_var.mult env offset h_env
  subst h_input
  change (eval env input_var).mult = 0 ∨
      SP1Clean.ByteOpcodeSpec (eval env input_var).entry at h_spec
  simp only [circuit_norm] at h_spec
  rcases h_spec with h_zero | h_in_table
  · exact Or.inl h_zero
  · right; convert h_in_table; funext x; simp [circuit_norm]

end ByteOpcodeGated

/-- Multiplicity-gated single-row byte-opcode lookup, as a Clean
`FormalAssertion`. The chip-level Spec is the disjunctive form
`mult = 0 ∨ ByteOpcodeSpec entry`. -/
@[reducible]
def byteOpcodeGated {p : ℕ} [Fact p.Prime] [Fact (p > 512)] :
    FormalAssertion (ZMod p) ByteOpcodeGated.Inputs :=
  { ByteOpcodeGated.elaborated with
    Assumptions := ByteOpcodeGated.Assumptions,
    Spec := ByteOpcodeGated.Spec,
    soundness := ByteOpcodeGated.soundness,
    completeness := ByteOpcodeGated.completeness }

end SP1Lookup

/-! ## Bridge: per-row Clean assertion to trace-level bus contribution

Each chip's per-row `FormalAssertion` has a corresponding contribution
to the trace-level `LookupAccessList`. The bridge is provided by a
function `ChipRow.lookupAccesses : ChipRow → LookupAccessList` that
walks the row's emitted constraints and emits the corresponding
`(table_id, entry, multiplicity)` triples.

Trace-level soundness is then the SP1-style claim:

  `aggregateLookupAccesses (rows) |>.isConsistentOnline`

— which by `isConsistentOnline_iff_isConsistentBalanced` reduces to the
decidable offline check.

This parallels how
`SP1Clean/Soundness/MemoryConsistency.lean` aggregates `MemoryAccess`
records across `ChipRow` constructors, except for the lookup bus
instead of the memory bus.
-/

namespace LookupAccessList

/-- Concatenate per-row lookup accesses into a single trace-level list. -/
def aggregateChipRows {α : Type}
    (rows : List α)
    (perRow : α → LookupAccessList) : LookupAccessList :=
  rows.flatMap perRow

/--
  The trace-level claim that downstream `Soundness/LookupConsistency.lean`
  (yet to be written; parallel to `Soundness/MemoryConsistency.lean`)
  would discharge: aggregated per-row lookup accesses form a balanced bus.

  Parallel to
  `SP1Clean.Soundness.MemoryConsistency.chip_specs_admit_offline_bridge`.
-/
def TraceLookupConsistent {α : Type}
    (rows : List α)
    (perRow : α → LookupAccessList) : Prop :=
  (aggregateChipRows rows perRow).isConsistentOnline

end LookupAccessList
