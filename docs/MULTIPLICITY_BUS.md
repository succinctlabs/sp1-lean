# Multiplicity-aware lookup bus — work in progress toward a new canonical representation

**Status (2026-05-25):** foundation laid (Phases 1+2 of 6 complete; both
verified axiom-clean via `lean_verify`). Two material `sorry`s in
`SP1Clean/AddwChip/Circuit.lean:152` and
`SP1Clean/Soundness/MemoryConsistency.lean:1067` are still open, with
clearly-documented closure paths.

> **Heads-up for a fresh Claude instance picking this up:** the soundness
> story is sealed (Phase 1+2 verified), but the chip-level proof refactor
> to actually close the sorries (Phases 3–5) is non-trivial — likely
> 200–400 LoC across `AddwChip/Circuit.lean`, a new bridge lemma in
> `SP1Memory.lean`, and `Soundness/MemoryConsistency.lean`. Don't dive
> into the chip refactor without first reading this doc end-to-end and
> the architectural memo at the top of `SP1Clean/SP1Memory.lean`.

## What we're moving toward (the new canonical representation)

SP1's actual cross-row interaction model is a **multiplicity-weighted
multiset bus** — each chip row contributes `(table_id, entry, multiplicity)`
triples to one of several typed buses (Memory, Byte, Program, PageProt, …),
and global soundness reduces to "for each `(kind, table_id, entry)` key,
the multiplicity sum over all rows is zero." The SP1 prover protocol
(log-derivative / GKR) verifies this multiset balance.

Clean's current per-row `lookup` primitive is **multiplicity-1 only** —
every emitted lookup unconditionally claims `entry ∈ table`. This is
strictly stronger than SP1's `send X with multiplicity (is_real - imm_c)`,
which contributes 0 to the bus on rows where `mult = 0` (ADDIW rows for
op_c, etc.). The mismatch produces a chip-level **completeness gap**:
the SP1 prover is free to put garbage in `op_c_memory` fields on ADDIW
rows, but our unconditional `lookup` would fail to verify.

The canonical representation we're building toward in `SP1Clean/SP1Memory.lean`
introduces a `lookupGated` primitive that is genuinely vacuous when the
multiplicity expression evaluates to 0, plus an `InteractionKind`-tagged
`LookupAccess` data type that mirrors SP1's `AirInteraction<E>` from
`crates/hypercube/src/air/interaction.rs`. Trace-level consistency uses
a new parallel `ChipRow.lookupAccesses` aggregator alongside the existing
`ChipRow.memoryAccesses` (memory-bus stays distinct, mirroring SP1's
`InteractionKind` separation).

## SP1 Rust source of truth

The canonical pattern lives at:

- **`/home/devontuma/Documents/sp1/crates/core/machine/src/air/memory.rs`**
  — `MemoryAirBuilder` trait, `eval_memory_access_{read,write}` and
  `eval_register_access_{read,write}` methods, `do_check` multiplicity,
  send/receive bus pattern (lines 20–216). This is the single most
  important file for understanding what we're mirroring.

- **`/home/devontuma/Documents/sp1/crates/core/machine/src/memory/consistency/columns.rs`**
  — `MemoryAccessCols`, `MemoryAccessTimestamp` with 5 fields
  (`prev_high, prev_low, compare_low, diff_low_limb, diff_high_limb`).
  Our Lean models only 2 fields (`prev_low + diff_low_limb`); the other
  3 are the cross-shard generalization not yet mirrored.

- **`/home/devontuma/Documents/sp1/crates/hypercube/src/air/interaction.rs`**
  — `AirInteraction<E>` struct (`values, multiplicity, kind`) and
  `InteractionKind` enum (Memory=1, Byte=5, Program, PageProt=18,
  PageProtAccess=19). Phase 1 mirrors the enum into Lean.

- **`/home/devontuma/Documents/sp1/crates/core/machine/src/adapter/register/alu_type.rs`**
  line 142 — the source-of-truth for AddwChip's op_c gating:
  `builder.eval_register_access_read(..., is_real - cols.imm_c)`. This
  is the specific multiplicity that closes the AddwChip op_c completeness
  gap.

## What's done (Phase 1 + Phase 2)

Both phases are merged into `SP1Clean/SP1Memory.lean` (~470 LoC) and
verified clean via `lean_verify`.

### Phase 1 — refine SP1Memory.lean to mirror memory.rs

**Added:** `InteractionKind` enum (Memory, Byte, Program, PageProt,
PageProtAccess, State) with `DecidableEq, Repr, Inhabited`.

**Widened:** `LookupAccess` from `(String × List ℕ × ℤ)` to
`(InteractionKind × String × List ℕ × ℤ)`. The discriminator
distinguishes byte-bus and memory-bus contributions at the trace-level
aggregator.

**Migration result:** all 11 existing consistency theorems
(`multiplicitySum_perm`, `isConsistentBalanced_perm`,
`isConsistentBalanced_iff_allBalanced`,
`isConsistentOnline_iff_isConsistentBalanced`, etc.) survived the
widening *without proof changes* — the math is structural over
`List.sum` and didn't depend on the `LookupAccess` shape. All four
re-verified axiom-clean (`propext, Classical.choice, Quot.sound` only).

**Added:** `HasDefaultRow` typeclass parameterized by table:
```lean
class HasDefaultRow (table : Table F Row) where
  defaultRow : Row F
  defaultRow_in_table : ∀ data, table.Completeness data defaultRow
```
**Instance:** `SP1Clean.ByteOpcodeTable` → `#v[(3 : ZMod p), 0, 0, 0]`
(U8Range-opcode row with all-zero args; completeness derives from
`(256 : ZMod p).val = 256` under `Fact (p > 512)`). Proof axiom-clean.

**Deferred:** the `MemoryAccessTimestamp` 5-field structure and the full
`eval_memory_access_{read,write}` API surface. Not needed for closing
the sorries; documented as future work.

### Phase 2 — real hint-witness `lookupGated`

**Replaced:** the `Circuit.lookup`-shim definition with a true hint-witness
implementation:
```lean
def lookupGated table entry mult := do
  let n := size Row
  let hint ← witnessVector n (fun env =>
    if mult.eval env ≠ 0 then toElements (eval env entry)
    else toElements (HasDefaultRow.defaultRow (table := table)))
  Circuit.lookup table (fromElements hint)
  for h : i in [:n] do
    assertZero (mult * (entry[i]'h.2.1 - hint[i]'h.2.1))
```

**Semantics:** when `mult.eval env = 0`, the per-component gates are
vacuous and the hint is `defaultRow` (which is in the table); when
`mult.eval env ≠ 0`, the gates force `hint = entry` and the underlying
lookup proves `entry ∈ table`.

**Disjunctive Spec** (the multiplicity-aware target):
```
mult.eval env = 0 ∨ table.Soundness data (entry.map env)
```

## What's still TODO (Phases 3–5)

The two `sorry`s remaining in the codebase both stem from the same root
cause: AddwChip's `Assertion.main` uses unconditional `OperandAccess.assertion`
for op_c, while its `FormalSpec` is in the disjunctive
multiplicity-aware form. This mismatch is what Phases 3–5 close.

### Phase 3 — chip refactor + close `AddwChip/Circuit.lean:152`

**The sorry** (line 152, completeness):
```lean
· refine ⟨trivial, ?_⟩
  exact h_oc_disj.resolve_left (by sorry)
```
The chip has no way to discharge the `Or.inl (mult_c = 0)` branch because
the underlying `OperandAccess.assertion` requires the byte rows unconditionally.

**Closure mechanism:**

1. **Add a bridge lemma in `SP1Clean/SP1Memory.lean`** stating that
   `lookupGated`'s circuit constraint discharge implies the disjunctive
   Spec form:
   ```lean
   theorem lookupGated_implies_disjunctive
       {Row : TypeMap} [ProvableType Row]
       (table : Table F Row) [HasDefaultRow table]
       (entry : Row (Expression F)) (mult : Expression F)
       (env : Environment F) (data : Array (Row F)) :
       /-- pseudo: -/ ConstraintsHold env (lookupGated table entry mult) →
       mult.eval env = 0 ∨ table.Soundness data (entry.map env)
   ```
   Proof mechanism: extract the underlying `Circuit.lookup` soundness
   (gives `table.Soundness data hint`), extract the per-component gate
   facts (`mult * (entry[i] - hint[i]) = 0`), then case-split on
   `mult.eval env`. The exact statement form depends on how
   `circuit_proof_start` shapes `h_holds` for the `witnessVector +
   lookup + n gates` sequence.

2. **Refactor `SP1Clean/AddwChip/Circuit.lean`'s `Assertion.main`** to
   replace the op_c `OperandAccess.assertion` call with 6 inline
   `lookupGated` calls:
   ```lean
   let mult_c := is_real - imm_c
   SP1Lookup.lookupGated SP1Clean.ByteOpcodeTable
     (#v[6, op_c_memory.access_timestamp.diff_low_limb, 16, 0] : ...) mult_c
   SP1Lookup.lookupGated SP1Clean.ByteOpcodeTable
     (#v[3, 0, scaled_ts, 0] : ...) mult_c
   -- 4 more for prev_value[0..3] in Range 16
   ```
   Note the prior abortive refactor in this direction is at git history
   commit ~`Wired AddwChip op_c` (since reverted). The challenge there
   was the chip's destructure / form-unification with the new circuit
   shape; the bridge lemma in step 1 should make it tractable now.

3. **Update soundness** to discharge the disjunctive form via the bridge
   lemma instead of `Or.inr ∘ unconditional_spec`.

4. **Update completeness** to dispatch on the disjunctive form: when
   `mult_c = 0`, the lookupGated's hint witnesses `defaultRow`
   (completeness via `HasDefaultRow`); when `mult_c ≠ 0`, the chip's
   Spec gives `entry ∈ table` and the gates auto-hold.

### Phase 4 — parallel `ChipRow.lookupAccesses` aggregator

Mirror `ChipRow.memoryAccesses` (line 121 of `MemoryConsistency.lean`)
with a new `ChipRow.lookupAccesses : ChipRow p → LookupAccessList`
accessor. For each chip constructor, emit `(InteractionKind.Byte, table_id,
entry, mult)` and `(InteractionKind.Program, table_id, entry, mult)`
tuples. AddwChip's case specifically tags op_c byte lookups with
`mult = is_real - imm_c` rather than 1.

Add `aggregateLookupAccesses` + `TraceLookupConsistent` (skeleton
already in `SP1Memory.lean`'s tail; just needs the per-chip
`lookupAccesses` projections wired in).

### Phase 5 — close `MemoryConsistency.lean:1067`

**The sorry** (line 1067, trace-level companion):
```lean
· subst h
  exact h_oa_c_disj.resolve_left (by sorry)
```

**Closure mechanism:** modify `ChipRow.memoryAccesses (.addw cols)` to
*conditionally* include the op_c entry based on `cols.adapter.imm_c = 0`.
The current implementation unconditionally emits 3 memory access entries
(op_a/op_b/op_c) for AddwChip rows; the gated version emits 2 or 3 based
on imm_c.

After this change, `memoryAccessesValid_of_spec_addw`'s
`rcases h_mem with h | h | h` becomes a 2-or-3 way split. The op_c case
only fires when `imm_c = 0`, in which case `mult_c = is_real - 0 = 1 ≠ 0`,
and `h_oc_disj.resolve_left` is provable structurally.

**Caveat:** `ChipRow.offsets (.addw cols)` (line 632 of `MemoryConsistency.lean`)
currently emits a fixed-length `[2, 3, 4]` for AddwChip; this also needs
parallel imm_c-conditional emission to stay in sync with the conditional
`memoryAccesses`.

### Phase 6 — verification

Standard end-to-end:
- `lake build SP1Clean` → 0 errors, 2 unrelated `sorry` warnings only
  (`LoadX0Chip.lean:182`, `DivRemChip.lean:271` — unrelated half-iff
  bridge gaps).
- `lean_verify` axiom check on `Addw.Assertion.completeness`,
  `memoryAccessesValid_of_spec_addw`, `lookupGated`, all 11 SP1Memory.lean
  theorems.
- `git grep -n "sorry" SP1Clean/AddwChip/ SP1Clean/SP1Memory.lean
  SP1Clean/Soundness/MemoryConsistency.lean` → both target sorries
  closed, no new sorries introduced.
- Backward compat: AddChip, AddiChip, the 18 other chips using
  unconditional `OperandAccess.assertion` should be untouched.

## Key files (in dependency order)

**Foundation (Phase 1+2 — done):**
- `SP1Clean/SP1Memory.lean` (~470 LoC) — multiplicity-aware bus
  machinery; `InteractionKind`, `LookupAccess`, `HasDefaultRow`,
  `lookupGated`, 11 axiom-clean consistency theorems. The architectural
  memo at the top of the file is the primary on-disk reference for the
  new canonical representation.

**Bridge to chips (Phase 3 — TODO):**
- `SP1Clean/AddwChip/Circuit.lean` (~177 LoC) — has the `sorry` at line
  152 in `Assertion.completeness`. The chip's `FormalSpec` is already in
  the disjunctive form; refactoring `Assertion.main` to use `lookupGated`
  for op_c lookups closes the gap.
- `SP1Clean/Reader/OperandAccess.lean` (~217 LoC) — the unconditional
  6-byte-lookup subcircuit currently used for op_c. AddwChip currently
  composes this; the refactor either replaces the call with 6 inline
  `lookupGated` calls OR adds a parallel `OperandAccess.assertionGated`
  variant (designer's choice — the audit recommended inline for
  smaller-scope demonstration).

**Trace-level (Phase 4+5 — TODO):**
- `SP1Clean/Soundness/MemoryConsistency.lean` (~1190 LoC) — has the
  `sorry` at line 1067 in `memoryAccessesValid_of_spec_addw`. Phase 4
  adds a parallel `ChipRow.lookupAccesses` accessor; Phase 5 closes
  the sorry by conditionalizing `ChipRow.memoryAccesses (.addw cols)`
  on `imm_c = 0`.

**Reference (unchanged):**
- `Clean/Utils/OfflineMemory.lean` (~931 LoC, in `.lake/packages/Clean/`)
  — the existing memory-bus consistency proof that SP1Memory.lean's
  lookup-bus structure parallels. Read its main theorem
  `isConsistentOnline_iff_isConsistentOffline` (lines 906–931) for the
  template structure.

## Patterns and gotchas a fresh instance needs to know

1. **`circuit_proof_start` + `subst_eqs` shape.** After these tactics in
   a chip's soundness/completeness proof, `h_holds` is a tuple of
   subcircuit-`.Spec` arrows and inline-gate equalities, *in the order
   they appear in `Assertion.main`*. When you refactor `main` to add or
   remove subcircuit calls, the destructure pattern *must* match exactly
   or you get cryptic unification errors. See
   `SP1Clean/AddChip/Circuit.lean` for the canonical destructure shape.

2. **`lookupGated`'s for-loop syntax.** Lean's `for h : i in [:n] do ...`
   gives `h : ∃ i ∈ [:n], (...)`. To extract the bound `i < n`, use
   `h.2.1`. So the per-component gate body looks like
   `assertZero (mult * (entry[i]'h.2.1 - hint[i]'h.2.1))`. The
   alternative `have h_lt : i < n := h.2` (which I tried first) fails
   because `h.2` has a more complex range-membership type.

3. **`HasDefaultRow.defaultRow` needs `(table := table)`.** Lean can't
   infer which table's instance to use without the explicit hint, even
   when the `table` argument is in scope. Without it you get "Function
   expected at HasDefaultRow.defaultRow" because Lean treats
   `.defaultRow` as expecting more arguments.

4. **Type widening of `LookupAccess` (Phase 1) was non-breaking.**
   The 11 consistency proofs all use structural `List.sum`/`List.filter`
   properties, not the specific shape of `LookupAccess`. When you add
   the `InteractionKind` factor, none of the existing proofs need
   updating — they widen automatically. *Don't* assume the same will
   hold if you make more invasive changes (e.g., adding the
   `MemoryAccessTimestamp` 5-field generalization). Verify with
   `lean_verify` after each schema change.

5. **The chip's `FormalSpec` is the source of truth, not the circuit.**
   The chip's `Assertion.main` is what the circuit *emits*. The
   `FormalSpec` is what the chip *promises*. Soundness shows
   `circuit ⇒ FormalSpec`; completeness shows `FormalSpec ⇒ circuit`.
   For the AddwChip multiplicity work, the `FormalSpec`'s disjunctive
   form is correct (matches SP1 semantics); the circuit is currently
   over-strong (unconditional `OperandAccess.assertion`). Phase 3 makes
   the circuit match the Spec — the Spec doesn't change.

6. **`subst_eqs` on `e_adapter` is destructure-sensitive.** For ALU-type
   chips (AddwChip), the `e_adapter` equality is a nested conjunction.
   To get the per-leaf substitutions you may need to explicitly
   `obtain ⟨e_op_a, ⟨e_op_a_pv, ...⟩, ...⟩ := e_adapter` before
   `subst_eqs`. See AddwChip's earlier abortive refactor in git history
   for a worked example.

7. **Pre-existing sorries are out of scope.** The two unrelated sorries
   (`LoadX0Chip.lean:182`, `DivRemChip.lean:271`) are half-iff bridge
   gaps from earlier work, completely orthogonal to this multiplicity
   refactor. Don't touch them.

8. **Build hygiene.** Per `CLAUDE.md`: cap of 2–3 concurrent `lake`
   processes. `lake env lean <file>` silently lies on stack overflow
   (cached olean makes downstream checks pass falsely). Finish each
   phase with a full `lake build SP1Clean` and check `lean_verify`.

## Open architectural questions for the next session

These are *design* questions, not just *execution* questions, and worth
re-engaging with the user before plowing through Phases 3–5:

1. **Bridge lemma form.** Should the bridge from `lookupGated`'s
   constraints to the disjunctive Spec be a single top-level theorem
   in `SP1Memory.lean`, or a `@[simp]` lemma that fires during
   chip-level proofs automatically? The former is more explicit; the
   latter is more ergonomic if many chips use `lookupGated`.

2. **`OperandAccess.assertionGated` vs. inline.** The original Phase 3
   plan called for a parallel `OperandAccess.assertionGated`
   subcircuit. The audit later recommended inline 6 `lookupGated` calls
   in AddwChip for smaller scope. Either works; the inline form is
   harder to reuse if other chips later need gated byte-bus lookups
   (e.g., conditional shift cases).

3. **Phase 1 deferred items.** The 5-field `MemoryAccessTimestamp` and
   `eval_memory_access_{read,write}` API were deferred. They're needed
   if/when we want full cross-shard RAM modeling (currently SP1Clean is
   register-shard only). Add as a separate planning ticket; not blocking
   for closing the current sorries.

## What "done" looks like

After Phases 3–5 land successfully:
- The two sorries listed above are closed.
- `lake build SP1Clean` reports 0 errors, 2 warnings (LoadX0Chip,
  DivRemChip — both unrelated).
- `lean_verify SP1Clean.Addw.Assertion.completeness` produces
  `{propext, Classical.choice, Quot.sound}` only.
- `lean_verify
  SP1Clean.Soundness.MemoryConsistency.memoryAccessesValid_of_spec_addw`
  same.
- `SP1Clean/AddwChip/Circuit.lean`'s `Assertion.main` uses `lookupGated`
  for op_c with `mult = is_real - imm_c`; soundness/completeness are
  structurally honest about SP1's gated emission.
- `SP1Clean/Soundness/MemoryConsistency.lean` has a
  `ChipRow.lookupAccesses` accessor and the AddwChip op_c memory
  access is conditional on `imm_c = 0`.

Then the foundation is ready for the *next* user to extend the
multiplicity-aware bus to other chips that have genuinely-gated
lookups (ShiftLeftChip's shift-amount, BranchChip's taken-branch
lookups, etc.).

## Related plan file

The most recent plan for the in-progress work is at
`~/.claude/plans/make-a-plan-to-parsed-pumpkin.md`. It contains the
full Phase 0–6 breakdown including the deferred Phase 1 items
(MemoryAccessTimestamp, eval_memory_access_*). When picking this work
up, read that plan first for the structural overview, then this doc
for the concrete on-disk progress and gotchas.
