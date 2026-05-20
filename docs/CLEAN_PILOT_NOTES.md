# Clean DSL pilot — notes from the spike

Status as of 2026-05-19. Companion to `docs/CLEAN_DSL_EVALUATION.md` and the
plan at `~/.claude/plans/look-at-the-doc-mossy-popcorn.md`.

**Update (later same day).** Reworked along principled lines: checked out a
local branch `sp1-pilot-misc-dedup` in `../clean`, applied the one-line
`Clean/Utils/Misc.lean` dedup, and upgraded Tier 1 to a full re-exported
`FormalCircuit` (inherits Clean's soundness + completeness). Tiers 2a/2c
keep the iff bridge but now compile with idiomatic `<==` / `===` operators
that the dedup patch unblocked. See "After the principled rework" below.

## What landed

A new `SP1Clean/` library inside sp1-lean (wired through `lakefile.toml`
`[[require]] name = "Clean" path = "../clean"`), containing parallel Clean
mirrors for three of SP1's smallest constraint fragments:

- **Tier 1 (no interactions)** — `SP1Clean/IsZeroOperation.lean` mirrors
  `SP1Operations/Compare/IsZeroOperation` (3× `assertZero`).
- **Tier 2a (1 byte send)** — `SP1Clean/U16MSBOperation.lean` mirrors
  `SP1Operations/Operation/U16MSBOperation` (2× `assertZero` + 1× `send
  (.byte Range _ 16 0)`).
- **Tier 2c (8 byte sends, opcode-parametric)** — `SP1Clean/BitwiseOperation.
  lean` mirrors `SP1Operations/Operation/BitwiseOperation` (8× `send (.byte
  (ofNat opcode) _ _ _)`).

The shared lookup table lives in `SP1Clean/ByteOpcodeTable.lean`. The
per-opcode tag (`ByteOpcode.toNat`) was added to `SP1Foundations/ByteOpcode.
lean` to make the encoding usable.

`lake build SP1Clean` is **green with zero errors, zero warnings, zero
sorries** (the `BitwiseOp.ByteOpcodeSpec_of_Spec_when_lt7` connector lemma
closes via `interval_cases`).

## Pre-flight: toolchain

`../clean` is on a **local branch `sp1-pilot-misc-dedup`**, forked off
upstream `bump-lean-4.29` with one patch (`Clean/Utils/Misc.lean` —
delete the duplicate `Fin.foldl_eq_foldl_finRange`). The full `lake build`
of Clean still has 13 leftover errors in `Clean/Utils/SourceSinkPath.lean`
and `Clean/Types/U32.lean` (pre-existing Lean 4.29 mechanical fallout from
the upstream branch, untouched by us), but everything we transitively
import — `Clean.Circuit.{Basic, Provable, Lookup}`, `Clean.Gadgets.
{IsZeroField, Equality}`, `Clean.Utils.Field`, `Clean.Circuit.Loops` — now
all build cleanly.

The dedup patch is a one-liner upstream-PR candidate: Batteries provides
`Fin.foldl_eq_foldl_finRange` verbatim on Lean 4.29+, so Clean's
re-implementation is dead code that breaks any project that pulls both.

## Interactions representation, as exercised

Decision per the pilot plan: **stateless `lookup ByteOpcodeTable entry`**,
not channels. The table's `Contains`/`Soundness`/`Completeness` are all set
to a single `ByteOpcodeSpec` predicate — there's an existential over
`ByteOpcode` whose `toNat` matches the row's first element. We sidestep
`StaticTable` enumeration (no need to list every AND/OR/XOR/Range row at
the pilot scale).

Concrete observations:

1. **U16MSB** — the single byte send mapped to a single `lookup` call,
   completely mechanical. The iff's only non-trivial step was the
   `(16 : F p).val = 16` round-trip, which needed an extra `Fact (p >
   65536)` instance (the existing `Fact (p > 512)` from Clean isn't
   strong enough). For KoalaBear (`p = 2130706433`) this is automatic.

2. **Bitwise** — 8 opcode-parametric sends mapped to 8 `lookup` calls. The
   iff was a pure 8-way `Fin` case-split. **The hard sub-question is
   opcode round-trip**: SP1's send carries `ByteOpcode.ofNat opcode_val`,
   while the Clean table spec is existential over `ByteOpcode`. They only
   agree when `opcode.val < 7` — a discipline the *chip* enforces (e.g.
   via `is_and + is_or + is_xor = 1`), not the operation fragment. The
   pilot exposes this as a separate connector lemma
   (`ByteOpcodeSpec_of_Spec_when_lt7`) closed via `interval_cases`. This
   is the cleanest pilot finding: at the fragment level, the natural Spec
   matches SP1's `toProp_poly` exactly; the lookup-table existential
   bridge is a *separate*, *chip-level* concern.

3. **Multiplicity drop is fine at fragment scale.** Every SP1 send's
   `mult ≠ 0 → P` reduces, under the `is_real = 1` hypothesis we carry,
   to just `P`. The Clean lookup encoding has no multiplicity. The two
   match because the chip-level `is_real = 1` premise discharges the
   guard. The global "balanced multiplicities" property still isn't
   captured — but no fragment-level proof needs it, so the pilot doesn't
   surface this limitation either way.

## Headline friction (and how each was navigated)

1. **`Fin.foldl_eq_foldl_finRange` duplicate declaration.** Clean's
   `Clean/Utils/Misc.lean:62-69` redeclares a lemma that's already in
   `Batteries.Data.Fin.Fold` on Lean 4.29+. Any sp1-lean file importing
   both (e.g. via `Clean.Gadgets.IsZeroField` *and* `SP1Foundations`)
   errors out before any of our code elaborates. **Now fixed locally**
   on the `sp1-pilot-misc-dedup` branch in `../clean`. Recommend
   upstreaming as a PR; the fix is one line.

2. **`FormalCircuit` instances — partial promotion.** With the patch
   applied, Tier 1 (`IsZeroOperation`) is now a full `FormalCircuit`
   re-exported from upstream `Gadgets.IsZeroField` — Clean's
   soundness + completeness inherit for free. Tiers 2a (`U16MSB`) and
   2c (`Bitwise`) still ship as iff-only: the soundness/completeness
   would have to be hand-written against the `ByteOpcodeTable`'s
   existential spec, which requires more fluency with Clean's
   `circuit_norm` / `circuit_proof_all` pattern than the spike budget
   allowed. **Concrete obstruction** when I tried: Clean's `cases bop
   <;> simp_all` doesn't dispatch the false `(n : F p) = 6` branches
   for `n ≠ 6` — needs an explicit field-injectivity step under
   `p > 6`. Tractable, not trivial.

3. **`omit [Fact ...] in` placement.** Lean 4.29 wants `omit [Fact …] in`
   *before* a doc comment, not between the doc comment and the `theorem`
   keyword. Tripped over this three times — adding to the
   `docs/GOTCHAS.md` list isn't a bad idea if the project grows.

## Per-fragment proof effort

- IsZero iff (no interactions): ~25 lines of tactic prose, 3 `by_cases`
  on `a = 0`, two `linear_combination` calls. Took longest of the three
  because of the early circuit-vs-iff phrasing missteps.
- U16MSB iff (1 send): ~25 lines including the `range_at_sixteen` helper.
  The interaction encoding adds essentially nothing to the proof — `simp
  [ofNat_seven]` rewrites the SP1 `ofNat 6` to `Range`, then it's a
  direct match.
- Bitwise iff (8 sends): ~20 lines, dominated by the `Fin 8` case-split.
  The connector lemma to `ByteOpcodeSpec` is another ~15 lines.

Total pilot elaboration time (`lake build SP1Clean`): seconds. No
heartbeat exhaustion, no kernel deep-recursion, no `circuit_norm`
performance issue (we didn't use it). Useful negative data: the proofs
were small enough that we never stressed the elaborator.

## What we learned vs. the evaluation doc's predictions

- **Doc Risk 1 (no KoalaBear in Clean).** Not exercised at the iff level
  — our proofs are field-generic. Would only matter for the deferred
  `FormalCircuit`s, when `circuit_norm` meets KB literals.
- **Doc Risk 4 (`circuit_norm` perf).** Not exercised, same reason.
  Cannot report.
- **Doc Risk 6 (drift).** Now real. `update_constraints.py` regen of any
  of the three mirrored fragments will silently break the corresponding
  `iff_sp1` — we have no CI gate yet. Lowest-cost mitigation: a `lake
  build SP1Clean` line in whatever CI runs on the constraint-regen PR.
- **Doc §5 cost estimate (~50-150 lines per chip).** For these
  *fragments* — much less. ~100 lines per file all-in including iff +
  docstring. For full chips with state/program/memory interactions the
  estimate likely still holds.

## Recommended next steps

In rough priority order:

1. **Land the `Clean/Utils/Misc.lean` upstream patch.** Removes the
   single biggest source of friction; unblocks `FormalCircuit`
   integration and the `<==` / `===` ergonomic surface.
2. **Promote one fragment to a full `FormalCircuit`** (IsZero is the
   easiest target). This validates the soundness/completeness pairing
   end-to-end without the upstream patch landing first — we can use
   raw `witnessField` + manual `Soundness`/`Completeness` proofs.
3. **Pick the next tier.** The plan's Tier 3 was `CPUState` (state
   interactions). Two options:
   - **State interactions via `Channel`.** Forces engaging with the
     multiplicity-preserving encoding the pilot deferred. Likely the
     bigger unknown.
   - **Memory interactions via lookup.** Cheaper continuation of the
     current path; harder to motivate without a chip use site.
4. **Add a CI guard** (cheap): in whatever job watches
   `update_constraints.py` regen, also run `lake build SP1Clean` and
   fail on a non-zero return.
5. **Open an upstream issue / PR** on Verified-zkEVM/clean to surface
   the duplicate-declaration collision and the `bump-lean-4.29`
   completion needs. Even if we don't pursue the use case any further,
   the WIP branch + this pilot's findings are useful to feed back.

## After the principled rework

After the initial pilot landed, we checked out a local branch
`sp1-pilot-misc-dedup` in `../clean` and removed the duplicate
`Fin.foldl_eq_foldl_finRange` (one-line patch in `Clean/Utils/Misc.lean`).
With the import chain unblocked we:

- Rewrote `SP1Clean/IsZeroOperation.lean` to **re-export** upstream's
  `Gadgets.IsZeroField.circuit` as the canonical Clean side, inheriting
  Clean's full soundness + completeness pairing. Added a tiny
  `circuit_Spec_eq_Spec : (circuit (p := p)).Spec = Spec` `rfl` lemma
  to anchor the naming.
- Rewrote `SP1Clean/U16MSBOperation.lean` to use the idiomatic
  `msb * (msb - 1) === 0` operator (was raw `assertZero` before).
  Kept iff-only; FormalCircuit promotion attempted but reverted due to
  proof friction noted in §"Headline friction" #2.
- `BitwiseOperation.lean` is unchanged — its body has no `===`
  asserts, and the same FormalCircuit-promotion friction applies.

End state: `lake build SP1Clean` is still green (0 / 0 / 0 on errors /
warnings / sorries), `BitwiseOp.ByteOpcodeSpec_of_Spec_when_lt7`
remains closed, and Tier 1 now ships with full FormalCircuit
soundness + completeness instead of just the iff bridge.

## File index

- `SP1Clean.lean` — library root (3-line import list)
- `SP1Clean/ByteOpcodeTable.lean` — shared lookup table (53 lines)
- `SP1Clean/IsZeroOperation.lean` — Tier 1 (95 lines)
- `SP1Clean/U16MSBOperation.lean` — Tier 2a (90 lines)
- `SP1Clean/BitwiseOperation.lean` — Tier 2c (115 lines)
- `SP1Foundations/ByteOpcode.lean` — `toNat` definition added (12 new lines)
- `lakefile.toml` — `Clean` require + `SP1Clean` library entries

## Chip-level `FormalAssertion` spike (later landing)

After the principled rework, `AddChip` was promoted to a full Clean
`FormalAssertion` composition. The deliverables:

- `SP1Clean.AddOp.assertion : FormalAssertion (ZMod p) Inputs` — full
  soundness + completeness against `AddOp.Spec`, with 8 byte lookups +
  4 boolean asserts. Axiom set: just `propext`, `Classical.choice`,
  `Quot.sound`.
- `SP1Clean.CPUState.assertion : FormalAssertion (ZMod p) Inputs` —
  same shape, with 2 byte lookups (`Range 13` and `U8Range`) against
  `cpuStateSpec`.
- `SP1Clean.Add.assertion : FormalAssertion (ZMod p) AddCols` —
  composes the two sub-assertions via subcircuit calls plus two
  trailing asserts (`is_real` boolean, `op_a_0 = 0`). Spec is a new
  `FormalSpec` — the byte-lookup-derivable subset of the chip's full
  `Spec`.

**Out of scope as expected**: `RTypeReader`'s full FormalAssertion. Its
constraint surface includes `.program` and `.memory` channel sends that
the pilot deferred to the state-bridge layer (see "Interactions
representation"). `FormalSpec` drops the `rtypeReaderSpec` clause for
this reason. The existing `iff_sp1` and `correct_add` continue to use
the full `Spec` (which includes `rtypeReaderSpec`) and stay untouched.

**Friction navigated**:
1. `circuit_proof_start` puts goals/hypotheses through an `id`-wrapped
   typeclass synthesis that breaks `linear_combination` and
   `mul_eq_zero.mpr`. Workaround: `unfold id at *` once after
   `circuit_proof_start` and before the algebraic reasoning starts.
   Cheap, but needed in every `_poly`-style soundness/completeness.
2. The `ByteOpcodeSpec` existential needs explicit field-injectivity
   per row shape. The pilot's two new helpers
   (`byteOpcodeSpec_range16_of_lt` / `_range13_of_lt` /
   `_u8range_of_lt` for completeness; mirror lemmas for soundness)
   encapsulate this. Each follows the same recipe: `apply_fun
   ZMod.val + Nat.mod_eq_of_lt` to convert `(bop.toNat : ZMod p) = K`
   to `bop.toNat = K` under `Fact (2^17 < p)`, then case-split on
   `bop`. About 20 lines per opcode shape; reusable.
3. `linear_combination`'s `ring` step doesn't see `+ -X` ≡ `- X`
   inside ZMod inverses without `unfold id`, so e.g. proving
   `(a + b + -r) * 65536⁻¹ = (a + b - r) * 65536⁻¹` needs the
   `unfold id at *` workaround.

**End state**: `lake build SP1Clean` is green (0 errors / 0 warnings);
each of the three new `assertion` declarations closes with only the
standard axioms; the existing `iff_sp1` / `correct_add` / `Spec`
machinery is untouched.

**Next bites** (if the spike justifies continuation):
- Promote `Addi`, `Sub`, `Subw` chips — each is a near-copy of
  `AddChip` with an `ITypeReader` swap; the limiting factor is
  whether `ITypeReader` admits a similar byte-only FormalAssertion
  (it should).
- Add a Clean lookup table for the `.memory` channel — the next
  largest unlock, since memory `send`/`receive` would let
  `RTypeReader`'s `isU64_poly` clauses flow through Clean.
- Add a Clean table for the `.program` channel — the deepest unlock,
  letting `trusted_instr_poly` flow through. Probably needs a real
  enumeration (not the stateless lookup encoding we use today).

## Tier 3: state + memory + program interactions (2026-05-19)

The pilot now covers all four SP1 interaction kinds (`byte`, `state`,
`memory`, `program`) — the first three via Clean `lookup`-against-`Table`
calls visible in each chip's `main` Circuit, the fourth (`memory`) via
per-row propositional records aggregated at trace level through
`Clean.Utils.OfflineMemory`.

**Shipped modules**

- `SP1Clean/ProgramTable.lean` — stateless 16-field `ProgramTable`
  mirroring `AirInteraction.program`. Row spec is the existential RHS of
  `SP1Constraint.toProp_poly` for `.program` (opcode `trusted_instr_poly`
  + register bounds + PC alignment + flag binarity). Plus
  `ProgramTable.assertion : FormalAssertion (ZMod p) Inputs` wrapping a
  single lookup as a subcircuit (Inputs struct mirrors `AddCols`'
  Vector-field discipline so subst chains in `circuit_proof_start`
  remain mechanical).
- `SP1Clean/MemoryAccess.lean` — `MemoryAccess` record (addr +
  prev_value + prev_low + diff_low_limb), `memoryAccessSpec` predicate
  (per-row timestamp + U64 bounds matching the reader iff RHS clauses),
  `toAccessTuple` flattener into the 4-tuple shape
  `Clean.Utils.OfflineMemory.MemoryAccess` expects. Reuses
  `SP1Foundations.MemoryConsistency.MemoryAccessInSharedCols` via
  `ofRegisterShared` to bridge from the SP1 reader-struct view.
- `SP1Clean/LoadByteChip.lean` — new chip mirroring `Load.LoadByteChip`
  over 47 columns. Critical pieces: a `loadMemoryAccess` exposing the
  load-side `MemoryAccess` record at the *computed* address
  `addr_value`, which generally hits the RAM branch
  (`addr0.val ≥ 32`) of `SP1Constraint.toStateProp_poly` rather than
  the register-special-case branch — first chip in the pilot to
  exercise that branch.
- `SP1Clean/Soundness/MemoryConsistency.lean` — trace-level bridge.
  `ChipRow` heterogenous wrapper (`.add` + `.loadByte` constructors),
  `aggregateMemoryAccesses` flattens a list of rows into a
  `MemoryAccessList`, `chip_specs_admit_offline_bridge` is the
  parameterized statement of the OfflineMemory main theorem
  (`isConsistentOnline ↔ isConsistentOffline`).

**Chip retrofit**: `AddChip`, `AddiChip`, `SubChip`, `SubwChip`,
`BitwiseChip`, `LoadByteChip` all emit explicit
`SP1Clean.ProgramTable.assertion` subcircuits in their `main`, with the
appropriate opcode encoding (constant for single-opcode chips like
`Add`, selector-arithmetic for fan-out chips like `Bitwise`,
`is_lb * 29 + is_lbu * 32` for `LoadByte`). `AddChip`'s
`FormalAssertion` (`SP1Clean.Add.assertion`) now closes a richer
`FormalSpec` that includes the `ProgramTable.Spec` consequence
alongside the existing `AddOp.Spec` + `cpuStateSpec` + trailing
asserts — first chip in the pilot whose FormalAssertion is *not* a
strict subset of the byte-bus surface.

**Friction encountered**

1. `Clean.Utils.OfflineMemory` in the `../clean` fork has 3
   pre-existing build failures (lines 278, 287, 311 — `simp_all` /
   `simp [filter_cons]` leaving residual decidability goals on Lean
   4.29 / current Mathlib). The pilot side-steps by declaring
   `Soundness/MemoryConsistency.lean`'s shape against a compatible
   local `MemoryAccessTuple := ℕ × ℕ × ℕ × ℕ` abbreviation and
   parameterizing the trace-level theorem over abstract
   `isConsistentOnline`/`isConsistentOffline` predicates plus the
   upstream main equivalence as a hypothesis. When the fork builds
   again, swap the abbreviation for `_root_.MemoryAccess` and the
   abstract predicates for OfflineMemory's actual ones — the shape and
   chip-side wiring don't change.
2. `lookup ProgramTable` row arguments couldn't pattern-match
   `Expression.eval env input_var_pc[0]` against `cols.pc[0]` directly
   in `FormalSpec` (Lean's elaborator doesn't push `Vector.map eval`
   through `Vector.getElem` automatically). Resolution: wrap the
   lookup in a small `ProgramTable.assertion` FormalAssertion whose
   `Inputs` struct mirrors `AddCols`'s `pc : Vector T 3` shape. The
   `circuit_proof_start`'s `subst` chain on `h_input`'s vector-equality
   conjuncts then makes the LHS and goal forms identical.
3. `Spec` form mismatch between `Vector.map eval` and pushed-through
   `eval [i]`. Resolved with `simp only [Spec, Vector.getElem_map]` at
   both the goal and hypothesis sites — `Vector.getElem_map` is not in
   `circuit_norm` and has to be invoked explicitly.

**Out of scope for this iteration**

- `state`-bus dedicated table. `CPUState` stays with its propositional
  `cpuStateSpec` clauses (just clock-decomposition bounds). PC
  permutation follows from OfflineMemory once register reads model it;
  a dedicated state-bus table is a follow-up.
- Full FormalAssertion promotion of `AddiChip`/`SubChip`/`SubwChip`/
  `BitwiseChip`. They emit `ProgramTable.assertion` in `main` but stay
  iff-only at the chip level. Tier 2 friction (`circuit_norm` +
  field-injectivity) still gates promotion.
- `StoreByte` (natural sibling of `LoadByte`). The read side is now
  fully modeled via `loadMemoryAccess`; Store adds the write side and
  is a one-of follow-up.
- Multiplicity tracking. Per the established stateless-table
  convention, SP1's `mult` is dropped — `is_real = 1` /
  `is_trusted = 1` discharge the per-row `mult ≠ 0` guards.

**End state**: `lake build SP1Clean` is green (0 errors / 0 warnings).
`SP1Clean.Add.assertion` carries program-bus + byte-lookup consequences
in its `FormalSpec`. `SP1Clean.LoadByte.Spec` captures three memory
accesses (two register reads + one RAM read) explicitly as
`memoryAccessSpec` records. `SP1Clean.Soundness.MemoryConsistency`
states the trace-level OfflineMemory bridge, parameterized to compile
around the upstream `OfflineMemory.lean` build failures.
