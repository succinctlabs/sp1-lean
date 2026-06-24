# Cleanup / refactor backlog

Prioritized follow-up cleanup and refactor work, plus the golfing/cleanup skills available. Distilled from the
2026-06-22/23 proof-cleanup campaign (109 hand-written files golfed, −591 lines, axiom-cleanliness preserved).
For *how* to golf safely, see `proof-patterns.md` § "Golf & cleanup discipline".

## Already landed (for reference)

- The per-file golf sweep (109 files) + substrate hoists: `Word.isU64_four` (6 inline sites), Faithful
  `val_16`/`bool_iff` dedup → `ChipTactics` (24 files), the `ShiftLeftChip/Core` loose-variable helper dedup.
- The Soundness Memory-layer helper consolidation (`two_lt_p_aux` / `valCast_pos_aux` /
  `mem_memEventsFiltered_of_mem_eventsAt`).
- Linters: `style.lambdaSyntax` / `style.dollarSyntax` enabled on the `SP1Proofs` lake library (zero fallout).
- `lake lint` (environment linters) stood up — the `sp1Lint` lintDriver (`scripts/sp1Lint.lean`) runs 11 curated
  Batteries `#lint` linters over the hand-written `SP1Clean.*` decls (auto-gen excluded by module-path filter),
  with a 21-entry `scripts/nolints.json` baseline; CI runs it in the build job.
- The `val_N` private-lemma sweep — the scattered `(N : ZMod p).val = N` copies (`val_13`×3, `val_14`×3,
  `val_16'`/`val_16''`×4, Shift-core `val_4/8/16/32/64`, Native `c65535_ne_zero`×2) consolidated onto the
  `Math/Word.lean` family (now `val_2/4/8/13/14/16/32/64/256/32768/65535/65536`); plus a new `Math/Gate.lean`
  binary-field/BitVec-compare API (`bool_val_le`, `val_ne`, `eq_one_iff_of_ite` + siblings,
  `slt/ult_{true,false}_iff` over `BitVec w`) absorbing the Branch/Lt decision-proof private helpers. Also
  fixed the 2 `ShiftRightMath.val_4/64` `simpNF` nolints.

## Cross-file refactors — deferred with caveats

### R1 — NeZero / Fact boilerplate  (BLOCKED by design)

`haveI : NeZero p := …` appears ~185× (Fact-derived) + ~14× (Prime-derived). A **global** `NeZero p` instance
derived from `Fact (2^17 < p)` is *deliberately avoided* — it would make the pervasive `omit [Fact (2^17 < p)]
in` clauses illegal (`Model/ByteTable.lean:84`). A `Fact p.Prime`-derived global instance *might* survive the
`omit` pattern (it depends on primality, not the magnitude), eliminating most of the boilerplate — but it goes
against the documented local-instance discipline and risks instance-resolution surprises. **Needs an owner
decision**, not a drive-by change.

### R2 — eval-map global lemma  (MARGINAL)

A global `eval (map) v[i] = w[i]` lemma could replace the per-file quantified `ea`/`epc` helpers across ~36
`Formal.lean` files. But the per-file helpers already capture the dedup *within* each file; a global lemma saves
only ~1 line/helper while re-churning 36 already-clean files + a foundational rebuild + form-variation risk.
Low ROI — skip unless a foundational pass is happening anyway.

## `/decompose-proof` candidates (long proof bodies, >50 lines)

- `ShiftLeftChip/Formal.lean` + `ShiftRightChip/Formal.lean` — `completeness` (~130–180 lines).
- `LoadHalfChip/Formal.lean` — the 4-way `h_sel_lt` offset-selection case-bash (near-verbatim across soundness
  + completeness).
- `BranchChip/Formal.lean` — `soundness` / `completeness` (per-column `env.get` plumbing).

Caveat: several are perf-tuned heavy files — decompose with care and watch elaboration time.

## `/split-file` candidates

None currently exceed 1500 lines after cleanup. `Proofs/Chips/ShiftRightChip/Core.lean` (2177) is the largest
single file but is kept whole on purpose (the dispatch proof is one entangled unit). Note only.

## Heavy cores — deferred (poor risk/reward)

Left untouched in the campaign; revisit only with a specific goal:
- `ShiftRight/Core` (2177), `ShiftRight/Dispatch` (1591), the rest of `ShiftLeft/Core` — bv_decide/kernel-fragile.
- `Model/SailMemory` (1270) — foundational, full-rebuild cost.
- **All DivRem files** — fresh perf work landed via the `div-rem-perf` merge; leave alone.

## Cross-file dedup candidates (re-examine before acting)

- **SailState-staging bridge preamble** (`hpc_get` / `key` / `hsp_config`) recurs across ~10 store/jal/load
  `Bridge.lean` files → a shared lemma. **Re-examine first** — upstream #101/#102 rewrote several bridges in the
  2026-06-23 merge, so the pre-merge shape may have changed.
- Mul `soundness` 5-branch tail — byte-identical block ×5, but a clean factor needs an intractable ~40-line
  `resultWord` struct type; **skip** (the duplication is cheaper than the abstraction).
- **`vec4_eval`** — the `#v[eval e v[0],…,v[3]] = Vector.map (eval e) v` lemma recurs ×6 across chip
  `Formal.lean` (Mul/Lt/ShiftRight/ShiftLeft/Bitwise + DivRem `Completeness/Driver`). Clean Math candidate
  (Clean-DSL-generic), but **2 of the 6 are perf-sensitive** (DivRem Driver, Shift Formals) — fold into a
  Shift/DivRem pass rather than a standalone touch. Not done in the val_N sweep.

## Performance — what's actually actionable (investigated 2026-06-24)

The "safe mechanical" perf levers were swept over the touched + fair-game heavy files and found **nothing
actionable**:
- **`maxHeartbeats` tightening is the wrong lever.** The heavy Shift/DivRem proofs are **kernel /
  type-checking-bound, not heartbeat-bound** — measured `ShiftLeftChip/Soundness/Sll.soundness` at **72**
  elaboration heartbeats against its 4M ceiling. The ceilings are non-binding safety margins; lowering them has
  no wall-clock effect and only risks a future spike. Leave them.
- No `simp_all` / heavy `simp [circuit_norm]` in the touched files (already targeted), and none carry
  `unusedSimpArgs` suppressions, so the simp-tightening / redundant-arg levers are empty there too.
- The **only** real prize is the **Shift tail-dedup** (extract the byte-identical `cpuA/msb*/aluA` tail shared
  across the 6 Shift conjuncts, mirroring `DivRemChip/Soundness/Tail.lean`) — a structural change, deferred:
  it overlaps the recently-golfed Shift soundness files and is a multi-hour effort. That, plus the term-intrinsic
  DivRem cost (off-limits), is where the build time genuinely lives.

## Linters — next candidates (deferred; real fallout)

### Syntactic (build-time, lib `moreLeanArgs`)

After `style.lambdaSyntax` / `style.dollarSyntax` (zero-fallout, enabled): `linter.oldObtain`,
`linter.style.longLine` (Model/Sail* already suppress it), `linter.style.cdot`. Each has real hits to triage
(fix or per-file suppress) across the heavy cores — enable one at a time, return to 0-warning, then the next.
Do **not** enable `linter.unusedSectionVars` / `linter.unusedSimpArgs` (structurally necessary in circuit
proofs — ~275 deliberate suppressions). Leave the auto-gen `linter.all false` (`Extracted/`, `TraceGenTests/`).
The scoping unit is the `SP1Proofs` lake library's `moreLeanArgs` (see `lakefile.toml` + the AGENTS.md "Linters"
note for the registration caveat).

### Environment (`lake lint` / `sp1Lint`)

The curated set runs 11 of the Batteries `#lint` linters. Deferred / dropped, with rationale:

- **`docBlame` / `docBlameThm` / `tacticDocs` / `deprecatedNoSince`** — doc-coverage linters; thousands of hits
  on undocumented private proof lemmas. Enable only after a deliberate documentation pass (not planned).
- **`unusedArguments`** — *dropped, not deferred.* It flags **only** the project's uniform signature args
  (`{p} [Fact p.Prime] [Fact (2^17<p)]` / `NeZero p`, and the `ProverData`/`ProverHint` args every chip
  `Spec`/`Assumptions` carries) — all structurally required, none a defect — and it grows a fresh false-positive
  per new chip, so even nolinting it is a permanent tax. Re-run ad hoc if hunting genuinely-dead args.
- **`structureInType`** — not in the curated set; revisit if structure-universe hygiene becomes a concern.
- **Fixable `simpNF` residue (2 entries):** `ShiftRightMath.val_4_zmod_p` / `val_64_zmod_p` are "simp can prove
  this" *duplicate* `@[simp]` re-declarations (provable by the canonical `val_4_zmod_p` / `ShiftLeftCore.
  val_64_zmod_p`). Droppable, but in a heavy `ShiftRightChip/Core` file — fold into a future Shift-core pass and
  re-`--update` the nolints. The other 19 `nolints.json` entries are stable Math/Model/Sail simp infra (leave).

**Hardening option — namespace-isolate the auto-gen (Option B, deferred).** The `sp1Lint` exclusion is a *soft*
module-path filter (`getHandwrittenDecls` drops `SP1Clean.Extracted.*` + `*Vectors`). A *hard* boundary would
relocate all auto-gen to a separate root namespace `SP1Extracted.*`, so the stock `runLinter SP1Clean` excludes
it by construction (no custom filter). Cost: ~87 module renames + hundreds of import-line edits + `update_
extracted.py` writer paths + the root aggregator + lakefile globs, and it touches the deliberate "vectors live
in `Proofs/TraceGenTests/`" layering. Not worth it for linting alone; reconsider if a hard auto-gen/hand-written
namespace split is wanted for other reasons.

## Golfing / cleanup skills available

- **`/cleanup`** — the per-file 7-phase workflow (style audit → per-decl golf → simplify → verify). Best for a
  handful of named files.
- **`/cleanup-all`** — the orchestrator marathon (dispatches per-batch workers across the whole tree). Best for a
  project-wide sweep; honor the repo guardrails (auto-gen exclusion, axiom-clean, heavy-core caution).
- **`/decompose-proof`** — break one long proof into named sub-lemmas.
- **`/split-file`** — split an over-long file along namespace/section seams.
- **`Skill(simplify)`** — a holistic reuse/altitude review pass on a file (invoked inside `/cleanup` Phase 6.5).
