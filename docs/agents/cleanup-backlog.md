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

## Linters — next candidates (deferred; real fallout)

After `style.lambdaSyntax` / `style.dollarSyntax` (zero-fallout, enabled): `linter.oldObtain`,
`linter.style.longLine` (Model/Sail* already suppress it), `linter.style.cdot`. Each has real hits to triage
(fix or per-file suppress) across the heavy cores — enable one at a time, return to 0-warning, then the next.
Do **not** enable `linter.unusedSectionVars` / `linter.unusedSimpArgs` (structurally necessary in circuit
proofs — ~275 deliberate suppressions). Leave the auto-gen `linter.all false` (`Extracted/`, `TraceGenTests/`).
The scoping unit is the `SP1Proofs` lake library's `moreLeanArgs` (see `lakefile.toml` + the AGENTS.md "Linters"
note for the registration caveat).

## Golfing / cleanup skills available

- **`/cleanup`** — the per-file 7-phase workflow (style audit → per-decl golf → simplify → verify). Best for a
  handful of named files.
- **`/cleanup-all`** — the orchestrator marathon (dispatches per-batch workers across the whole tree). Best for a
  project-wide sweep; honor the repo guardrails (auto-gen exclusion, axiom-clean, heavy-core caution).
- **`/decompose-proof`** — break one long proof into named sub-lemmas.
- **`/split-file`** — split an over-long file along namespace/section seams.
- **`Skill(simplify)`** — a holistic reuse/altitude review pass on a file (invoked inside `/cleanup` Phase 6.5).
