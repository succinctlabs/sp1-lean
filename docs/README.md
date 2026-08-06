# Documentation index

The top-level [`README.md`](../README.md) is the public entry point and [`AGENTS.md`](../AGENTS.md) is the
contributor brief loaded by coding agents. This directory separates current claims from historical design
records so that an old audit packet is never mistaken for the present theorem boundary.

> **Upstream authority: read Clean's own docs.** This project is built on the Clean DSL (upstream
> <https://github.com/Verified-zkEVM/clean>; its docs are in the `doc/` folder, singular). Read them either
> on GitHub or from the in-tree copy Lake installs under `.lake/packages/Clean/`, which is exactly the
> pinned revision (every dependency is an immutable git pin). For *how to write proofs and tame
> elaboration*, Clean's docs are the authority — `doc/performance-problems.md`, `doc/proving-guide.md`,
> `AGENTS.md`, and `Clean/Air/README.md` (the channel/ensemble/balance model our grounding engine builds
> on). Our [`agents/proof-patterns.md`](agents/proof-patterns.md) records the SP1-specific instances.

## Read these first

1. [`verification-report.md`](verification-report.md) — the self-contained technical report: what
   is proved, on what foundations, with what trust base — written for readers who know SP1 and
   Clean but not this repository.
2. [`overview.md`](overview.md) — concise, current statement of what is implemented, what is reserved, and
   where the proof stops.
3. [`architecture.md`](architecture.md) — the whole-chip verification chain, structural buses, typed witness
   decode, ranked/timed grounding, and theorem layering.
4. [`release-audit.md`](release-audit.md) — machine-derived pins, trust boundary, direct-deferral inventory,
   and `#print axioms` census.
5. [`roadmap.md`](roadmap.md) — dependency-ordered work toward native AIR, full upstream AIR, execution, and
   verifier soundness.
6. [`proposals/consolidation-progress.md`](proposals/consolidation-progress.md) — compact current checkpoint
   board for the architecture-consolidation work.

## Current reader-facing docs

- [`overview.md`](overview.md) — honest current overview; it distinguishes the supported-native theorem,
  the conditional exact-upstream `_of_obligations` composition boundary, and the still-open
  execution/ArkLib layers. Its §4 is the current statement of the channel/bus model.
- [`architecture.md`](architecture.md) — detailed architecture and migration status.
- [`release-audit.md`](release-audit.md) — authoritative current proof and trust audit. Regenerate its raw
  census with `scripts/run_audit.sh` before citing numbers.
- [`roadmap.md`](roadmap.md) — live dependency graph from exact system-table grounding through ArkLib
  integration and witness-generation completeness.
- [`chip-standardization.md`](chip-standardization.md) — the completed 25/25 `ChipKind.advance` interface
  and how the machine layer consumes it.
- [`goal-overview.md`](goal-overview.md) — completion contract for the full AIR, boot-to-halt, ArkLib
  verifier, and witness-generation layers. Do not cite it as current status.

One historical design record stays in the tree: [`bus-model.md`](bus-model.md) (the pre-consolidation
bus model) — source doc-comments cite its section numbers; read its banner before citing it. The other
historical records (the pre-remediation audit packet, retired migration handoffs, the 2026-07
consolidation proposal, one-off talks/spikes/profiling baselines) were removed from the working tree
once superseded; retrieve them from git history if needed.

## Contributor and agent docs

See [`agents/README.md`](agents/README.md) for the full index:

- [`agents/porting-recipe.md`](agents/porting-recipe.md) — chip-porting checklist.
- [`agents/proof-patterns.md`](agents/proof-patterns.md) — circuit proof recipes and Lean/Clean landmines.
- [`agents/lean-sail-notes.md`](agents/lean-sail-notes.md) — Lean 4.32.2 dependency pins and Sail
  environment, including the model/runtime pairing rule.
- [`agents/sail-fork-delta.md`](agents/sail-fork-delta.md) — the exact six-value `sail-riscv-lean`
  platform-configuration delta, why it is required for the memory-bridge lemmas to be true, and how to
  retire it.
- [`agents/extraction.md`](agents/extraction.md) — Rust extraction and generated-artifact contract.
- [`agents/mul-operation-learnings.md`](agents/mul-operation-learnings.md) — multiplication-specific proofs.
- [`agents/cleanup-profile.md`](agents/cleanup-profile.md) — binding house rules for `/cleanup` and `/cleanup-all`.
- [`agents/perf-findings.md`](agents/perf-findings.md) — how to avoid an elaboration budget: the rule
  (extract over opaque arguments), the predictor, the cause classes with their fixes, the diagnostic
  instrument, the measurement traps, and the bar a site must clear to be allowlisted at all.
- [`agents/cleanup-deferred.md`](agents/cleanup-deferred.md) — the owner-decision queue: duplication
  deliberately not fixed, grouped by blocker, plus the queued-never-applied renames.

Point-in-time generated records live in [`snapshots/`](snapshots/), notably the axiom census and compile
profile. They should be regenerated before a release rather than treated as evergreen prose.
