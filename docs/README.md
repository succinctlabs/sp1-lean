# Documentation index

The top-level [`README.md`](../README.md) is the public entry point and [`AGENTS.md`](../AGENTS.md) is the
contributor brief loaded by coding agents. This directory separates current claims from historical design
records so that an old audit packet is never mistaken for the present theorem boundary.

> **Upstream authority: read Clean's own docs.** This project is built on the Clean DSL (upstream
> <https://github.com/Verified-zkEVM/clean>; its docs are in the `doc/` folder, singular). Read them either
> on GitHub or from the in-tree copy Lake installs under `.lake/packages/Clean/` (see
> [`../AGENTS.md`](../AGENTS.md) for the "where to find them" note — including that the dependency is
> temporarily a local path checkout during the 4.31 migration). For *how to write proofs and tame
> elaboration*, Clean's docs are the authority — `doc/performance-problems.md`, `doc/proving-guide.md`,
> `AGENTS.md`, and `Clean/Air/README.md` (the channel/ensemble/balance model our grounding engine builds
> on). Our [`agents/proof-patterns.md`](agents/proof-patterns.md) records the SP1-specific instances.

## Read these first

1. [`overview.md`](overview.md) — concise, current statement of what is implemented, what is reserved, and
   where the proof stops.
2. [`architecture.md`](architecture.md) — the whole-chip verification chain, structural buses, typed witness
   decode, ranked/timed grounding, and theorem layering.
3. [`release-audit.md`](release-audit.md) — machine-derived pins, trust boundary, direct-deferral inventory,
   and `#print axioms` census.
4. [`roadmap.md`](roadmap.md) — dependency-ordered work toward native AIR, full upstream AIR, execution, and
   verifier soundness.
5. [`proposals/consolidation-progress.md`](proposals/consolidation-progress.md) — compact current checkpoint
   board for the architecture-consolidation work.

The most useful worked example in the source is `SP1Clean/Comparison.lean`; it explains the original Add
chain and the design choices that led to the current whole-chip boundary.

## Current reader-facing docs

- [`overview.md`](overview.md) — honest current overview; it distinguishes the proved supported-native
  theorem from the reserved `supported_core_air_sound`, `sp1_air_sound`, `sp1_execution_sound`, and
  `sp1_verifier_sound` layers.
- [`architecture.md`](architecture.md) — detailed architecture and migration status.
- [`release-audit.md`](release-audit.md) — authoritative current proof and trust audit. Regenerate its raw
  census with `scripts/run_audit.sh` before citing numbers.
- [`roadmap.md`](roadmap.md) — live debt and dependency graph. Its older W-item narrative is retained as
  implementation history and explicitly marked as such.
- [`bus-model.md`](bus-model.md) — the four plain Clean channels and their row-local guarantees.
- [`chip-standardization.md`](chip-standardization.md) — the completed 25/25 `ChipKind.advance` interface
  and how the machine layer consumes it.

## Design records and audit history

- [`proposals/2026-07-architecture-consolidation.md`](proposals/2026-07-architecture-consolidation.md) — the
  proposal that motivated the one-engine/one-contract split. It is a historical design record; use the
  progress board and architecture doc for implemented state.
- [`audits/2026-07-full-project/`](audits/2026-07-full-project/) — frozen repository-wide audit at
  `6c399dbd` before the remediation work. Its findings are preserved as evidence, with a post-audit note
  pointing to the current status; it is not a description of today's worktree.
- [`goal-overview.md`](goal-overview.md) — aspirational completed-state document for the full AIR,
  boot-to-halt, and ArkLib verifier layers. Do not cite it as current status.
- [`archive/`](archive/) — retired handoff records (the pre-4.31 `clean-main-migration.md` /
  `430-migration-handoff.md` and the `w11-rebase-status.md` ensemble re-base). Provenance only; their
  durable conclusions are in `roadmap.md`, `architecture.md`, and Clean's own docs
  (<https://github.com/Verified-zkEVM/clean> or in-tree `.lake/packages/Clean/`).

## Contributor and agent docs

See [`agents/README.md`](agents/README.md) for the full index:

- [`agents/porting-recipe.md`](agents/porting-recipe.md) — chip-porting checklist.
- [`agents/proof-patterns.md`](agents/proof-patterns.md) — circuit proof recipes and Lean/Clean landmines.
- [`agents/lean-sail-notes.md`](agents/lean-sail-notes.md) — Lean 4.31 dependency and Sail environment.
- [`agents/extraction.md`](agents/extraction.md) — Rust extraction and generated-artifact contract.
- [`agents/mul-operation-learnings.md`](agents/mul-operation-learnings.md) — multiplication-specific proofs.

Point-in-time generated records live in [`snapshots/`](snapshots/), notably the axiom census and compile
profile. They should be regenerated before a release rather than treated as evergreen prose.
