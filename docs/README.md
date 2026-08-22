# Documentation index

The top-level [`README.md`](../README.md) is the public entry point and [`AGENTS.md`](../AGENTS.md) is the
contributor brief loaded by coding agents. This directory separates current claims from historical design
records so that an old audit packet is never mistaken for the present theorem boundary.

Each document has **one role**, so none needs to repeat another:

| Document | Role |
|---|---|
| [`README.md`](../README.md) | GitHub front door: the claim, the build, the doc map, the license |
| [`overview.md`](overview.md) | ten-minute technical orientation — states, never argues |
| [`verification-report.md`](verification-report.md) | the long-form external report — argues and evidences each claim |
| [`release-audit.md`](release-audit.md) | machine-adjacent audit record: pins, gates, census |
| [`audits/2026-08-independent-semantic-audit.md`](audits/2026-08-independent-semantic-audit.md) | point-in-time independent second opinion on semantic foundations and ArkLib/VCVio readiness |
| [`audits/2026-08-pr110-external-report-disposition.md`](audits/2026-08-pr110-external-report-disposition.md) | finding-by-finding disposition of Alex Hicks's focused PR #110 review; the private PDF is identified there by hash |
| [`architecture.md`](architecture.md) | module/pillar ownership, design rules, deliberate exceptions |
| [`roadmap.md`](roadmap.md) | dependency-ordered future work + non-blocking backlog |
| [`goal-overview.md`](goal-overview.md) | the completed-state contract (never current status) |
| [`witgen-wire-format.md`](witgen-wire-format.md) | the `version: 1` witness-export wire format the `export/witgen/` artifacts and the Rust interpreter share |
| [`rust-integration-memo.md`](rust-integration-memo.md) | reader-facing memo for the SP1 team: what the witness-generation export is, how it is checked against the real prover, and the proposed in-SP1 conformance test |
| [`chip-standardization.md`](chip-standardization.md) | the completed 25/25 `ChipKind.advance` interface record |
| [`bus-model.md`](bus-model.md) | **HISTORICAL** pre-consolidation bus model, kept only for the section numbers source doc-comments cite |
| [`proposals/consolidation-progress.md`](proposals/consolidation-progress.md) | compact checkpoint board for the architecture-consolidation work |
| [`snapshots/`](snapshots/) | point-in-time generated records: [`axiom-ledger.md`](snapshots/axiom-ledger.md) (per-theorem axiom inventory) and [`compile-profile.md`](snapshots/compile-profile.md) (**STALE** as stamped — pre-migration timings) |
| [`agents/`](agents/README.md) | contributor/agent how-to family — per-file index in [`agents/README.md`](agents/README.md) |
| [`AGENTS.md`](../AGENTS.md) | contributor/agent discipline: build, proof style, tooling gates |

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
5. [`audits/2026-08-independent-semantic-audit.md`](audits/2026-08-independent-semantic-audit.md) —
   independent review of semantic boundaries, joint non-vacuity, and verifier-integration readiness.
6. [`roadmap.md`](roadmap.md) — dependency-ordered work toward native AIR, full upstream AIR, execution, and
   verifier soundness.
7. [`proposals/consolidation-progress.md`](proposals/consolidation-progress.md) — compact current checkpoint
   board for the architecture-consolidation work.

## Current reader-facing docs

- [`overview.md`](overview.md) — honest current overview; it distinguishes the supported-native theorem,
  the conditional exact-upstream `_of_obligations` composition boundary, and the still-open
  execution/ArkLib layers. The current statement of the channel/bus model is
  [`architecture.md`](architecture.md) § "Structural buses and semantic grounding".
- [`architecture.md`](architecture.md) — detailed architecture and migration status.
- [`release-audit.md`](release-audit.md) — authoritative current proof and trust audit. Regenerate its raw
  census with `scripts/run_audit.sh` before citing numbers.
- [`audits/2026-08-independent-semantic-audit.md`](audits/2026-08-independent-semantic-audit.md) — a
  point-in-time second opinion; its findings refine the roadmap but do not override current theorem types.
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
- [`agents/clean-upstream.md`](agents/clean-upstream.md) — the Clean pin is currently a **fork**: its
  state and exit condition, the modification-vs-addition split rule, and the upstream PR queue.
- [`agents/sail-model-provenance.md`](agents/sail-model-provenance.md) — the generated
  `Lean_RV64D` snapshot's provenance: the SP1 platform config, why it is required for the
  memory-bridge lemmas to be true, and the regeneration pipeline.
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
