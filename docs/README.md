# Documentation index

The top-level [`README.md`](../README.md) is the public entry point and [`AGENTS.md`](../AGENTS.md)
is the contributor brief loaded by coding agents. Documents in this tree describe the current
theorem boundary or provide an explicitly retained external audit record. Superseded proposals,
handoffs, campaign queues, and timing snapshots are available from git history instead of living
beside current claims.

Each document has one role:

| Document | Role |
|---|---|
| [`overview.md`](overview.md) | ten-minute technical orientation |
| [`verification-report.md`](verification-report.md) | self-contained external technical report |
| [`release-audit.md`](release-audit.md) | machine-adjacent pin, gate, trust, and census record |
| [`audit-surface.md`](audit-surface.md) | short semantic definition inventory, mechanically gated |
| [`layering.md`](layering.md) | structural layering and namespace contract |
| [`architecture.md`](architecture.md) | module ownership, proof chain, and deliberate exceptions |
| [`roadmap.md`](roadmap.md) | dependency-ordered future work and non-blocking backlog |
| [`goal-overview.md`](goal-overview.md) | completed-state contract; never current status |
| [`witgen-wire-format.md`](witgen-wire-format.md) | witness-export wire format |
| [`rust-integration-memo.md`](rust-integration-memo.md) | SP1-side witness-generation integration memo |
| [`audits/2026-08-independent-semantic-audit.md`](audits/2026-08-independent-semantic-audit.md) | retained independent semantic review |
| [`audits/2026-08-pr110-external-report-disposition.md`](audits/2026-08-pr110-external-report-disposition.md) | retained finding-by-finding external-review disposition |
| [`audits/2026-08-unification-target-architecture.md`](audits/2026-08-unification-target-architecture.md) | unification campaign's measured architecture baseline and pin decision |
| [`agents/`](agents/README.md) | maintained contributor techniques and provenance procedures |
| [`snapshots/axiom-ledger.md`](snapshots/axiom-ledger.md) | generated per-theorem axiom inventory |

> **Upstream authority: read Clean's own docs.** Read the pinned copy under
> `.lake/packages/Clean/` or upstream at <https://github.com/Verified-zkEVM/clean>:
> `doc/performance-problems.md`, `doc/proving-guide.md`, `AGENTS.md`, and
> `Clean/Air/README.md`. [`agents/proof-patterns.md`](agents/proof-patterns.md) records only the
> SP1-specific applications and cleanup constraints.

## Read these first

1. [`verification-report.md`](verification-report.md) — claim, evidence, limitations, and trust base.
2. [`overview.md`](overview.md) — concise current implementation status.
3. [`architecture.md`](architecture.md) — the whole-chip and whole-shard proof chain.
4. [`release-audit.md`](release-audit.md) — machine-derived pins, gates, and axiom disclosures.
5. [`audit-surface.md`](audit-surface.md) — the definitions requiring human semantic review.
6. [`roadmap.md`](roadmap.md) — remaining exact-AIR and verifier work.

The release audit runs `scripts/check_release_surface.py`, which independently checks that all 25
instruction identities retain a native definition, Formal/Bridge/Complete proof surface,
whole-chip Rust oracle and faithfulness anchor, real-row satisfiability theorem, SP1 dump, and all
three witgen artifacts. `scripts/check_current_docs.py` checks local Markdown links, rejects retired
paths, and requires module documentation on hand-written Lean modules.

## Historical records

Superseded internal design proposals and campaign handoffs are deliberately not kept in the working
tree. Durable conclusions were moved into `architecture.md`, `roadmap.md`, `AGENTS.md`, source
docstrings, and `agents/proof-patterns.md`. Use git history when reconstructing an old decision.
The documents under `audits/` remain because they are review/measurement records rather than live
design instructions.
