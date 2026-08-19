# docs/agents/ — contributor / agent techniques

The fiddly proof- and build-level techniques used while working on the proofs. These are the
*how-to-make-the-proofs-go* references; for *what the project proves and how much it means*, see the
reader-facing docs one level up (start with [`../architecture.md`](../architecture.md) and
[`../release-audit.md`](../release-audit.md)).

> **Read Clean's own docs first.** The Clean dependency (upstream <https://github.com/Verified-zkEVM/clean>,
> or in-tree under `.lake/packages/Clean/` — see [`../../AGENTS.md`](../../AGENTS.md) for the "where to find
> them" note) ships the upstream authority for proofs and performance: `doc/performance-problems.md` (the
> `whnf`/kernel-blowup doctrine — read before any nontrivial proof, and first on any heartbeat/`deep
> recursion` failure), `doc/proving-guide.md`, `AGENTS.md` (subcircuit/spec/`ElaboratedCircuit` discipline),
> and `Clean/Air/README.md` (channels/ensembles/balance). Most landmines in `proof-patterns.md` are
> SP1-specific instances of principles those docs state generally.

## Index

- [porting-recipe.md](porting-recipe.md) — step-by-step checklist to port a new chip from the Add/Bitwise template: create the four artifacts, wire the root import, verify build + axioms.
- [proof-patterns.md](proof-patterns.md) — the witnessed-`FormalCircuit` soundness/completeness skeleton; `ZMod p` / `Word` / `circuit_proof_start` landmines; the fold recipes that keep proofs inside the default elaboration budget; the `ElaboratedCircuit` field-obligation recipe; the **Golf & cleanup discipline** section (how to golf/clean proofs safely).
- [lean-sail-notes.md](lean-sail-notes.md) — the Lean 4.32.2 dependency environment: the immutable git
  pins, the generated-model/runtime pairing rule, and the `lake update` toolchain-bump trap.
- [clean-upstream.md](clean-upstream.md) — **the Clean pin is currently a fork.** Its state and exit
  condition, the rule for what may go in the fork versus `ToClean/` (modification vs addition), and the
  upstream PR queue with the measurement behind each entry.
- [sp1-upstream-draft.md](sp1-upstream-draft.md) — the prepared SP1-side draft PR: the 5-commit
  `v6.4.0`-based series, why it is not rebased onto `sp1-private/main`, and the PR body.
  **Prepared only — nothing pushed.**
- [upstream-drafts.md](upstream-drafts.md) — ready-to-file Clean issue/PR texts for the queue
  (U11 first). **Prepared only — posting requires the owner's explicit approval.**
- [sail-model-provenance.md](sail-model-provenance.md) — the generated `Lean_RV64D` snapshot's
  provenance: the four-key SP1 config and its six generated sites (CLINT/signature/PMP off), why it
  is load-bearing for the memory-bridge lemmas, its `rfl` disclosure lemmas, the generation
  pipeline, and the re-pinning procedure.
- [extraction.md](extraction.md) — the constraint-extraction pipeline (`sp1-constraint-compiler` → `update_extracted.py` → Lean) and the DSL contract.
- [cleanup-profile.md](cleanup-profile.md) — binding house rules for `/cleanup` and `/cleanup-all`; overrides the `mathlib-quality` plugin wherever they conflict.
- [perf-findings.md](perf-findings.md) — how to avoid an elaboration budget: **the rule** (extract over opaque arguments), the folded-vs-unfolded predictor, the cause classes with their fixes, the diagnostic instrument and measurement traps, and the bar a site must clear before it may be allowlisted.
- [cleanup-deferred.md](cleanup-deferred.md) — the owner-decision queue: duplication found and deliberately not fixed, grouped by blocker, with measured sizes; plus the 42-entry rename queue (never applied).
Point-in-time snapshots (regenerate before release) live under [`../snapshots/`](../snapshots/):
- [../snapshots/axiom-ledger.md](../snapshots/axiom-ledger.md) — the machine-checked `#print axioms` inventory per theorem.
- [../snapshots/compile-profile.md](../snapshots/compile-profile.md) — per-module elaboration profile + worst offenders + common threads.
- [mul-operation-learnings.md](mul-operation-learnings.md) — Mul-specific soundness/completeness pitfalls (the 16-limb schoolbook multiply).
