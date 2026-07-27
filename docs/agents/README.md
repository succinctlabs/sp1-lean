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
- [proof-patterns.md](proof-patterns.md) — the witnessed-`FormalCircuit` soundness/completeness skeleton; `ZMod p` / `Word` / `circuit_proof_start` landmines; `maxHeartbeats` floors; the `ElaboratedCircuit` field-obligation recipe; the **Golf & cleanup discipline** section (how to golf/clean proofs safely).
- [lean-sail-notes.md](lean-sail-notes.md) — the Lean 4.31 migration environment: local dependency pins,
  the Sail platform delta, and the `lake update` toolchain-bump trap.
- [sail-fork-delta.md](sail-fork-delta.md) — the exact three-line `sail-riscv-lean` platform-configuration
  delta (CLINT/signature/PMP off), its `rfl` disclosure lemmas, and the path to retiring the fork.
- [extraction.md](extraction.md) — the constraint-extraction pipeline (`sp1-constraint-compiler` → `update_extracted.py` → Lean) and the DSL contract.
Point-in-time snapshots (regenerate before release) live under [`../snapshots/`](../snapshots/):
- [../snapshots/axiom-ledger.md](../snapshots/axiom-ledger.md) — the machine-checked `#print axioms` inventory per theorem.
- [../snapshots/compile-profile.md](../snapshots/compile-profile.md) — per-module elaboration profile + worst offenders + common threads.
- [mul-operation-learnings.md](mul-operation-learnings.md) — Mul-specific soundness/completeness pitfalls (the 16-limb schoolbook multiply).
