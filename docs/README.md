# docs/ — index

Topical guides for `sp1-clean-native`. Skim the relevant one when you hit a matching surface.
The top-level `../README.md` is the public entry point; the always-loaded contributor brief is `../AGENTS.md`.

The docs split into two audiences:

- **Reader-facing** (understand what the project proves and how much it means) — the top-level files here:
  `architecture.md`, `release-audit.md`, `roadmap.md`, `bus-model.md`.
- **Contributor / agent-facing** (the fiddly proof/build techniques used while working on the proofs) — these
  live under [`agents/`](agents/README.md): `porting-recipe.md`, `proof-patterns.md`, `lean-sail-notes.md`,
  `extraction.md`, `mul-operation-learnings.md`. Point-in-time snapshots live under
  [`snapshots/`](snapshots/): `axiom-ledger.md`, `compile-profile.md`.

## What to read first

1. **`architecture.md`** — what this project is and the per-chip pattern. Read before adding a chip.
2. **`release-audit.md`** — the honest claim + pre-release audit: what is proven, the trust boundary, the
   axiom census, and the `sorry` inventory. Read before trusting or citing the result.
3. **`agents/porting-recipe.md`** — the step-by-step checklist to port a new instruction. Your working doc.
4. **`agents/proof-patterns.md`** — the witnessed-`FormalCircuit` proof recipe + the landmines.
5. **`agents/lean-sail-notes.md`** — the 4.28 environment: relevant when touching deps, imports, or the Sail side.

The single richest in-repo reference is `SP1Clean/Comparison.lean` — a no-new-proofs findings doc
recording the worked Add example's six steps end-to-end. The docs here distill it; read it for the full rationale.

## Index

**Reader-facing (top-level)**
- [overview.md](overview.md) — **SKELETON** of the north-star 5-page overview (the claim, the theorem, the buses, one chip end-to-end, the engine, faithfulness, tests, audit) — drafted against the *proposed* end-state with `[PENDING]` markers; becomes the public entry doc once the consolidation lands.
- [goal-overview.md](goal-overview.md) — the **TARGET-STATE** version of overview.md, written in the completed voice with no pending markers (empty gap ledger, 26 chips, engine as capstone); the diff against overview.md IS the remaining work. Do not cite as current status.
- [proposals/2026-07-architecture-consolidation.md](proposals/2026-07-architecture-consolidation.md) — **PROPOSAL**: the deep-audit findings + the one-engine/one-contract/one-theorem end-state, keep/retire/replace verdicts, migration plan, de-risk spikes.
- [architecture.md](architecture.md) — four-artifact chain (gadget → chip → Sail bridge → faithful anchor), mirror-rust layout, design verdict, design status.
- [release-audit.md](release-audit.md) — the honest claim, the five-kinds-of-faithfulness analysis, the machine-model divergence catalog, the axiom census, the `sorry` blocker inventory, and the modeling-fidelity / SP1-developer-reactions sections.
- [roadmap.md](roadmap.md) — open work along two axes: coverage breadth (Axis A) and sound-model depth (Axis B), with the five remaining `sorry`s up front.
- [bus-model.md](bus-model.md) — the cross-chip interaction-bus model (channels, the static byte table, Guarantees/Requirements duality).
- [chip-standardization.md](chip-standardization.md) — the uniform per-chip `ChipKind.advance` contract: motivation (spurred by the semantic channels), the two-axis effect model, the generic dispatcher, current progress (21/25 chips), and the decoder-seam deferral.

**Contributor / agent-facing** — see [`agents/README.md`](agents/README.md) for the full index.
- [agents/porting-recipe.md](agents/porting-recipe.md) — create the four artifacts, wire the root import, verify build + axioms; reuse Clean's native gadgets instead of an SP1 byte-bus.
- [agents/proof-patterns.md](agents/proof-patterns.md) — soundness/completeness skeleton for witnessed gadgets; `ZMod p` / `Word` / `circuit_proof_start` landmines; `maxHeartbeats` floors.
- [agents/lean-sail-notes.md](agents/lean-sail-notes.md) — Lean 4.28 + public Clean `main` + the GitHub-fetched Sail deps; the `lake update` toolchain-bump trap; the Clean-main ↔ Batteries `Fin.foldl` collision and the import-narrowing fix.
- [agents/extraction.md](agents/extraction.md) — the constraint-extraction pipeline (`sp1-constraint-compiler` → `update_extracted.py` → Lean) and the DSL contract.
- [snapshots/axiom-ledger.md](snapshots/axiom-ledger.md) — the machine-checked `#print axioms` inventory per theorem (re-generate from a green build before release).
- [snapshots/compile-profile.md](snapshots/compile-profile.md) — per-module elaboration profile + worst offenders (a point-in-time snapshot).
- [agents/mul-operation-learnings.md](agents/mul-operation-learnings.md) — Mul-specific soundness/completeness pitfalls (the 16-limb schoolbook multiply).
