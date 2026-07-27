# Release-readiness audit — findings log (2026-07)

Campaign log for the release-readiness pass: legacy-debt retirement (23-chip `ChipOracle` migration),
spec-level semantic audit, docs refresh, and the external verification report. Every finding cites
`file:line` at the time of discovery. Severities: **BLOCKER** (must fix before release), **WEAK-SPEC**
(statement weaker/other than intended), **STALE-DOC** (prose contradicts the tree), **COSMETIC**,
**DISCLOSED-OK** (intentional, correctly disclosed limitation — no action).

Top-of-log standing item: the four **local path dependencies** (`../clean`, `../sail-riscv-lean`,
`../riscv-lean`, `../lean-sail`; see `lakefile.toml`) are 4.31-migration checkouts. Restoring
reproducible immutable git pins is a **release blocker** tracked outside this campaign
(`docs/release-audit.md` § dependency pins). Never run bare `lake update`.

## Phase 0 — baseline and extraction preconditions

- **F-0-01 (BLOCKER, fixed).** `update_extracted.py`'s `render_chip_oracle` was the only render path
  that never applied `_preserve_raw_byte_opcodes`, so regenerating any chip oracle at the pinned
  overlay emitted byte interactions as `(.byte (ByteOpcode.ofNat 6) …)` instead of the intended raw
  `(.byte 6 …)` — reproducibly diverging from the checked-in `ChipOracle/{Add,Sub}.lean` and breaking
  the documented byte-idempotence of full regeneration. The wrapper is semantically dangerous, not
  merely cosmetic: `ByteOpcode.ofNat` maps every out-of-range value to `.Range`, so it is not an
  injective representation of the upstream AIR tuple (the reason the strip exists — see the function's
  docstring). Had the 23-chip migration proceeded on the broken renderer, every new oracle would have
  carried the non-injective encoding. Fix: one-line call added in `render_chip_oracle`
  (`update_extracted.py`), after which the complete `EXTRACT_AIR_ONLY=1` regeneration at the pinned
  overlay (`69a8377c`, patch set `a2c43cfa…`) reproduces all 62 generated modules byte-identically.
- **F-0-02 (COSMETIC, documented).** Each extractor run's `cargo` invocation rewrites the overlay's
  `Cargo.lock` (newer-cargo re-normalization of one `slop-algebra` entry), which the strict
  audited-worktree check then rejects on the next run. Operational note added to
  `docs/agents/extraction.md` (stash/restore `Cargo.lock` before each run; `--locked` cannot work).
- **F-0-03 (STALE-DOC, fixed).** `SP1Clean/Soundness/ChipRegistry.lean:32-34` still disclosed a
  4.31-migration `sorryAx` deferral (DivRem `evidenceSoundness` + Branch/ShiftLeft/DivRem
  completeness) that no longer exists — contradicted by the 2026-07-27 audit run (`run_audit.sh`
  `== AUDIT PASS ==`, zero `sorryAx`, empty allowlist) re-confirmed at this campaign's Phase-0
  baseline. Comment replaced with the accurate axiom-clean statement.
- Phase-0 baseline: G1 `lake build SP1Clean` (3626 jobs, 0 error/0 warning/0 info), G2 `lake test`,
  G3 `lake lint`, G4 `scripts/run_audit.sh` — all green before any change.

## Phase 1 — quick cleanup + docs pruning

- Deleted (only the root index imported them): `Faithful/{AddrAddOperation, AddressOperation,
  LtOperationSigned, U16toU8OperationUnsafe, ITypeReader, JTypeReader}.lean` (14 probe entries
  auto-dropped on `gen_axiom_probe.py` regeneration: 513 → 499), plus the doc-only
  `SP1Clean/Comparison.lean` (4.28-era worked-example memo; rationale lives in
  `docs/architecture.md` and the forthcoming verification report), plus the empty untracked
  `SP1Clean/Extracted/Circuit/` directory.
- Docs pruned (retrievable from git history): `docs/audits/2026-07-full-project/`, `docs/archive/`,
  `docs/snapshots/profile-baseline-2026-06-10/`, `docs/talks/`, `docs/spikes/`, `docs/upstream/`,
  `docs/agents/{capstone-seam-plan,bytechip-provider-design}.md`,
  `docs/proposals/2026-07-architecture-consolidation.md`. `docs/bus-model.md` was **kept** (with a
  strengthened HISTORICAL banner) because eight load-bearing source doc-comments cite its section
  numbers. Index files (`docs/README.md`, `docs/agents/README.md`, `AGENTS.md` docs section) updated;
  `sail-fork-delta.md` newly indexed; dangling references in `TouchChains.lean`,
  `ByteChip/Ensemble.lean`, `compile-profile.md`, `bus-model.md` repointed.

## Phase 2 — ChipOracle migration

(recorded as batches land)

## Phase 3 — audit findings

(recorded as batches land)
