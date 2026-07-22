# docs/archive/ — retired handoff records

Fully-historical documents kept for provenance, **not** for current guidance. These were live handoff
notes during earlier migrations; their durable conclusions have been folded into the live surface
(`docs/roadmap.md`, `docs/architecture.md`, `docs/README.md`) and Clean's own docs (upstream
<https://github.com/Verified-zkEVM/clean>, or in-tree `.lake/packages/Clean/`) are now the authority for the
Clean-API and channel/ensemble material they describe. Read them only for the "how did we get here" story.

- `clean-main-migration.md` — the 2026-06 Clean re-pin (`2c20f7f0`) API deltas (off-gate `Requirements`,
  `pushIf`/`pullIf` → `pushedIf`/`pulledIf`, `channelsWithRequirements` relocation). Superseded by the 4.31
  migration (`docs/agents/lean-sail-notes.md`) and Clean's own docs.
- `430-migration-handoff.md` — the Lean 4.30 migration handoff.
- `w11-rebase-status.md` — the W11 ensemble/`VmTables` re-base status. Its live conclusion (stock `VmTables`
  deferred, reuse Clean's balance/channel primitives) now lives in `docs/roadmap.md` W11 and
  `docs/architecture.md` §"Relationship to Clean's `Air` layer".
