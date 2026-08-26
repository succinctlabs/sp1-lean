# Contributor and agent techniques

These files contain maintained proof, build, provenance, and upstream-integration procedures. For
the current theorem boundary, start with [`../architecture.md`](../architecture.md) and
[`../release-audit.md`](../release-audit.md).

Read Clean's pinned upstream documentation first:
`.lake/packages/Clean/doc/performance-problems.md`, `doc/proving-guide.md`, `AGENTS.md`, and
`Clean/Air/README.md`. The files here specialize those rules to SP1.

- [proof-patterns.md](proof-patterns.md) — circuit proof recipes, performance landmines, and the
  repository's cleanup discipline. Its source-stability and folded-term rules override generic
  `mathlib-quality` transformations when they conflict.
- [porting-recipe.md](porting-recipe.md) — step-by-step chip-porting checklist.
- [lean-sail-notes.md](lean-sail-notes.md) — Lean/Sail environment, immutable pins, and update
  traps.
- [clean-upstream.md](clean-upstream.md) — Clean fork state, upstream queue, and exit condition.
- [sail-model-provenance.md](sail-model-provenance.md) — generated model provenance and
  regeneration.
- [extraction.md](extraction.md) — Rust constraint extraction and generated-artifact contract.
- [sp1-upstream-draft.md](sp1-upstream-draft.md) — prepared SP1-side draft; nothing pushed.
- [upstream-drafts.md](upstream-drafts.md) — prepared Clean issue/PR text; posting needs approval.

Generated axiom records live in [`../snapshots/`](../snapshots/). Compile profiles are generated on
demand with `scripts/profile_compile.sh` and kept with the review that motivated them, not as
evergreen documentation.
