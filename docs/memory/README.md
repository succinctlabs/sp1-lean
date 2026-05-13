# Memory mirror

This directory mirrors Claude Code's per-machine project memory so the
context survives a machine switch (or a fresh checkout). The live
memory lives under
`~/.claude/projects/<slug>/memory/`, where `<slug>` is derived from the
absolute path of this checkout — e.g. on the `dtumad` workstation it
resolves to `~/.claude/projects/-home-dtumad-Documents-sp1-lean/memory/`,
on the `devontuma` workstation to
`~/.claude/projects/-home-devontuma-Documents-sp1-lean/memory/`. The
in-repo mirror is **not** the source of truth for the live agent — the
live memory is read from `~/.claude/...` — but copying the contents back
into that path on a new machine restores the agent's context.

## How to restore on a new machine

```sh
# resolve the slug for this checkout
SLUG="$(pwd | tr / - )"   # e.g. -home-dtumad-Documents-sp1-lean
DEST="$HOME/.claude/projects/$SLUG/memory"
mkdir -p "$DEST"
cp docs/memory/*.md "$DEST/"
```

(The Claude Code project slug is just the absolute path with `/`
replaced by `-`. If you customize the project root, derive the slug
accordingly.)

## Sync convention

When a session lands material updates to live memory, copy them back
into the mirror and commit alongside whatever code change motivated the
update:

```sh
SLUG="$(pwd | tr / - )"
SRC="$HOME/.claude/projects/$SLUG/memory"
cp "$SRC"/*.md docs/memory/
```

If your active session also drove plan-file changes (rare; usually
plans are ephemeral), copy them too:

```sh
cp ~/.claude/plans/<active-plan>.md docs/memory/PLAN_<topic>.md
```

After copying, also **delete** in-repo mirror entries that have been
pruned from live memory and have no external references (CLAUDE.md /
`docs/*.md` / other surviving memory files). The mirror should stay
close to a strict copy of live memory; orphaned archives only earn
their place when CLAUDE.md or another doc still points at them.

## What lives here

- `MEMORY.md` — index loaded into every conversation; lists each
  active memory entry with a one-line hook. **Mirrors live exactly.**
- `feedback_*.md` — guidance learned from past sessions ("don't do X",
  "the trick that closed Y"). Read-then-act.
- `project_*.md` — current state of ongoing initiatives (e.g.
  `project_divrem_poly.md`, `project_sll_poly_status.md`).
- `reference_*.md` — pointers to commits / external resources.

## Archive divergence

A small set of `feedback_*.md` files in this directory are NOT listed
in `MEMORY.md` because they've been pruned from live memory, but they
remain in the repo because external docs still reference them:

- `feedback_extra_shells_slow_compile.md` — referenced from `CLAUDE.md`
  (build-concurrency section)
- `feedback_grind_ring_finkb.md` — referenced from `docs/PERF_PATTERNS.md`
- `feedback_poly_proof_patterns.md` — referenced from `docs/FIELD_GENERIC.md`
- `feedback_divrem_core_port_blockers.md` — referenced from
  `feedback_extra_shells_slow_compile.md`

When updating those external docs, either keep these archive files in
sync or inline the relevant content into the doc and delete the archive
entry.
