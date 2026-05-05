# Memory mirror

This directory mirrors Claude Code's per-machine project memory at
`~/.claude/projects/-home-devontuma-Documents-sp1-lean/memory/` so the
context survives a machine switch (or a fresh checkout). It is
**not** the source of truth for the live agent — the live memory
is read from `~/.claude/...` — but copying the contents back into that
path on a new machine restores the agent's context.

## How to restore on a new machine

```sh
mkdir -p ~/.claude/projects/-home-devontuma-Documents-sp1-lean/memory
cp docs/memory/*.md ~/.claude/projects/-home-devontuma-Documents-sp1-lean/memory/
```

(The `PLAN_*.md` files are plan-file snapshots and should go in
`~/.claude/plans/` instead, with whatever name the current session is
using — the in-repo copy is purely for reference.)

## What lives here

- `MEMORY.md` — index loaded into every conversation; lists each
  memory entry with a one-line hook.
- `feedback_*.md` — guidance learned from past sessions ("don't do X",
  "the trick that closed Y"). Read-then-act.
- `project_*.md` — current state of ongoing initiatives (e.g.
  `project_field_generic_effort.md` — the field-genericization tracker).
- `reference_*.md` — pointers to commits / external resources.
- `PLAN_*.md` — plan-file snapshots from active multi-session work
  (e.g. `PLAN_divu_remu_poly.md` is the in-progress port plan as of
  the latest checkpoint).

## Sync convention

When a session lands material updates to memory, copy them back:

```sh
cp ~/.claude/projects/-home-devontuma-Documents-sp1-lean/memory/*.md docs/memory/
cp ~/.claude/plans/<active-plan>.md docs/memory/PLAN_<topic>.md
```

The mirror should be committed alongside whatever code change motivated
the memory update so the in-repo snapshot stays in sync with the
agent's view of the project.
