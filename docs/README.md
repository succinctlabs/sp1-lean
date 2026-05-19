# docs/ — canonical references

Topical guides for working in this repo. `CLAUDE.md` (at the repo root)
is the architectural entry point — *what* the libraries are, *how* a
chip proof is structured, *which* file to look at for a given chip.
This directory is the **deeper field guide** that CLAUDE.md points into
when a topic deserves more than a paragraph.

If you're reading this because something in CLAUDE.md gestured at a doc
under `docs/`, look at the matching entry below.

## When to consult which doc

- **`LEAN_AND_SAIL_NOTES.md`** — toolchain compatibility quirks for the
  current Lean (4.29) and Sail RISC-V Lean (v4) pins. Read when an
  upgrade is on the horizon, or when a proof fails for reasons that
  smell version-specific (instance synthesis paths, `simp_all`
  behavior, `BitVec` rewrite ordering, Sail v2→v4 renames). Ends with
  a "what to look for on the next upgrade" rubric — the categories of
  breakage that recur — so the same investigation doesn't restart from
  zero when the toolchain moves again.

- **`FIELD_GENERIC.md`** — the field-genericization design, current
  state, polymorphic proof patterns, and recipe for instantiating at a
  new prime field (BabyBear, Mersenne31, …). Read when you're adding
  or migrating a chip's `_poly` companion, hitting a tactic that works
  on `Fin KB` but not `ZMod p`, or surveying what would change to add
  a second concrete field. Includes the DivRem worked example and the
  compressed timeline / design rationale appendix.

- **`CONSTRAINT_REGEN.md`** — the playbook for re-running
  `update_constraints.py` after the upstream SP1 constraint compiler
  changes a chip's column layout. Includes the canonical `is_trusted`
  removal cascade (17 chips), the mechanical `Main[k]`-shift recipe,
  the "shift + stop" fallback for landing the cascade incrementally,
  and the Fin-KB deletion-sweep template used to drop dead parallel
  layers once `_poly` siblings are sorry-free.

- **`PROOF_PATTERNS.md`** — performance wins, anti-patterns, kernel /
  elaboration landmines, and build-validation gotchas. Read when a
  proof is slow, mysteriously fails after appearing to elaborate, or
  when `lake env lean` says everything passed but you don't quite
  believe it. Aggregates the durable lessons from PR #92's ~40% perf
  effort, the kernel deep-recursion on `2^N` work, and the
  silent-success bug in `lake env lean` discovered during DivRem
  `_poly` work.

## Auto-memory mirror

`docs/memory/` is **not** part of this documentation set — it's a
mirror of Claude Code's per-machine project memory, persisted in the
repo so context survives a machine switch. The live memory lives at
`~/.claude/projects/<slug>/memory/`. See `docs/memory/README.md` for
the restore-on-new-machine recipe. Lessons from memory that are
durable across sessions get promoted *out* of memory into the
canonical docs above (typically into `FIELD_GENERIC.md`'s polymorphic
patterns section or `PROOF_PATTERNS.md`).
