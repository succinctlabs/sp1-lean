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

- **`CLEAN_OVERVIEW.md`** — onboarding and current state for the
  SP1Clean pilot. Read this first if you've heard "Clean" or
  "SP1Clean" without knowing what they refer to, how the parallel
  formalization differs from `SP1Chips/` / `SP1Operations/`, or what's
  built today. Covers the three proof layers (dirty `correct_*` /
  Clean `FormalAssertion` / trace), per-chip status across all 24
  chips, three-layer bridging discipline, faithful sub-circuit
  composition, and the canonical AddChip/AddOp pattern reference.

- **`CLEAN_VERIFICATION_STATUS.md`** — the **status of record** for the
  SP1Clean effort: a ground-truth snapshot (sorry/axiom inventory verified
  by `grep` + `#print axioms`, not docs), a per-chip closure matrix
  distinguishing *FormalAssertion-complete* from *actually complete*, the
  path to soundness-end-to-end, and the witness-generation frontier
  (boundary A intra-Lean vs boundary B Rust-prover link). Read this when you
  need *what is actually proven today* rather than narrative or roadmap, or
  to see why "closed" chips like Lt are complete only in the structural
  sense. Reconciles drift in `CLEAN_FUTURE.md` / `MULTIPLICITY_BUS.md`.

- **`CLEAN_PARALLEL_TRACKS.md`** — the open SP1Clean work partitioned
  into three **file-disjoint, logically decoupled tracks** for parallel
  overnight effort: (1) witness generation + combinatorial-ALU closure,
  (2) non-ALU control/memory chips, (3) final aggregation / soundness
  end-to-end. Each track names the files it owns, a recommended attack
  order, and per-track verification. Read this when coordinating
  multiple machines/sessions, or to see why the three fronts don't block
  each other (the join points are future, not overnight). Derived from
  `CLEAN_VERIFICATION_STATUS.md`.

- **`CLEAN_FUTURE.md`** — open work and roadmap for the SP1Clean
  pilot. Per-chip sorry register with verdicts (canonical /
  mechanical / needs-Gated / needs-memory-routing / scope-fence);
  phased plan (Phase A gating combinator → Phase B heavy ops → Phase
  C reader promotion → Phase D write-back tooling); critical-path
  steps to a single end-to-end ensemble soundness + completeness
  theorem; bridging hard SP1 proofs without rewriting; durable
  lessons distilled from iter-1 through iter-8 retrospectives. Read
  this when planning the next iteration of pilot work.

- **`STRUCT_DIVERGENCE.md`** — field-level snapshot of how far
  `SP1Clean/` column structs and `SP1Operations/` operation structs
  have drifted from upstream Rust (`../sp1`). Read when scoping a
  sync, evaluating coverage gaps (privilege/trap, paging, syscalls,
  lookup tables, etc.), or before any porting work that depends on
  upstream struct shape. Focuses on shape only — no constraint logic.

- **CLAUDE.md § "Faithful sub-circuit composition"** (not a separate
  doc — lives in the repo-root `CLAUDE.md`). Codifies the SP1Clean
  invariant: each `SP1Clean/Operations/<Op>.lean` and
  `SP1Clean/<Chip>Chip/Circuit.lean` exposes exactly one `main` and one
  `Spec`, composes sub-operations as `FormalAssertion` subcircuits
  (never inlining sub-constraints), and references sub-Specs by direct
  field application (never via `List.Forall SP1Constraint.toProp ...`
  envelopes). Read before adding a new Clean operation or chip.

- **`SPEC_AUDIT.md`** — per-`FormalSpec` classification of every
  entry in `SP1Clean/Chips/Spec.lean` into four categories: (a)
  minimal semantic + `RV64.*`, (b) internals + `RV64.*`, (c) faithful
  mirror without `RV64.*`, (d) Spec or `main` still incomplete vs
  upstream Rust. Read before deciding which chip Spec to upgrade
  next, or to understand the gap between a chip's `main`, its
  `FormalSpec`, and what the upstream constraint compiler emits.
  Ends with a "highest-leverage gaps" list ordered by faithfulness
  unlocked per unit of work.

- **`MULTIPLICITY_BUS.md`** — **work-in-progress** doc for the
  multiplicity-aware lookup bus refactor (`SP1Clean/SP1Lookup.lean`).
  Read this when the AddwChip op_c completeness `sorry` blocks you,
  when you need to extend `lookupGated` to a new gated lookup site,
  or when you need to understand SP1's `InteractionKind`-tagged
  multiset bus model (mirrors
  `sp1/crates/core/machine/src/air/memory.rs`). Documents the Phase
  1+2 foundation that's landed (`InteractionKind`, `HasDefaultRow`,
  real hint-witness `lookupGated`; all theorems axiom-clean) plus the
  Phase 3–5 roadmap for closing the two remaining `sorry`s in
  `AddwChip/Circuit.lean:152` and `MemoryConsistency.lean:1067`.
  Designed as a hand-off doc — start here if you're picking this work
  up cold.
