# Build-time reduction campaign — results (2026-09-21/22)

Point-in-time record of the campaign tracked by fork issue #43 (sub-issues #36–#42, plus #6 and
#20). Method, tooling and the durable rules live in `docs/agents/build-profiling.md` and
`docs/agents/proof-patterns.md`; this file holds the numbers and the verdicts, and is not
maintained after the campaign closes.

Measurement conventions: **solo** = one `lean` process against warm oleans on a 14-core macOS
machine with the package flags (`scripts/lean_flags.py`), machine otherwise idle, ≥ 2 runs; **CI**
= GitHub `ubuntu-latest` (4 vCPU / 16 GB), named by run/job id. Per-module `Built` times inside a
parallel build carry a median 8 % run-to-run spread, so module claims are solo and build claims
are Σ / wall / critical path.

## Where the time went, and where it went to

| Tier | Case | Before | After | Mechanisms |
|---|---|---:|---:|---|
| T1 | warm PR run; `main` after a merge | 6.4–7.4 min over 3 jobs; `main` redid the PR's build (24–75 min) | ≈ 3–5 min, one job; `main` reuses the PR's build | job folding, lineage keys, PR→main hand-off |
| T2 | cold-project PR (the 552-module core) | 22.5–29 min | ≈ 24 min | concurrency cap, import floor, module fixes |
| T3 | cold bump (toolchain/pin/options) | 65–75 min build, 75 min job | ≈ 32 min build | RvfiDii, `-j2` + `LEAN_NUM_THREADS=3` |
| T4 | alignment after a merge | 56–110 min, 3 of 7 runs cancelled mid-build | 38.5 min for the whole job | same-run core restore, folding, module fixes |
| — | Actions cache | 10.72 GB, LRU-evicting, ≈ 6.5 GB unreachable | 8.0 GB, lineage-correct, self-pruning | keys, gc, closed-PR cleanup |

The two structural facts behind the tier numbers: the cold build was **critical-path-bound** on one
generated module (3,554 s path, 100 % of the 4-processor bound, a single job running for the last
26 minutes), and the runner was **CPU-oversubscribed**, not swapping — Lake runs `LEAN_NUM_THREADS`
jobs and each child `lean` also defaulted to every core, so 16 threads shared 4 vCPU and spent a
third of the build's CPU-seconds in contention.

## Module-level results (solo CPU)

| Module | Before | After | Δ | Mechanism | PR |
|---|---:|---:|---:|---|---|
| `LeanRV64D.RvfiDii` | 718 s / 15.4 GB | 2.5 s / 1.4 GB | −99.7 % | lean4#13858 `do`-elaborator blow-up; one-module library with `backward.do.legacy` | #46 |
| `Extracted/SystemOracle/Global` | 124 s / 14.4 GB | 14.7 s / 2.9 GB | −88 % | 1,649-binding nested `let` chain hoisted to top-level defs by the emitter | #51, #56 |
| `Soundness/Grounding/RTypeChips` | 61.7 s | 10.2 s | −84 % | whole-row `circuit_norm` → scalar view projections | #55 |
| `Proofs/Chips/DivRemChip/Evidence` | 38.9 s | 7.5 s | −81 % | 121-conjunct `obtain` chunked | #59 |
| `FormalModel/Contracts/DivRemColumns` | 45.0 s | 9.2 s | −80 % | per-field `eval` lemmas by `rfl` (template, ≈ 144 modules) | #52 |
| `Soundness/GroundingAdapter` | 52.3 s | 10.6 s | −80 % | as `RTypeChips` | #55 |
| `Faithful/SyscallInstrsChip` | 60.1 s | 27.0 s | −55 % | two 80-conjunct `rintro`s chunked | #58 |
| `Model/Register` | 15.3 s | 7.1 s | −53 % | 62 `fin_cases` → `decide +kernel` | #48 |
| `Proofs/Chips/ShiftRightChip/Core` | 37.3 s | 20.7 s | −44 % | 7 `nlinarith` → `omega` / existing helpers | #49 |
| every module's import floor | 1.19 s / 3.07 GB | 0.91 s / 2.27 GB | −0.28 s, −0.8 GB | 28 wholesale `Mathlib.Tactic` imports narrowed | #54 |

## CI changes

`lean_action_ci.yml` now carries the whole pipeline: `guards`, `build` (core + tests + save +
lint + export identity + per-PR cache dedupe), `handoff`, and `build-full` (the alignment layers,
full test library, `lake lint`, witgen regeneration, both censuses, cache gc) gated on pushes to
`main`, the weekly schedule, a dispatch input, or the `ci:alignment` label. `alignment.yml` is
gone. Cache entries are chosen by first-parent lineage (`scripts/ci/cache_pick.py`), pruned by
rule (`scripts/ci/cache_gc.py`, `cache-cleanup.yml`), and exclude the packages `lake exe cache
get` already restores. Runs on `main` queue instead of cancelling.

## Closed as measured negatives

- **`Proofs/Sail/InstructionDecode/Families`** (528 s CI, the remaining T4 critical-path head).
  112.7 s of self time in 3,194 `conv_lhs => whnf` steps (≈ 51 per lemma × 62 lemmas); the
  per-node guard needs the full default simp set. Four variants measured on a 5-lemma probe
  (baseline 11.5 CPU-s): `simp_all only` + arithmetic closers 26.7 s with failures; goal-only
  `simp` 3.5 s but wrong; `simp [*, …]` 3.5 s but changes the guard's normal form and breaks the
  walk downstream; cheap-first with `done` 13.0 s. `ext_decode` is one monolithic 27,530-line
  `encdec_backwards`, so a shared-prefix lemma cannot be stated without naming a giant internal
  continuation. Remaining route: one decoder-table lemma with the 62 family lemmas as lookups —
  multi-day, essentially moving the whole-parser agreement theorem upstream of them.
- **`Soundness/Grounding/MemoryChips`** (164 s CI): no declaration above 700 ms; ≈ 300 theorems
  at ≈ 100 ms each. A template cost, not a hotspot.
- **Chunking 43–53-conjunct destructurings** (5 files): −3 % to noise, reverted. The super-linear
  cost bites at ≈ 80+ conjuncts.
- **Precompiling tactic code**: the profiler's `interpretation` share is Mathlib's tactics, which
  this repo cannot precompile; the earlier "26 % of the core" figure was a pre-v4.33 measurement
  and is now 0.5 s on the modules it named.

## Regression that reached `main`, and the process fix

#51 added 3,963 generated definitions whose uniform binder block made `unusedArguments` fire 384
times. PR CI was green because the full-tree `lake lint` runs only in `build-full`; `main`'s next
run went red (run 35683302943) and #56 fixed it in the emitter. The rule — label alignment-layer,
generated, `ToClean`, pin or exporter PRs `ci:alignment` — is in `docs/agents/build-profiling.md`
and `guards` prints a notice when it is missing.

## Open items

- #20: per-cluster keep/park/retire decisions (frontier-only 283 modules / 2,377 s = 23 % of the
  full build; 72 modules reached by no headline claim / 345 s; the exact-relation stack 82 s).
- #41: the `Families` decoder-table refactor, if the critical path becomes the binding constraint
  again.
- #33: module-system tier 2 (a dev-loop lever: a proof edit still rebuilds importers).
- #6: the durable RvfiDii fix (Sail backend emitting `let _ : Unit := e`), after which the
  `LeanRV64DRvfi` library goes.

## Reproduction

```bash
scripts/profile_compile.sh <path prefix>                     # solo per-module CPU + categories
scripts/profile_aggregate.py --lake-log <log> --out <dir>    # per-module times of a real build
scripts/build_semantics.py --lake-log <log> --out <dir> \
    [--compare <head log>] [--processors 3]                  # layers, claims, critical path, pairs
gh workflow run build-experiment.yml --ref <branch> -f label=<tag> -f restore=none
```
