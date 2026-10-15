# Build profiling: which tool answers which question

The toolkit for finding out where build time goes, verified against the pinned toolchain and
`.lake/packages` (2026-09). Point-in-time numbers never live here: they go to the review artifact
that motivated them (`docs/audits/`, the `build-time` issues on the fork). Read together with
Clean's `doc/performance-problems.md` (the *why* of slow elaboration) — this file is about the
*measuring*.

## The one-line rules

- **Lake's `Built X (Ns)` is wall time of that job inside a parallel build**, not CPU and not the
  module's cost alone: two cold builds of the same tree differ by ≈ 5 % in the sum and by a median
  8 % per module, with a long tail beyond ±15 %. Judge a CI pair by the **sum, the wall and the
  critical path**; judge a *module* by a **solo CPU timing**.
- **`lake env lean <file>` applies neither `moreLeanArgs` nor `[leanOptions]`** and exits 0 on a
  stack overflow. It is not a gate and not a measurement. Pass the package flags (see
  `scripts/lean_flags.py`) or measure with `lake build <module>`.
- **Lake has no `-j`.** Its concurrency is the Lean runtime thread pool of the `lake` process —
  `LEAN_NUM_THREADS` (default: all cores), inherited by every child `lean`, which by default *also*
  uses all cores for async proof elaboration. `-j<n>` for the children goes through `moreLeanArgs`
  (traced: changes it → everything rebuilds); `LEAN_NUM_THREADS` is not traced.
- **Label every number** with machine, parallelism (solo / N-core / CI 4 vCPU) and what it
  measures (CPU, wall, `Built`). Hosted runners alternate CPU models (±10–15 %): record `lscpu`
  and compare same-model pairs.
- Lean elaborates proof bodies on parallel threads: a module's **CPU can exceed its wall**, and the
  profiler's `blocked (unaccounted)` is the main thread waiting for those tasks. Read
  `simp`/`tactic execution`/`type checking` together with it.
- The profiling runner warms the strict full library, never stops another process, and fails
  if a measurement emits diagnostics or lacks the final cumulative report. Its `exit` field
  includes output-validation failures. Keep the logs and finish a Lean change with the strict
  full build; profiler output is not a proof gate.

## Whole build

| Question | Tool | Invocation | Output / gotcha |
|---|---|---|---|
| What did a CI build spend, per module? | Lake `Built` lines + `scripts/profile_aggregate.py --lake-log` | `gh api repos/dtumad/sp1-lean/actions/jobs/<job id>/logs > ci.log; scripts/profile_aggregate.py --lake-log ci.log --out out/build-log --top 30` | ranking, per-pillar sums (`.md/.tsv/.json`). The GitHub log carries a timestamp per line; a local `lake build` log does not. `gh run view --log` is empty while a run is in progress; use the jobs API. |
| Is the build critical-path-bound or throughput-bound? What can P processors never beat? | `scripts/build_semantics.py` (`critical_path.md`) | `scripts/build_semantics.py --lake-log ci.log --out out/bsem [--processors 4]` | longest import-weighted path through the built modules, `max(CP, Σ/P)`, the path itself. CP > Σ/P → shorten the path; otherwise only CPU-seconds help. Dependencies outside the import graph (Clean, …) count in Σ but not in the path. |
| How many jobs were running when? Is there a single-job tail? | `scripts/build_semantics.py` (`timeline.md`, timestamped logs only) | same command | span, average/peak concurrency, seconds at ≤ 1 / ≤ 2 running jobs, the longest solo stretch (a critical-path module running alone). Jobs under 1 s are left out. |
| Did my PR move the build? | `scripts/build_semantics.py --compare` | `scripts/build_semantics.py --lake-log base.log --compare head.log --out out/cmp --touched touched.txt` (`touched.txt` = `git diff --name-only base..head`) | `compare.md`: both totals and critical paths, the touched modules' deltas, largest regressions/improvements among common modules, a noise check over untouched modules. |
| Which layer / stratum / claim closure pays what? | `scripts/build_semantics.py` (`layers.md`, `claims.md`, `unreached.md`, `chips.md`) | as above, optionally `--profile-dir <solo sweep>` for the category split | the cost-versus-claims tables of `docs/audits/2026-09-build-semantics.md`. |
| A controlled cold / warm measurement on the CI runner, without touching the shared cache | `.github/workflows/build-experiment.yml` | `gh workflow run build-experiment.yml --ref <branch> -f label=<tag> -f restore=none [-f lean_num_threads=3] [-f targets=…]` | job summary: runner inventory, `time -v` (max RSS, CPU-seconds), swap-out from `vmstat`, critical path, timeline, top modules; artifact `experiment-<label>-<run id>` with `lake.log` (time-stamped), `vmstat.log`, `ps.log`, `time.txt`. The workflow file must exist on `main` to be dispatchable; `--ref` picks the branch to build. |
| Import graph, transitive-import waste | importGraph | `lake exe graph --to SP1Clean out.html` / `lake exe unused_transitive_imports <mods>`; `#redundant_imports`, `#min_imports` (`import ImportGraph.Tools`) | needs built oleans. `lake shake` (Lake's, the successor of Mathlib's) only runs on `module` files — usable after the `SP1Clean/` migration (#33). No `lake exe pole` exists in this dependency set; the critical path above replaces it. |

## One module

| Question | Tool | Invocation | Output / gotcha |
|---|---|---|---|
| Solo cost and Lean's category split for a set of modules | `scripts/profile_compile.sh` | `SKIP_BUILD=1 OUTDIR=.lake/profile/<tag> scripts/profile_compile.sh SP1Clean/Proofs/Chips/AddChip/` (a path prefix; `TREES=… SKIP_BUILD=1` for a full sweep, ≈ 1 h, machine idle) | `summary.tsv` (`cpu wall exit module`, CPU first), `profile.md/json` (`import`, `elaboration`, `simp`, `tactic execution`, `type checking`, `typeclass inference`, `interpretation`, `blocked`, …). Requires warm oleans; run solo after other builds finish. Stop only identified stale LSP workers; never `lean --server` or `lake serve`. Use 3 runs and their median for a claim. |
| The same by hand | `lean --profile` / `-Dprofiler=true` | `lean $(scripts/lean_flags.py --shell) -Dprofiler=true -Dprofiler.threshold=50 <file>` (after `eval "$(lake env)"` or with `LEAN_PATH` set) | per-declaration lines above the threshold (ms) + `cumulative profiling times:`; add `-Dtrace.profiler=true` for nested timings. Categories seen here: `import`, `parsing`, `elaboration`, `type checking`, `typeclass inference`, `tactic execution`, `simp`, `dsimp`, `interpretation`, `linting`, `compilation …`, `.olean serialization`, `blocked`, `do element elaborator`, `grind …`. |
| Where inside a slow declaration is the time (a flame graph) | `trace.profiler.output` | `lean … -Dtrace.profiler=true -Dtrace.profiler.threshold=10 -Dtrace.profiler.output=prof.json <file>` then open `prof.json` at profiler.firefox.com (`-Dtrace.profiler.serve=true` serves it directly); `-Dtrace.profiler.output.pp=true` keeps full trace text, `-Dtrace.profiler.useHeartbeats=true` reports heartbeats instead of seconds | Firefox Profiler format; categories `Elab`, `Elab.async`, `Elab.block`, `Meta`, `Kernel`. This is the tool that attributes `interpretation` (which interpreted tactic/simproc) and `type checking` (which declaration hits the kernel cliff). |
| Peak memory of one module | `/usr/bin/time` | `/usr/bin/time -l lean … <file>` (macOS: "maximum resident set size" in bytes) / `-v` on Linux (kB) | the import floor is ≈ 2.6–3 GB with the Mathlib + Clean + Sail-model closure; a module's own peak is what it adds. |
| How much do the imports cost before any elaboration? | import-probe file | a one-line file `import <X>` + `example : True := trivial`, timed with `-Dprofiler=true` and `/usr/bin/time -l` | the `import` category and RSS for that root; multiply by the number of modules whose closure contains it. `lean --stats` prints the environment's import counts and bytes. |
| Is a whole file within budget under the real configuration? | `lake build <module>` | `lake build SP1Clean.Proofs.Chips.AddChip.Formal` (or `lake lean <file>`, which applies the module's setup + `moreLeanArgs`) | the only authoritative signal for a build failure or a `maxRecDepth`/heartbeat cliff (`docs/agents/proof-patterns.md`). |

## One declaration

| Question | Tool | Invocation | Output / gotcha |
|---|---|---|---|
| Heartbeats of a declaration (is it near the ceiling? how variable?) | Mathlib `#count_heartbeats` | `#count_heartbeats in theorem …` / `#count_heartbeats! 5 in …` (repeats, range and stddev) / `guard_min_heartbeats n in …`; `#count_heartbeats` alone turns on `linter.countHeartbeats` for the rest of the file | runs the command with `maxHeartbeats 0`, so it reports the true cost but not whether the real ceiling would have been hit — measure floors by lowering `maxHeartbeats` and rebuilding (`docs/agents/proof-patterns.md`). |
| What did `simp`/`whnf`/instance search unfold, and how often? | `diagnostics` | `set_option diagnostics true in` (+ `diagnostics.threshold n`) | `[reduction]` unfolded declarations/instances, `[type_class]` used instances, `[simp]` used/tried theorems, `[kernel]` unfolded declarations, `[def_eq]` heuristics — the map from a slow `simp only [circuit_norm]` to the lemma that keeps firing. |
| Which instance search is slow | `trace.Meta.synthInstance` (+ `trace.profiler`) | `set_option trace.Meta.synthInstance true in` | candidate ladders; `synthInstance.maxHeartbeats`/`maxSize` are the ceilings. |
| What a command added to the environment | Mathlib `whatsnew` | `whatsnew in <cmd>` | new declarations (e.g. the auxiliary lemmas a `deriving` or a `simp` produced). |
| A quick per-line profile from the editor | lean-lsp MCP `lean_profile_proof` | tool call with file + line | runs `lake env lean --profile -Dtrace.profiler=true` on the single declaration: **no package flags**, same-file dependencies absent; good for a first look, not for a number. |

## Reading `-Dprofiler` categories

- `import` — loading the olean closure; the per-module floor. Only import narrowing, precompiled
  or module-system oleans move it.
- `elaboration` — term elaboration outside tactics (structure/`deriving`/`let` chains, statement
  elaboration of large theorems).
- `simp` / `tactic execution` / `typeclass inference` — the tactic mix; `trace.profiler.output`
  or `diagnostics` say which call.
- `type checking` — the kernel; large values mean a kernel size cliff (Clean's
  `performance-problems.md`: make the expensive value opaque, state facts over variables).
- `interpretation` — tactic, simproc and `deriving` code that is not native: Mathlib's and
  Clean's tactics, this repo's own, `decide`-by-evaluation. Native code is only what the toolchain
  ships or what a library precompiles (`precompileModules`).
- `blocked (unaccounted)` — main thread waiting for async proof bodies; not a cost of its own.
- `do element elaborator` — the `do` notation elaborator (the generated Sail model's
  `print_rvfi_exec`, lean4#13858).

## Measurement pitfalls (each cost a wrong conclusion once)

- `lean -Dprofiler=true`'s `cumulative profiling times:` block goes to **stderr**; the per-event
  lines go to stdout. Capture both.
- A profiler category sum is not wall: proof bodies elaborate on parallel threads, and
  `blocked (unaccounted)` is the main thread waiting for them — it can exceed wall many times over.
  Compare `user+sys` CPU across runs, not the category sums.
- Per-module `Built` times in a parallel build are noisy: two cold builds of the same tree gave a
  median 8 % per-module difference with a long tail beyond ±15 %, while their sums differed by 5 %.
  The same configuration on two runner models differed by 18 % (hosted runners alternate CPU
  models; the experiment workflow records `lscpu`, the production jobs do not). Judge a change by
  Σ, wall and critical path across a pair; judge a module by a solo timing.
- The tool's numbers age with the toolchain: the 2026-09-20 solo sweep's "26 % interpretation,
  9 s per load/store `Formal` file" was true on v4.32.2 + the Clean fork and false one bump later
  (0.5 s). Re-sweep before citing a category split after a toolchain or Clean move.
- `interpretation` is interpreted *tactic* code (Mathlib/Clean/ours), not `decide` proofs or the
  kernel — see proof-patterns.md. The plain profiler names the interpreted constant; only
  `trace.profiler.output` names the call site.
- Run local profiles **solo**: a `lake build` in another shell (or an agent's) inflates every
  number, including `import` (measured 1.2 s → 4.8 s). And never switch git branches in a checkout
  while a `lake build` runs there — Lake reads sources as it reaches them.
- **A measurement loop can put the machine into swap and void its own results.** Eight
  elaborations of a 5 900-line file back to back left `vm_stat` at 14 M swap-outs and turned a
  34 s file into 348–673 s; the per-declaration numbers from that loop were meaningless. Check
  `sysctl vm.swapusage` / `vm_stat` before trusting a solo number, stop only identified stale
  `lean --worker` processes (never `lean --server` or `lake serve`), and re-run the two configurations you
  actually want to compare back to back.
- **Do not attribute kernel time by replacing a proof with `sorry`.** `sorry` changes the
  elaboration path, not just the term: replacing one structure field of
  `divRemChip_rtypeGroundingData` with `sorry` took the file from 34 s to 673 s. Attribute with
  `-Dtrace.profiler=true` (its `[Kernel] typechecking declarations [X]` nodes name the
  declaration) and, within a declaration, by truncating the tactic block at successive points.
- `lake env lean` applies no package flags (`scripts/lean_flags.py` prints them); it also exits 0
  on a stack overflow.

## CI pitfalls (the design that answers them is in the workflow headers)

- `actions/cache` restore-key fallbacks match the **newest** entry with the prefix, blind to branch
  history: a bare `<prefix>-` fallback restored a stale lineage and rebuilt a scripts-only PR from
  scratch (582 modules, 22.5 min). `scripts/ci/cache_pick.py` chooses by first-parent lineage; no
  bare prefix fallback exists any more.
- The `path:` list is part of an entry's version hash: editing it invalidates every entry, so it
  ships with a `SP1_CACHE_VERSION` bump and one cold transition.
- A PR's entries live on `refs/pull/N/merge` and are invisible to `main`, so every merge used to
  redo the PR's build. After all full checks pass, the build runner passes the completed core,
  alignment and test build to `main` as an artifact. Lake still checks the merged tree's content hashes.
- Mathlib's downloaded cache includes generated C but omits native objects. A separate cache,
  keyed by toolchain and dependency pins, retains those objects and their traces for the
  backend exporter. Only full runs save it; downloaded oleans are not duplicated there.
- Weekly runs and the manual `clean_build` input discard project outputs while reusing pinned
  dependencies. The full phase uses the same runner and fresh build directory as the core phase.
  This catches stale project oleans, including imports of deleted modules.
- Never save the cache from a cancelled job (a truncated `.olean` behind a written trace poisons
  every later restore); `main` runs queue instead of cancelling.
- The 4-vCPU runner does not swap; the 5–11× CI-vs-solo inflation of big modules was **CPU
  oversubscription** — Lake runs `LEAN_NUM_THREADS` jobs (default = cores) and each child `lean`
  also defaults to all cores. 16 threads on 4 vCPU cost a third of the CPU-seconds; 3 jobs × 2
  threads (`LEAN_NUM_THREADS=3` + `-j2` in `moreLeanArgs`) is −17 % wall on a cold build.
- GitHub serves a job's log only after it completes; `gh run view --log` is empty in progress.
- The `build` runner performs core and full builds on every PR, then full-tree `lake lint`,
  export/conformance gates and both compiled trust scopes. Setup and cache restore/save happen
  once, and full lint covers the core. `build-full` retains the full-check status name and fails
  if that runner fails, is cancelled or does not select full validation; it performs no build.
  Core-only dispatches and `ci-testing` pushes still run core lint. No label controls PR coverage.
- Production, cache cleanup and build experiments must agree on the cache version; production
  and experiments also need identical path lists, since paths participate in the cache identity.
  Tooling regressions check this contract. Changing only the producer can make cleanup delete
  valid entries or make a purported warm experiment miss its cache.

## Measurement protocol for a build-time PR

1. **Before**: a CI pair from `build-experiment.yml` on the base and the head commit with identical
   inputs (same `restore`, same `LEAN_NUM_THREADS`), and — for a Lean-source change — the solo
   sweep of the touched modules on the base.
2. **After**: the same on the head; `scripts/build_semantics.py --compare` for the pair.
3. **Report** in the PR body: modules built, Σ `Built`, build-step wall, critical path, the touched
   modules' solo CPU before/after (median of 3), the profiler category the change claims to move,
   both run ids.
4. **Acceptance**: a Lean-source PR shows ≥ 20 % solo CPU on every module it names, adds no entry to
   `scripts/option_escapes_allowlist.txt`, adds no trust-policy exception and no untouched module
   consistently regressed (beyond the ≈ ±15 % per-module noise); a CI/lakefile PR moves Σ or wall
   beyond the ≈ 5 % noise floor on same-CPU runs, two repeats when the effect is small.

The package flags for any direct `lean` invocation: `scripts/lean_flags.py [--lib SP1CleanTest|LeanRV64D] [--shell]`
(package `moreLeanArgs` + `[leanOptions]`, the library's own winning on a key, as in Lake).
