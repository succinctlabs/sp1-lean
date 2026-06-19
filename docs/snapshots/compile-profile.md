> **Point-in-time snapshot — regenerate before relying on it.**

# Compile-time profile — SP1Clean

Per-module wall-clock elaboration profile, with per-tactic attribution for the worst offenders and
the common threads behind them. Measured **2026-06-10** (Lean v4.28.0, warm olean cache, branch
`full-clean-dsl-implementation`), **after** the get_elem fast-path / linter / `localLength_eq`
optimization batch landed that same day. The pre-fix baseline, per-module delta table, probe
evidence, and drafted upstream reports live in `docs/snapshots/profile-baseline-2026-06-10/`
(`findings.md` is the diagnosis writeup).

**Headline: the 2026-06-10 batch cut isolated elaboration of the swept set in half — 3422s → 1689s
(−50.7%), no regression beyond ±2% noise.** The three fixes, by measured leverage:

1. **`v[i]` index-bound `decide` fast path** (`Foundations/GetElemFastPath.lean`, one `macro_rules`
   line): every `v[i]` elaboration was paying ~11 `rw/dsimp … at *` context traversals inside Std's
   slice `get_elem_tactic_extensible` rule — ~0.34s per `[i]` under a fat proof context, ~0.8s per
   `have`. This single fix produced most of the −50%: medium chip Formal files −70%, generated
   `Extracted/` files −87…93% (their `#v[…][k]` projection chains were this, not "monolithic term
   elaboration"), `BranchChip.Formal` −77%, `OwnAsserts` −92%.
2. **`set_option linter.all false` on the 76 auto-generated modules** (~1.6s/file linter
   interpretation tax; emitted by the `update_extracted.py` templates).
3. **`localLength_eq := by intros; simp +arith […]`** on the two ALU readers — the silent
   `by intros; rfl` field default whnf-unfolds all of `main` (334k heartbeats ≈ 15.5s each; the simp
   route is 109× cheaper). Both readers now fit the **default** heartbeat/recdepth budgets.

## How to re-run

```sh
scripts/profile_compile.sh            # whole library (warm-builds first, then sweeps)
SKIP_BUILD=1 scripts/profile_compile.sh            # cache already warm
SKIP_BUILD=1 scripts/profile_compile.sh Operations/  # scope to one subdir
EXCLUDE_RE='Chips/DivRemChip/Soundness/' scripts/profile_compile.sh Chips/  # skip the conjuncts
```

Outputs land in `build/profile/`:
- `summary.tsv` — `seconds⇥exit⇥module`, sorted slowest-first (the canonical offender ranking)
- `summary.md` — same as a markdown table + totals/failures footer
- `<module>.log` — the full `-Dprofiler=true` breakdown for each module
- `measurements.jsonl` — one archival JSON-Lines record per module

## Method & caveats

After one warm `lake build`, each module is re-elaborated in isolation with
`lake env lean -Dprofiler=true -Dprofiler.threshold=50 <file>`. Every dependency loads from its cached
`.olean`, so the timing isolates **that one file's** elaboration. Caveats:

1. **Import tax is a sweep artifact** (~1s/file, shared in a real parallel build). It dominates the
   cheap files; the ranking of expensive files is accurate.
2. **Profiler sums over-count** (nested/cumulative) — per-category numbers are dominance signals,
   not an additive budget.
3. **`lake env lean` exits 0 even on a stack overflow** — the script records exit codes; this run
   had **0 nonzero exits** across all 260 modules.
4. **The nine `Chips/DivRemChip/Soundness/*.lean` conjuncts are excluded** (each is 18–33 min to
   elaborate in isolation); their costs are taken from `lake build` logs instead — see below.

## Headline numbers (post-fix sweep)

- **260 modules, ~1689s total** (sequential, isolated; excludes the DivRem conjuncts).
  Mean 6.5s, **median 2.7s**, p95 28.3s, **max 118s** (was max 462s).
- 156/260 modules elaborate in <3s (≈ import floor).
- Generated modules (`Extracted/`, `Operations/*/Extracted`, witness vectors): **245.6s across 77
  files — was 1178.8s.**

### Time by subsystem (vs pre-fix baseline)

| Subsystem | Time | was | Files |
| --- | ---: | ---: | ---: |
| `Chips/` (excl. DivRem conjuncts) | 1041s | 1598s | 95 |
| `Operations/` | 285s | 553s | 62 |
| `Extracted/` | 146s | 1013s | 50 |
| `Foundations/` | 91s | 90s | 16 |
| `WitnessTests/` | 85s | 88s | 27 |
| `Readers/` | 40s | 81s | 10 |

### DivRem soundness conjuncts (from `lake build` logs, ≤5-way-parallel — contention-inflated)

Rem 1997s, Div 1849s, Remu 1706s, Divu 1651s, Divw 1535s, Divuw 1494s, Remw 1256s, Remuw 1090s,
Reader 720s — **~3.7 CPU-hours, the library's dominant remaining cost.** (Pre-fix sum of the same
seven measured files was ~15% higher.) Probe-measured: `circuit_proof_start` is only ~90s of each;
the rest is per-conjunct omega/bitvec/carry proof bodies at 128M maxHeartbeats.

## Top offenders (post-fix)

| # | Time | Module | Note |
| ---: | ---: | --- | --- |
| 1 | 118s | `Chips.DivRemChip.Defs` | instance-field simps + **kernel type-checking** (~40s) — next target |
| 2 | 81s | `Chips.ShiftRightChip.Soundness.Sra` | conjunct proof body |
| 3 | 73s | `Chips.ShiftRightChip.Soundness.Sraw` | conjunct proof body |
| 4 | 73s | `Chips.ShiftRightChip.Soundness.Srl` | conjunct proof body |
| 5 | 69s | `Chips.ShiftRightChip.Soundness.Srlw` | conjunct proof body |
| 6 | 45s | `Chips.ShiftRightChip.Core` | arithmetic lemma farm |
| 7 | 45s | `Chips.ShiftLeftChip.Soundness.Sll` | conjunct proof body |
| 8 | 41s | `Chips.ShiftLeftChip.Soundness.Sllw` | conjunct proof body |
| 9 | 41s | `Operations.MulOperation.RawSpec` | |
| 10 | 40s | `Operations.MulOperation.Formal` | was 121s (−67%) |
| 11 | 37s | `Chips.ShiftRightChip.Dispatch` | |
| 12 | 31s | `Extracted.DivRemChip` | **was 462s (−93%)** |
| 13 | 29s | `Chips.ShiftLeftChip.Core` | |
| 14 | 28s | `Chips.ShiftRightChip.Defs` | was 60s |
| 15 | 27s | `Operations.LtOperationUnsigned.RawSpec` | |
| 16 | 27s | `Foundations.SailWrap` | 232 mathlib-style simp calls — not Clean-related |
| 17 | 25s | `Chips.DivRemChip.Formal` | |
| 18 | 23s | `Foundations.Register` | mathlib-style — not Clean-related |
| 19 | 23s | `WitnessTests.MulOperationWitnessVectors` | `native_decide` anchor data |
| 20 | 21s | `Chips.BranchChip.Formal` | was 95s (−77%) |

## What the 2026-06-10 diagnosis established (kill-list of myths)

Full evidence: `profile-baseline-2026-06-10/findings.md`. In brief:

- **`circuit_proof_start` / bind-chain normalization is NOT the bottleneck** — 6k–32k heartbeats on
  medium chips (~10% of file cost), 320k (~90s) even on DivRem's `main`, the repo's biggest. A
  once-per-chip "normalized ops" lemma (main_ops_eq) would save only ~13 min across DivRem's nine
  files — parked (`scratch/design-main-ops-eq-divrem.md` at the measurement commit).
- **The dominant medium-chip cost was `v[i]` elaboration**, fixed by the decide fast path.
- **`ElaboratedCircuit` field defaults can silently cost seconds**: `localLength_eq`'s `rfl` default
  whnf-unfolds `main`; the `channelsLawful` default outright fails on channel-heavy mains. Watch for
  this on every new chip with a non-trivial `main` (hand-write the simp-route `localLength_eq`).
- The old threads C/E ("linter tax" / "Extracted monolithic terms") are **resolved** — E was mostly
  the `v[i]` tax in disguise.

## Addendum 2026-06-19 — the numbers above are STALE (pre-pillar-refactor); partial re-measure + DivRem tail dedup

This snapshot predates the pillar refactor (merged 2026-06-18) and was contention-inflated. Two of
its "next targets" were re-measured in isolation (`lake env lean -Dprofiler=true`, warm cache) and
came out very differently — **do not trust the absolute seconds above without re-running
`scripts/profile_compile.sh`.**

- **`Chips.DivRemChip.Defs` is NOT 118s — it is ~37–40s in isolation** (3 instance-field simps
  ≈ 21s total: 9.99s `channelsLawful` + 7.13s + 3.95s; type-checking ≈ 10.6s). Target #2 below is
  largely obsolete; the only lever left is sharing the one `main` unfold across the 3 field proofs
  (the parked `main_ops_eq`), worth ~14s — marginal.
- **DivRem soundness conjunct cost is dominated by the Mul product-glue, NOT omega/carry.** Profiling
  a spec-only conjunct (after the tail dedup below): the `linear_combination`/`omega` bridges are
  negligible; ~167s is **4 `simpa … using h_ctq_k` product-glue calls (37–44s each)** establishing
  `r_k = cols.product[2k] + cols.product[2k+1]·256` against the witnessed 16-element `mul_lower`/
  `mul_upper` product vectors, plus `instantiate metavars` 41s and the two big `obtain`s (~25s).
  **This cost is term-intrinsic** — swapping the heavy `circuit_norm` simp set for the minimal
  `[Vector.getElem_map, getElem_mapRange]` built green with **zero speedup** (274→274s). The
  "minimal-context pure-ℕ lemma" lever (target #1) does NOT apply; reducing it needs deeper
  restructuring of how the Mul product columns are reduced. Open, harder than billed.

**Landed 2026-06-18/19 (compile-time campaign, commit f0e6f82+):** the shared `Operations.Requirements`
"tail" of the 9 DivRem soundness conjuncts (byte-identical 265 lines, re-elaborated 9× at 128M HB) is
now proved **once** in `Proofs/Chips/DivRemChip/Soundness/Tail.lean` (`requirements_holds` +
`SpecObligation`/`soundness_of_specObligation` combinator + `spec_proof_start` elab). Each conjunct
delegates; `lake build SP1Clean` green (3676 jobs), axiom-clean. The same shared-obligation structure
was **verified** in the ShiftRight conjuncts (the `cpuA/msb1A/msb2A/msb3A/aluA` block is byte-identical,
236 lines, across Srl/Sra/Srlw/Sraw) — Phase 3 (apply the same dedup) is viable but a smaller prize.

## Where to optimize next (by leverage)

1. **DivRem conjunct proof bodies** (~3.7 CPU-h): the omega/carry work in heavy contexts. Known
   pattern from the files' own comments: extract minimal-context pure-ℕ lemmas so omega certificates
   shrink. Large effort, largest prize. *Open.* **(See 2026-06-19 addendum: re-measured — the cost is
   the Mul product-glue `simpa`, term-intrinsic, not omega; this lever does not apply.)*
2. **`Chips.DivRemChip.Defs` (118s)**: instance-field `simp` proofs 20s+ each plus ~40s kernel
   type-checking — investigate proof-term size of the field proofs (`share common exprs` lines).
   *Open.*
3. **ShiftRight/Left conjunct bodies** (~70–81s each) — same family as (1). *Open.*
4. **maxHeartbeats ratcheting**: post-fix, ceilings everywhere are loose (e.g. 16M-HB files now run
   in seconds). Mechanical sweep with `#count_heartbeats`, restores regression-alarm value. *Open.*
5. **Upstream filings** (`profile-baseline-2026-06-10/upstream-notes.md`): lean4/Std slice-rule
   `at *` report; Clean `localLength_eq`/`channelsLawful` default reports. *Drafted, not filed.*
6. `Foundations.SailWrap` / `Foundations.Register` (~50s combined): mathlib-style simp-heavy proofs,
   independent of Clean. *Open, low priority.*

## Verification of this run

- Coverage: 260 modules swept, 0 nonzero exits; DivRem conjuncts excluded by `EXCLUDE_RE` (costs
  recorded from build logs).
- Post-fix gate: `lake build SP1Clean` green (3630 jobs), only the five pre-existing `sorry`
  warnings (ShiftLeft/ShiftRight/Mul/DivRem `Formal`, `SP1GatedVm`), 0 new warnings, 0 `info:` notes.
- Axiom audit: representative headline theorems (StoreByte soundness/completeness + bridge, both ALU
  readers, Jalr, DivRem soundness, `correct_add_native`) all match the axiom ledger — no `sorryAx`,
  no new axioms from the decide-based proofs.
