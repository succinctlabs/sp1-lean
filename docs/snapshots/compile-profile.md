> **Point-in-time snapshot — regenerate before relying on it.**

# Compile-time profile — SP1Clean

Per-module wall-clock elaboration profile, with per-tactic attribution for the worst offenders.
Measured **2026-06-22** (Lean v4.28.0, 24-core host, warm olean cache, branch
`dtumad/div-rem-perf` / PR #103). This run measures **all** modules in isolation, including the nine
DivRem soundness conjuncts (previously excluded and quoted from a contention-inflated parallel build
log — they are now clean isolated numbers).

The durable proof-engineering lessons that came out of profiling (the `v[i]` fast path,
`circuit_proof_start` is not the bottleneck, the `localLength_eq` `rfl` cost, the shared-tail dedup
pattern) live in `docs/agents/proof-patterns.md` § "Compile-time / performance landmines". An older
pre-refactor baseline is archived under `docs/snapshots/profile-baseline-2026-06-10/`.

## How to re-run

```sh
scripts/profile_compile.sh                          # warm-builds first, then sweeps every module
SKIP_BUILD=1 scripts/profile_compile.sh             # cache already warm — skip the warm build
SKIP_BUILD=1 scripts/profile_compile.sh Operations/ # scope to one subdir
# The nine DivRem soundness conjuncts are 277–307s EACH in isolation (~40 min for the nine). To skip
# them for a quick non-conjunct pass and take their cost from a build log instead:
SKIP_BUILD=1 EXCLUDE_RE='Soundness/(Div|Divu|Divuw|Divw|Reader|Rem|Remu|Remuw|Remw)\.lean$' \
  scripts/profile_compile.sh
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

1. **Import tax is a sweep artifact** (~0.8s/file, shared in a real parallel build): 314.6s across the
   391 modules here. It dominates the cheap files; the ranking of expensive files is accurate.
2. **Profiler sums over-count** (nested/cumulative) — per-category numbers are dominance signals,
   not an additive budget (a file's summed "simp took" can exceed its own total time).
3. **`lake env lean` exits 0 even on a stack overflow** — the script records exit codes; this run had
   **0 nonzero exits** across all 391 modules.
4. **The nine DivRem soundness conjuncts are included** and measured in isolation this run (each
   277–307s; the slowest single files in the library). They are *not* run in parallel here, so these
   are clean per-file costs rather than contention-inflated build-log wall times.

## Headline numbers

- **391 modules, 3964.6s total** (sequential, isolated). Mean 10.14s, **median 1.84s**, p90 5.98s,
  p95 25.31s, **max 306.65s**.
- **307/391 modules (79%) elaborate in <3s** (≈ the import floor).
- The eight DivRem div/rem soundness conjuncts alone are **2334.6s (59% of the total)**.

### Time by subsystem

| Subsystem | Time | Files |
| --- | ---: | ---: |
| `Proofs/` (of which: 8 DivRem conjuncts 2334.6s, Reader 68.3s, Tail 123.6s) | 3376.4s | 147 |
| `Proofs/` excluding those ten DivRem files | 849.9s | 137 |
| `Native/` | 190.6s | 66 |
| `Extracted/` | 165.9s | 77 |
| `Faithful/` | 114.9s | 50 |
| `Soundness/` | 44.9s | 27 |
| `Model/` | 42.6s | 11 |
| `FormalModel/` | 12.6s | 6 |
| `Math/` | 11.1s | 6 |

### DivRem soundness conjuncts (isolated)

Divw 306.7s · Remw 305.4s · Div 298.5s · Rem 297.8s · Divuw 286.5s · Remuw 284.8s · Divu 278.3s ·
Remu 276.8s — mean **291.8s** across the eight — plus **Reader 68.3s** and the shared
**`Tail.lean` 123.6s** (proved once). Each conjunct now proves only its chip-specific `Spec`; the
~265-line `Operations.Requirements` tail is delegated to `requirements_holds` in `Soundness/Tail.lean`
and paid **once** instead of inline in all nine files.

## Top offenders

| # | Time | Module | Note |
| ---: | ---: | --- | --- |
| 1 | 306.7s | `Proofs.Chips.DivRemChip.Soundness.Divw` | conjunct `Spec` proof; Mul product-glue `simpa`s + `instantiate metavars` |
| 2 | 305.4s | `Proofs.Chips.DivRemChip.Soundness.Remw` | " |
| 3 | 298.5s | `Proofs.Chips.DivRemChip.Soundness.Div` | " |
| 4 | 297.8s | `Proofs.Chips.DivRemChip.Soundness.Rem` | " |
| 5 | 286.5s | `Proofs.Chips.DivRemChip.Soundness.Divuw` | " |
| 6 | 284.8s | `Proofs.Chips.DivRemChip.Soundness.Remuw` | " |
| 7 | 278.3s | `Proofs.Chips.DivRemChip.Soundness.Divu` | " |
| 8 | 276.8s | `Proofs.Chips.DivRemChip.Soundness.Remu` | " |
| 9 | 123.6s | `Proofs.Chips.DivRemChip.Soundness.Tail` | **the shared tail, now paid once** (`requirements_holds`). `instantiate metavars` 61.2s + the two big `obtain`s + `rewriteSeq` — term-intrinsic |
| 10 | 100.2s | `Proofs.Chips.DivRemChip.Completeness.Driver` | the DivRem completeness driver (sub-op col folding) |
| 11 | 68.3s | `Proofs.Chips.DivRemChip.Soundness.Reader` | the reader conjunct |
| 12 | 50.7s | `Proofs.Chips.ShiftRightChip.Soundness.Sra` | conjunct proof body |
| 13 | 46.9s | `Proofs.Chips.ShiftRightChip.Soundness.Sraw` | " |
| 14 | 46.5s | `Proofs.Chips.ShiftRightChip.Soundness.Srl` | " |
| 15 | 44.5s | `Proofs.Chips.ShiftRightChip.Soundness.Srlw` | " |
| 16 | 39.0s | `Proofs.Chips.DivRemChip.Defs` | instance-field simps + kernel type-checking |
| 17 | 29.0s | `Proofs.Chips.ShiftLeftChip.Soundness.Sll` | conjunct proof body |
| 18 | 28.3s | `Proofs.Chips.ShiftRightChip.Formal` | |
| 19 | 27.1s | `Proofs.Chips.ShiftLeftChip.Soundness.Sllw` | conjunct proof body |
| 20 | 26.6s | `Native.Operations.MulOperation.RawSpec` | |
| 21 | 25.3s | `Proofs.Operations.MulOperation.Formal` | |
| 22 | 19.8s | `Extracted.DivRemChip` | generated |
| — | 13.9s | `Model.SailWrap` | mathlib-style simp/`grind` — not Clean-related |
| — | 12.0s | `Model.Register` | 62 `fin_cases <;> trivial` register lemmas — not Clean-related |

### Project-wide hot tactic categories (summed across all 391 logs, >50ms entries)

`simpa` 1349.5s (36 calls) · `instantiate metavars` 718.1s · `simp` 374.2s (821 calls) · `import`
314.6s (sweep artifact) · `obtain` 275.0s · `rewriteSeq` 170.4s · type-checking 132.1s · `nlinarith`
interpretation 64.7s.

The dominant category, `simpa`, is **99.97% concentrated in the eight div/rem conjuncts** (1349.1s of
1349.5s) — the Mul product-glue `simpa`s establishing `r_k = product[2k] + product[2k+1]·256` against
the 16-element witnessed product vectors. `instantiate metavars` (70% in DivRem soundness), `obtain`
(88%), and `rewriteSeq` (88%) are likewise concentrated there; `nlinarith` interpretation sits almost
entirely in the two Shift `Core` lemma farms. `simp` is the only broadly-spread category (821 calls,
~0.4s/file). **No broad attribute/macro/instance lever remains** — the remaining cost is term-intrinsic
in the DivRem/Shift/Mul heavies, not a project-wide pattern.

## Where to optimize next (by leverage)

1. **The eight DivRem soundness conjuncts (277–307s each, 2334.6s combined) + `Tail.lean` (123.6s).**
   The cost is the Mul product-glue `simpa`s + `instantiate metavars` — term-intrinsic (swapping the
   heavy `circuit_norm` simp set for the minimal one builds green with *zero* speedup). Reducing it
   needs restructuring how the Mul product columns are reduced. Largest effort, largest prize. *Open.*
2. **`Proofs.Chips.DivRemChip.Completeness.Driver` (100.2s)** — the sub-op col-folding driver; same
   heavy-term family. *Open.*
3. **ShiftRight/Left conjunct bodies (~27–51s each)** — same family; the shared
   `cpuA/msb1A/msb2A/msb3A/aluA` block (byte-identical across Srl/Sra/Srlw/Sraw) is a tail-dedup
   candidate mirroring this PR's DivRem dedup, a smaller prize. *Open.*
4. **maxHeartbeats ratcheting** — mechanical `#count_heartbeats` sweep to tighten the now-loose
   ceilings on the heavies; restores regression-alarm value (not a speedup). *Open.*
5. **`Model.SailWrap` / `Model.Register` (~26s combined)** — mathlib-style simp/`fin_cases` proofs,
   independent of Clean; editing `Model/` triggers a full rebuild, so low priority. *Open.*

## Verification of this run

- Coverage: 391 modules swept, **0 nonzero exits** (no silent stack overflow).
- Build gate: `lake build SP1Clean` green (**3676 jobs**), the **single** remaining `sorry`
  (`Soundness/SP1GatedVm.lean:220`), 0 errors, 0 new warnings, 0 `info:` notes.
- Axiom audit: `DivRemChip.requirements_holds` (the dedup'd tail) is
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
