> **Point-in-time snapshot — regenerate before relying on it.**

# Compile-time profile — SP1Clean

Per-module wall-clock elaboration profile, with per-tactic attribution for the worst offenders and
the common threads behind them. Measured **2026-06-19** (Lean v4.28.0, 24-core host, warm olean
cache, branch `dtumad/perf-improvement` at the `main`-merge), **after** the pillar refactor
(2026-06-18) and the DivRemChip soundness-tail dedup (`f0e6f82`). This supersedes the 2026-06-10
snapshot, whose absolute seconds were pre-refactor and contention-inflated; the 2026-06-10 *diagnosis*
(the get_elem fast path, the linter tax, `localLength_eq`, and the "kill-list of myths" below) still
holds and is retained. The pre-fix baseline + drafted upstream reports live in
`docs/snapshots/profile-baseline-2026-06-10/`.

## How to re-run

```sh
# whole library; the 9 DivRem soundness conjuncts are 18–33 min EACH in isolation — exclude them and
# take their cost from a `lake build` log instead. The regex keeps Tail.lean (the shared tail, worth
# measuring) but drops the 9 heavy conjuncts.
SKIP_BUILD=1 EXCLUDE_RE='Soundness/(Div|Divu|Divuw|Divw|Reader|Rem|Remu|Remuw|Remw)\.lean$' \
  scripts/profile_compile.sh
scripts/profile_compile.sh                          # warm-builds first, then sweeps (no SKIP_BUILD)
SKIP_BUILD=1 scripts/profile_compile.sh Operations/ # cache warm, scope to one subdir
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

1. **Import tax is a sweep artifact** (~0.5s/file, shared in a real parallel build): 197s across the
   382 modules here. It dominates the cheap files; the ranking of expensive files is accurate.
2. **Profiler sums over-count** (nested/cumulative) — per-category numbers are dominance signals,
   not an additive budget (e.g. a file's summed "simp took" can exceed its own total time).
3. **`lake env lean` exits 0 even on a stack overflow** — the script records exit codes; this run had
   **0 nonzero exits** across all 382 modules.
4. **The nine `Chips/DivRemChip/Soundness/{Div,Divu,Divuw,Divw,Reader,Rem,Remu,Remuw,Remw}.lean`
   conjuncts are excluded** (18–33 min each in isolation); their costs come from the warm `lake build`
   log instead — see below. `Tail.lean` is **kept** in the sweep.

## Headline numbers (2026-06-19 sweep)

- **382 modules, 1780.5s total** (sequential, isolated; excludes the 9 DivRem conjuncts).
  Mean 4.66s, **median 2.02s**, p90 5.47s, p95 15.83s, **max 147.6s**.
- **296/382 modules (77%) elaborate in <3s** (≈ import floor).
- Generated/auto-gen modules (`Extracted/` + witness/trace vectors): **229.8s across 87 files.**

### Time by subsystem

| Subsystem | Time | Files |
| --- | ---: | ---: |
| `Proofs/` (excl. DivRem conjuncts) | 1131.4s | 138 |
| `Native/` | 210.8s | 66 |
| `Extracted/` | 186.7s | 77 |
| `Faithful/` | 127.4s | 50 |
| `Soundness/` | 50.1s | 27 |
| `Model/` | 46.7s | 11 |
| `FormalModel/` | 13.9s | 6 |
| `Math/` | 12.1s | 6 |

### DivRem soundness conjuncts (from the warm `lake build` log, 9-way parallel — contention-inflated)

Divw 357s, Remw 357s, Rem 354s, Div 348s, Divuw 334s, Remuw 334s, Divu 324s, Remu 322s, Reader 75s
— plus the shared **`Tail.lean` 147.6s (isolated, built once)**. **The `f0e6f82` tail dedup roughly
halved each conjunct**: the 2026-06-10 snapshot logged the same files at 720–1997s each (at ≤5-way
parallel, i.e. *less* contention), because each then re-elaborated the byte-identical 265-line
`Operations.Requirements` tail at 128M heartbeats. They now delegate to `requirements_holds` in
`Soundness/Tail.lean`, which is paid **once**. The conjuncts remain the library's dominant cost, but
the per-file body is now the chip-specific spec proof, not the tail.

## Top offenders (2026-06-19)

| # | Time | Module | Note |
| ---: | ---: | --- | --- |
| 1 | 147.6s | `Chips.DivRemChip.Soundness.Tail` | **the shared tail, now paid once** (was inline ×9). `instantiate metavars` 79.7s + the two big `obtain`s ~25s + `rewriteSeq` 14.6s — term-intrinsic |
| 2 | 118.0s | `Chips.DivRemChip.Completeness.Driver` | the DivRem completeness driver (sub-op col folding) |
| 3 | 61.5s | `Chips.ShiftRightChip.Soundness.Sra` | conjunct proof body |
| 4 | 56.0s | `Chips.ShiftRightChip.Soundness.Sraw` | conjunct proof body |
| 5 | 54.9s | `Chips.ShiftRightChip.Soundness.Srl` | conjunct proof body |
| 6 | 52.6s | `Chips.ShiftRightChip.Soundness.Srlw` | conjunct proof body |
| 7 | 43.3s | `Chips.DivRemChip.Defs` | instance-field simps + kernel type-checking. **Was reported "118s" in 2026-06-10 — that was contention; isolated it is ~43s** |
| 8 | 35.6s | `Chips.ShiftRightChip.Formal` | |
| 9 | 34.6s | `Chips.ShiftLeftChip.Soundness.Sll` | conjunct proof body |
| 10 | 32.7s | `Chips.ShiftLeftChip.Soundness.Sllw` | conjunct proof body |
| 11 | 29.9s | `Operations.MulOperation.Formal` | |
| 12 | 29.6s | `Operations.MulOperation.RawSpec` | |
| 13 | 23.4s | `Extracted.DivRemChip` | generated (was 462s pre-2026-06-10) |
| 14 | 22.9s | `Chips.ShiftLeftChip.Formal` | |
| 15 | 21.9s | `Chips.ShiftRightChip.Defs` | |
| 16 | 20.6s | `Chips.ShiftRightChip.Core` | arithmetic lemma farm |
| 17 | 19.7s | `Operations.LtOperationUnsigned.RawSpec` | |
| 18 | 17.1s | `TraceGenTests.DivRemChipTraceVectors` | `native_decide` anchor data |
| 19 | 17.0s | `Extracted.WitnessVectors.MulOperation` | `native_decide` anchor data |
| 20 | 16.0s | `Chips.ShiftLeftChip.Core` | |
| — | 14.7s | `Model.SailWrap` | 232 mathlib-style simp calls — not Clean-related |
| — | 13.3s | `Model.Register` | 94 `@[simp]` register lemmas, proved by `fin_cases <;> trivial` — not Clean-related |

### Project-wide hot tactic categories (summed across all 382 logs, >50ms entries)

`simp` 412.4s (789 calls) · type-checking 204.2s · import 197.0s (sweep artifact) · `rewriteSeq`
170.1s · `share common exprs` 88.2s · `nlinarith` interpretation 55.4s · `instantiate metavars` 52.1s.
**`simp` is the single largest category, but ~48% of it is concentrated in the top-10 heavy files**
(SailWrap, DivRem, Shifts) and the rest is spread thin (~0.4s/file) — there is no pathological broad
pattern like the pre-2026-06-10 `v[i]` tax. `instantiate metavars` (79.7s in Tail alone) and
`nlinarith` interpretation are likewise concentrated in the DivRem/Shift/Mul heavies. **The remaining
cost is term-intrinsic in a handful of files, not a broad lever.**

## What the 2026-06-10 diagnosis established (kill-list of myths — still valid)

Full evidence: `profile-baseline-2026-06-10/findings.md`. In brief:

- **`circuit_proof_start` / bind-chain normalization is NOT the bottleneck** — 6k–32k heartbeats on
  medium chips, ~320k (~90s) even on DivRem's `main`, the repo's biggest. The once-per-chip
  `main_ops_eq` lemma would save ~4% — parked.
- **The dominant medium-chip cost was `v[i]` elaboration**, fixed by the `decide` fast path
  (`Math/GetElemFastPath.lean`, one `macro_rules` line — registered above Std's slice rule). This
  single fix halved isolated elaboration of the swept set in the 2026-06-10 batch.
- **`ElaboratedCircuit` field defaults can silently cost seconds**: `localLength_eq`'s `rfl` default
  whnf-unfolds `main` (~15.5s on a 17-op main); `channelsLawful`'s default fails on channel-heavy
  mains. Hand-write the simp-route `localLength_eq` on every new chip with a non-trivial `main`.
- The "linter tax" / "Extracted monolithic terms" threads are **resolved** (the latter was the `v[i]`
  tax in disguise; the former is fixed by `set_option linter.all false` on the 76 generated modules).

## Perf-lever investigation (2026-06-19) — broad levers are exhausted

The 2026-06-19 sweep was mined for a new *broad* lever in the style of the `get_elem` fast path
(an attribute/macro/instance tweak that helps project-wide). **None was found** — the evidence:

- **No shared hot tactic.** `simp`/`rewriteSeq`/`obtain`/`instantiate metavars` are all either
  concentrated in the DivRem/Shift/Mul heavies or spread thin with no pathological pattern (above).
- **No broad instance-resolution cost.** Typeclass inference is negligible project-wide (only
  "typeclass inference of `Nonempty`" appears, 26× small); `instantiate metavars` is concentrated, not
  broad. There are no manual instance-priority declarations to tune, and none are warranted.
- **`localLength_eq` is already harvested.** All heavy chips (DivRem/Mul/Branch/Shifts/Loads/Stores)
  and both ALU readers carry an explicit simp-route `localLength_eq`; the chips that still default it
  (Add/Sub/Lt/Bitwise/Jal/Jalr/UType…) have small mains (2–5 ops) where the `rfl` default is cheap
  (all elaborate in 2–5s). No new candidate.
- **The 94 `Model/Register.lean` register `@[simp]` lemmas impose zero global tax.** They are
  discriminated by the `reg_idx_to_Register` head symbol and consumed by only 2 files
  (`SailWrap`, `SailMemory`); the other 380 modules never enter them into a rewrite attempt. Measured
  directly: a register-free `simp` costs **205 heartbeats with the lemmas in the default set and 205
  with them removed** (`attribute [-simp]`) — identical. Moving them to a scoped set would yield no
  project-wide gain and would require editing a foundational `Model/` module (≈ full rebuild) to
  validate. **Not pursued.** (Register.lean's own 13.3s is its 62 `fin_cases <;> trivial` lemma
  proofs — a single-file cost, not a project lever.)
- **maxHeartbeats ceilings are loose but right-sizing is alarm-hygiene, not speed.** Lowering a
  ceiling does not make a proof compile faster — it only tightens the regression alarm. The 9 DivRem
  conjuncts + `Tail.lean` sit at 128M HB; measuring their true consumption needs the multi-hour
  rebuild, for alarm-only value. Deferred to the mechanical `#count_heartbeats` sweep (target #4).

**Conclusion:** the three shipped optimizations (get_elem fast path, linter-off on generated,
`localLength_eq` on big-main readers) captured the broad wins. Further compile-time reduction requires
**per-proof restructuring of the concentrated heavies** (Tail/Driver/Shift conjuncts) — a larger,
term-by-term effort, not an easy attribute/priority lever.

## Where to optimize next (by leverage)

1. **`Chips.DivRemChip.Soundness.Tail` (147.6s) + the conjunct bodies (~322–357s contended each).**
   The cost is `instantiate metavars` + the Mul product-glue `simpa`s establishing
   `r_k = product[2k] + product[2k+1]·256` against the 16-element witnessed product vectors — term
   intrinsic (swapping the heavy `circuit_norm` simp set for the minimal one built green with *zero*
   speedup). Reducing it needs restructuring how the Mul product columns are reduced. Large effort,
   largest prize. *Open.*
2. **`Chips.DivRemChip.Completeness.Driver` (118s)** — the sub-op col-folding driver; same heavy-term
   family. *Open.*
3. **ShiftRight/Left conjunct bodies (~33–61s each)** — same family as (1); the shared
   `cpuA/msb1A/msb2A/msb3A/aluA` block (byte-identical 236 lines across Srl/Sra/Srlw/Sraw) is a
   tail-dedup candidate mirroring `f0e6f82`, a smaller prize than DivRem's. *Open.*
4. **maxHeartbeats ratcheting** — mechanical `#count_heartbeats` sweep to tighten the now-loose
   ceilings; restores regression-alarm value (not a speedup). *Open.*
5. **Upstream filings** (`profile-baseline-2026-06-10/upstream-notes.md`): lean4/Std slice-rule `at *`
   report; Clean `localLength_eq`/`channelsLawful` default reports. *Drafted, not filed.*
6. **`Model.SailWrap` / `Model.Register` (~28s combined)** — mathlib-style simp/`fin_cases` proofs,
   independent of Clean; Register's 62 `fin_cases <;> trivial` could try `decide`, but editing
   `Model/` triggers a full rebuild. *Open, low priority.*

## Verification of this run

- Coverage: 382 modules swept, **0 nonzero exits**; the 9 DivRem conjuncts excluded by `EXCLUDE_RE`
  (costs from the warm build log), `Tail.lean` included.
- Build gate: `lake build SP1Clean` green (**3676 jobs**), the **single** remaining `sorry`
  (`Soundness/SP1GatedVm.lean:220`), 0 errors, 0 new warnings, 0 `info:` notes. (The 2026-06-10
  ShiftLeft/ShiftRight/Mul/DivRem `Formal` sorries have since been closed.)
- Axiom audit: `DivRemChip.SoundDiv.soundness` and `DivRemChip.requirements_holds` (the dedup'd tail)
  both `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
