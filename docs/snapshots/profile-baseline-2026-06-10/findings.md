# Phase-1 diagnosis findings — 2026-06-10 (branch full-clean-dsl-implementation, post-e076768)

Baseline: scoped isolated-elaboration sweep, 259 modules, 0 nonzero exits (`summary-all.tsv`).
Probes: `scratch/Probe*.lean` (`#count_heartbeats` A/B), `trace.profiler` trees, `-Dprofiler` logs.

## The measured cost structure of a medium chip Formal file (StoreByteChip, 25.3s)

| Component | Cost | Evidence |
| --- | --- | --- |
| **Proof bodies — `have`-steps at ~0.8s each** | ~19s + ~20s (sound/complete, async-overlapped) | trace tree: every `have` 0.55–1.6s |
| → of which: `v[i]` index-bound elaboration | **~0.34s per `[i]` occurrence** ≈ half the body | `get_elem_tactic_extensible` hits Std's slice macro_rule: nine `try rw [Std.R??.mem_iff] at *` + `dsimp … at *` + slice-simp = ~11 full-context traversals per index, under 40+ giant hypotheses |
| circuit_proof_start | 2.4s/proof (32k HB) | probe: statement 70 HB / core 77 HB / full 32k HB |
| Linter interpretation (TacticAnalysis et al.) | ~1.6s/file | profiler log buckets |
| import | ~1s/file | profiler |

**Fix validated:** `macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| decide)` registered
after Std's rules (tried first; `first`-falls-through on non-literal bounds: 334 HB; literal: 26 HB; no
extension conflicts in SP1Clean/Clean; proof terms axiom-free). A/B on the 8 StoreByte bridges:
**175,413 → 34,745 HB** (~50× on the haves; ~32k of the "after" is circuit_proof_start itself).

## Killed hypotheses (measured, not assumed)

1. **circuit_proof_start / bind-chain normalization is NOT the medium-chip bottleneck**: 6k–32k HB
   (≈1–2.4s) on all 7 pilots — ~10% of file cost, well under even the default heartbeat budget.
2. **main_ops_eq for DivRem is NOT a big win**: full start on the repo's biggest `main` = 320k HB
   (~90s wall). 9 conjunct files × 90s ≈ 13 min of the chip's ~4.3 CPU-hours. The 128M-HB budgets
   are ~95% proof body (omega/bitvec/carry). Parked: `scratch/design-main-ops-eq-divrem.md`.
3. **Eval-bridge `rw`/`simp` content is cheap** — the cost was the `[i]` elaborations in the have
   *types*; the Track-2 shared-lemma rewrite is mostly superseded by the get_elem fast path.

## Second-tier findings

- **`localLength_eq` default `by intros; rfl` whnf-unfolds the whole `main`**: 333,951 HB (15.5s) on
  ALUTypeReader vs **3,052 HB** for the same goal via `simp +arith [circuit_norm, main, RegisterAccessCols.circuit]`
  (109×). Same 15.6s `eqRefl` visible in ALUTypeReaderImmutable's log. `output_eq` (85 HB) and
  `subcircuitsConsistent` (6.6k HB) defaults are fine. Clean's default `channelsLawful` tactic
  genuinely fails on ALUTypeReader's main (probe: "could not synthesize default value") — the
  hand-written full-`simp` there is a workaround, not a smell.
- **Generated files: 1178.8s / 77 modules — ~34% of the sweep.** `Extracted.DivRemChip` alone 461s
  (the #1 module overall; monolithic-term elaboration, thread E). Linter share is the cheap part
  (~1.6s/file); the term elaboration needs its own investigation.
- `Chips.DivRemChip.Defs` 152s: simp 24s+19s+13s + **kernel type-checking 18s+14s+7.6s** on the
  instance field proofs — needs a dedicated look (possibly `whnf`-heavy field goals + big proof terms).
- Control files (no Clean): `Foundations.SailWrap` 26.8s (232 simp calls), `Foundations.Register` 23s —
  generic mathlib-tactic cost, separate fix family, out of current scope.
- DivRem conjuncts (from the parallel build log, not re-measured): Div 2354s, Divu 2220s, Remu 2127s,
  Rem 1901s, Remw 1804s, Divw 1789s, Divuw 1474s. Their bodies are `have`-dense — the get_elem fast
  path should cut them materially (quantified by the post-fix rebuild).

## Fix plan (re-ranked by measured leverage)

1. **get_elem decide fast-path** — new `Foundations/GetElemFastPath.lean`, imported by `Foundations/Word.lean`
   (library-wide; costs one full rebuild, which doubles as the fix's whole-library measurement).
2. **Linter-off on 77 generated files** (generator templates already updated; mirror insertion script ready).
3. **localLength_eq simp-route** on ALUTypeReader + ALUTypeReaderImmutable (audit other defaulted
   instances with big mains via the sweep table).
4. maxHeartbeats right-sizing on touched files after measurement.
5. Upstream reports with this evidence: (a) Lean/Std — the slice `get_elem_tactic_extensible` rule's
   `at *` passes are O(context) per `v[i]`; (b) Clean — `localLength_eq` rfl-default scales badly with
   `main` size; default `channelsLawful` tactic fails on channel-heavy mains.
6. Deferred/parked: main_ops_eq (small win), circuit_proof_start trims (small), Extracted.DivRemChip
   term elaboration (separate investigation), SailWrap/Register mathlib-style proofs.
