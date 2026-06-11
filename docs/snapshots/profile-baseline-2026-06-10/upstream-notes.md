# Upstream reports drafted from the 2026-06-10 perf investigation

Evidence base: `findings.md` + `scratch/Probe*.lean` in this repo at the measurement commit.

## 1. leanprover/lean4 — polymorphic-range `get_elem_tactic_extensible` rule is O(context) per `v[i]`

**What:** In v4.28, the rule lives in core at `src/lean/Init/Data/Range/Polymorphic/GetElemTactic.lean`
(tried first, since macro_rules run in reverse registration order). It executes nine
`try rw [Std.R??.mem_iff] at *` passes, one `try dsimp +zetaDelta only [Vector.size] at *`, a
slice-size `simp only`, and then `omega` (which also preprocesses the whole context) — before any
context-blind closer sees a goal like `1 < 4`. Ready-to-file issue text: `docs/upstream/lean4-getelem-issue.md`.

**Impact measured:** inside a proof context with ~40 hypotheses carrying large terms (a zk-circuit
soundness proof), each `v[i]` elaboration costs ~0.34s; `have`-dense proofs pay ~0.8s per `have`.
Eight one-line `have`s: 175,413 heartbeats. With a `decide`-first extensible rule registered after
Std's: 3,000 heartbeats for the same eight (50×). Literal bounds close in ~26 HB; non-literal fall
through in ~300 HB.

**Suggestion:** try context-blind closers (`decide` for decidable literal bounds) before the `at *`
slice machinery, or scope the slice rewrites to the goal (`rw [...]` not `rw [...] at *`) until a
slice term is actually present in the goal.

**Workaround shipped here:** `SP1Clean/Foundations/GetElemFastPath.lean` (one `macro_rules` line).

## 2. Verified-zkEVM/clean — `ElaboratedCircuit.localLength_eq` rfl-default scales badly with `main`

**What:** the field default `localLength_eq := by intros; rfl` whnf-unfolds the entire `main` bind
chain. On a 17-operation `main` (SP1's ALUTypeReader): 333,951 heartbeats (~15.5s). The identical goal
closes in 3,052 heartbeats via `simp +arith [circuit_norm, main, <subcircuit circuits>]` (109×).
Every chip with a non-trivial `main` that leaves the field defaulted silently pays this at instance
elaboration, and it is invisible in the source (no tactic text to blame).

**Also:** the `channelsLawful` default tactic fails outright on channel-heavy mains (it does not
unfold `main`, and `try dsimp only [main]` does not fire when `main` is not a current-namespace
member at the instance site — e.g. probe error "could not synthesize default value for field
'channelsLawful'"), forcing hand-written full-`simp` workarounds downstream.

**Suggestions:** (a) document the simp-route override for `localLength_eq` (or change the default to
`by intros; first | rfl-with-budget | simp ...` semantics if expressible); (b) have the
`channelsLawful` default resolve/unfold the actual `main` argument rather than the name `main`.

**Mitigation shipped here:** explicit `localLength_eq := by intros; simp +arith [...]` on the two
affected reader instances; audit other defaulted instances as their mains grow.

## 3. Measured non-issues (do not upstream)

- `circuit_proof_start` / `provable_struct_simp`: 6k–32k HB on medium chips, 320k HB on the largest
  `main` in this repo (~90s) — real but secondary; the ~16-pass structure was not the bottleneck.
- The bind-chain `operations`-normalization (giant-goal hypothesis): the per-proof cost is the start
  cost above; the per-chip "normalize once" lemma (main_ops_eq) would save only ~13 min across
  DivRem's nine conjunct files (~4%) — parked in `scratch/design-main-ops-eq-divrem.md`.
