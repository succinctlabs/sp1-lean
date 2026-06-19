# [Ready-to-file lean4 issue] `get_elem_tactic`: polymorphic-range extensible rule costs O(context) per `xs[i]`, ~0.34s under large proof contexts

*Drafted 2026-06-10 from measurements in `sp1-clean-native` (Lean v4.28.0). Maintainer review
pending before filing at leanprover/lean4.*

## Summary

`Init/Data/Range/Polymorphic/GetElemTactic.lean` registers the `get_elem_tactic_extensible`
rule that is tried **first** (macro_rules run in reverse registration order). Before any
context-blind closer sees the bound goal, it executes:

- nine `try rw [Std.R??.mem_iff] at *` passes,
- `try dsimp +zetaDelta only [Vector.size] at *`,
- a `try simp only [Array.size_mkSlice_*, …]`,
- then `omega` (whose preprocessing also walks every hypothesis).

Each `at *` pass traverses the entire local context. In contexts whose hypotheses carry large
terms — for us, zk-circuit soundness proofs with ~40 hypotheses holding whole-circuit
expressions — a bound goal as trivial as `1 < 4` costs **~0.34s**, paid at *every* `xs[i]`
elaboration. Proofs that state intermediate `have`s over indexed vectors pay ~0.7–0.9s per
`have` in pure index-bound elaboration.

## Measurements (Lean v4.28.0, mid-range linux desktop)

- One representative proof block (8 one-line `have`s, each with two `v[i]` occurrences, inside a
  large soundness context): **175,413 heartbeats**.
- Same block after registering a `decide`-first extensible rule (tried before the range rule,
  still after `done`/`assumption`): **~3,000 heartbeats** for the same 8 haves (~50×).
- Literal bounds close via `decide` in ~26 heartbeats; non-literal bounds fail through in ~300.
- Library-wide effect of the workaround in our project (~260-module formal-verification library,
  isolated per-module elaboration): **3422s → 1689s (−50.7%)**, dominated by this fix. Generated
  files with dense `#v[…][k]` projections improved up to −93% (e.g. one 462s module → 31s).

## Workaround we ship

```lean
-- registered after core's rules, so tried first among extensible rules
macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| decide)
```

`done`/`assumption` still run before the extensible rules, preserving the
proof-term-is-the-hypothesis behavior unification relies on (#6999 note in `get_elem_tactic`).

## Suggested fix (maintainers' choice)

1. Try a context-blind closer first inside the range rule, e.g.
   `first | decide | (existing slice machinery) | done` — literal bounds (the overwhelmingly
   common case) never touch the context; or
2. guard the slice machinery on the goal actually mentioning `Std.R??`/slice types before
   running the `at *` rewrites; or
3. scope the `rw`s to the goal and only fall back to `at *` when the goal mentions slice terms.

Happy to provide the full probe files and traces.
