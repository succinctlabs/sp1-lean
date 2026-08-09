import Clean.Circuit.Basic

/-! # `v[i]` index-bound fast path

Every `v[i]` elaborates its bound side-goal (`i < n`) with `get_elem_tactic` =
`first | done | assumption | get_elem_tactic_extensible | fail`. In core Std (first
measured at Lean 4.28; verified still present at v4.32.2 in
`Init/Data/Range/Polymorphic/GetElemTactic.lean`), the range-support `macro_rules` for
`get_elem_tactic_extensible` (tried first — `macro_rules`
run in reverse registration order) opens with nine `try rw [Std.R??.mem_iff] at *` passes,
a `dsimp … at *`, and a slice `simp` — ~11 full-context traversals per index. Inside a chip
soundness proof (40+ hypotheses carrying whole-circuit terms) that is **~0.34s for `1 < 4`**,
and `have`-dense proofs pay it for every `[i]` in every `have` type (measured: the eight
StoreByteChip eval-bridge `have`s cost 175k heartbeats before this rule, 3k after — the
~0.8s-per-`have` body tax drops to noise).

The rule below registers *after* Std's (this module sits above them in the import graph), so
it is tried *first* among the extensible rules — but still after `done`/`assumption`, which
preserves the proof-term-is-the-hypothesis behavior unification relies on (Lean #6999 note).
`decide` is context-blind: literal bounds (`1 < 4`, the overwhelmingly common case here)
close by kernel `Nat.decLt` reduction in ~26 heartbeats with no extra axioms; non-literal
bounds fail in ~300 heartbeats and fall through to the standard rules. -/

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| decide)
