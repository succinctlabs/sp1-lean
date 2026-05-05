---
name: Polymorphic _poly proof patterns and gotchas (from Track A)
description: Non-obvious tactical patterns and workarounds discovered while writing _poly companions for ZMod p in SP1Operations
type: feedback
originSessionId: f9ab5b6f-d305-43ed-a962-8c272d98a1d1
---
Five tactical patterns and workarounds learned from Track A that recur
across `_poly` companion proofs over `ZMod p`. Future sessions writing
or migrating `_poly` proofs (especially Track B chip migration) should
expect to reach for these.

**1. `simp_all` strips Fact instances and local helpers — re-derive after.**

**Why:** When you `simp_all` to normalize a chunk of constraint structure,
local `have h := ...` bindings and synthesized `[Fact (...)]` instances may
disappear from the post-`simp_all` context. The CLAUDE.md warning about
"leaky simp_all" applies here too.

**How to apply:** If a downstream tactic needs `(N : ZMod p).val = N` or a
`Fact (1 < p)` instance, declare it AFTER the `simp_all`, not before. Use
`ZMod.val_natCast_of_lt (show (N : ℕ) < p by omega)` (which only needs
`hp_lt : 131072 < p` from `Fact (2^17 < p)`) rather than the
`val_*_zmod_p` simp family (which needs the original `Fact` instance).

**2. `intro cstrs; have cstrs := cstrs` shadowing keeps cstrs available
after `rcases cstrs`.**

**Why:** `rcases h with ⟨...⟩` consumes `h`. If you need to use `h` again
later (e.g. to apply a different lemma to the original constraint
list), shadow it with `have h := h` first — `rcases h` then destructures
the shadowed copy, and the original (with the same name) remains
accessible by name resolution.

**How to apply:** This is the canonical pattern in `LtOperationSigned.spec.branch`
and the polymorphic `branch_poly` companion. Use it whenever the proof
needs to invoke spec.unsigned_poly/spec.signed_poly AFTER destructuring
the constraint conjunction for case analysis.

**3. Anonymous constructor struct projections need explicit simp normalization.**

**Why:** `{ field := #v[a, b, c, d], ... }.field[2]` doesn't reduce to `c`
without simp. After `rw [iff_lemma]` the iff RHS often has anonymous
constructors of cols structs whose `[i]` accesses must be unfolded.

**How to apply:** Add this after destructuring an iff_poly:
```
simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
  List.getElem_cons_succ] at h_f0 h_f1 h_f2 h_f3 lt_d3 lt_d2 lt_d1 lt_d0
                                h_cmp_b h_cmp_d h_neq
```

**4. Field-level `<` doesn't auto-reduce to `.val <`.**

**Why:** `ZMod.instLT` makes `(x : ZMod p) < y` literally `x.val < y.val`,
but Lean's unifier doesn't unfold this for tactic lemmas that expect
explicit `.val < ...`.

**How to apply:** Convert manually:
```
have hr0' : cols.bitwise_operation.result[0].val < 256 := by
  have h : cols.bitwise_operation.result[0].val < (256 : ZMod p).val := hr0
  rw [h256_val] at h; exact h
```
where `h256_val : (256 : ZMod p).val = 256` (re-derived per pattern 1
if simp_all has fired).

**5. `ByteOpcode.ofNat (ZMod.val k)` needs `(k : ZMod p).val = k` to reduce.**

**Why:** When chip/op constraints use opcodes like 1 (OR) or 2 (XOR) as
`ZMod p` literals, the constraint structure becomes
`match ByteOpcode.ofNat (ZMod.val 1) with ...`. simp won't pick the OR
arm without first reducing `(1 : ZMod p).val = 1` (via `ZMod.val_one p`,
needs `[Fact (1 < p)]`) or `(2 : ZMod p).val = 2` (via
`val_2_zmod_p` or `ZMod.val_natCast_of_lt`).

**How to apply:** For non-zero opcode constraints, derive the relevant
`(k : ZMod p).val = k` helper and add it explicitly to the simp set on
the `simp [BitwiseOperation.constraints, ...]` (or analogous) call. The
0 (AND) opcode case works automatically via `ZMod.val_zero`.

These five patterns together describe ~80% of the "why doesn't this
close mechanically" friction in writing `_poly` companions. Anticipating
them upfront cuts iteration time substantially.
