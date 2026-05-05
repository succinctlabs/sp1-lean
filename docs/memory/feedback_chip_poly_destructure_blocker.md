---
name: Chip-side _poly destructure blocked by Fin KB / ZMod KB defeq gap
description: Non-obvious blocker discovered in Track B SubChip pilot 2026-05-01 — `(constraints Main).allHold_poly (p := KB)` type-checks but cannot be destructured via simp/rw because chip auto-gen `+++` is at Fin KB while outer List.Forall is at ZMod KB
type: feedback
originSessionId: f8658ef2-8574-44e7-9fe4-e4237b326295
---
When piloting chip-side migration to `_poly` lemmas, the
`(constraints Main).allHold_poly (p := KB)` hypothesis ascription idiom
(verified at the type-checking level via `lean_run_code` 2026-04-28)
**fails at the destructure step** because of a syntactic-vs-definitional
type gap.

**Why:** The chip's `<Chip>/Constraints.lean` auto-gen returns
`SP1ConstraintList (Fin KB)`. Restating `correct_*`'s hypothesis to use
`allHold_poly (p := KB)` causes Lean to type-check via the `Fin KB =
ZMod KB` definitional equality. After `simp [constraints]`, the
hypothesis displays as `List.Forall toProp_poly (CS0 +++ CS1 +++ CS2
+++ [...])` — looks ready to destructure. Inspecting with
`pp.explicit true` reveals the underlying instance mismatch:

```
@List.Forall (SP1Constraint (ZMod KB)) toProp_poly
  (@HAppend.hAppend (List (SP1Constraint (Fin KB))) ... ...)
```

The outer `List.Forall` is at `SP1Constraint (ZMod KB)`; the inner
`HAppend` is at `List (SP1Constraint (Fin KB))`. `List.forall_append`
(simp lemma `List.Forall p (xs ++ ys) ↔ ...`) cannot match because
its `?xs +++ ?ys` pattern's `α` parameter unifies to `SP1Constraint
(Fin KB)` from the `HAppend` instance, while the surrounding
`List.Forall` has `α := SP1Constraint (ZMod KB)`. Definitionally
equal, but simp's pattern matcher only does defeq-modulo-reducibility
and doesn't bridge `Fin KB ↔ ZMod KB` at this parameter position.

**How to apply:** Don't pursue chip-side migration before chip-level
parametric emission lands (Track C1 — extend `update_constraints.py`'s
post-processor). The following workarounds were tried and ALL fail:

1. `simp [constraints, SP1ConstraintList.allHold_poly,
   List.forall_append, List.Forall]` — leaves `+++` un-distributed.
2. `unfold SP1ConstraintList.allHold_poly + unfold constraints + rw
   [List.forall_append]` — `rw` errors "Did not find an occurrence of
   the pattern `@List.Forall ?m ?p (?xs +++ ?ys)`".
3. `with_unfolding_all (simp [...])` — same.
4. `let xs : SP1ConstraintList (ZMod KB) := constraints Main; have
   cstrs2 : SP1ConstraintList.allHold_poly xs := cstrs` — re-elaborates
   the let binding but inner `+++` instance keeps `Fin KB` types.
5. `change List.Forall (SP1Constraint.toProp_poly (p := KB))
   (constraints Main) at cstrs` — succeeds, doesn't change underlying
   type propagation; subsequent simp still leaves `+++` un-distributed.
6. Manual `List.forall_append.mp` — `cstrs : List.Forall toProp_poly
   (constraints Main)` doesn't match `List.Forall ?m (?xs +++ ?ys)`
   pattern because `constraints` is `@[irreducible]`.

**Diagnostic recipe** (use this to confirm whether a chip is hitting
this blocker, before wasting time on tactics): in the proof, after
`simp [constraints, SP1ConstraintList.allHold_poly] at cstrs`, run
`set_option pp.explicit true in trace_state` and look at the explicit
form of cstrs. If you see `@List.Forall (SP1Constraint (ZMod ...)) ...
(@HAppend.hAppend (List (SP1Constraint (Fin ...))) ...)`, you've hit
this blocker. Stop and pivot to C1.

**Resolution path (now LANDED for SubChip 2026-05-01):** Track C1 in
`docs/FIELD_GENERIC.md` — extended `update_constraints.py` with a
`PARAMETRIC_CHIPS: Dict[str, Tuple[str, bool]]` dict (chip name →
universe + needs_coe_head). Per-chip opt-in (user directive: only
regenerate for chips actively being migrated). The
`apply_parametric_chip_post_process` helper applies the same
`(Fin KB) → F` substitutions as `apply_parametric_post_process`,
adding `{F : <universe>} [Field F] [CoeHead F ℕ]` to the chip's
`def constraints` line. After regen, `<Chip>/Constraints.lean` returns
`SP1ConstraintList F` parametric in `(F : Type) [Field F]`. The chip's
`SubChip.lean`-style file then takes `Main : Vector (ZMod p) N` over
`{p : ℕ} [Fact (Nat.Prime p)] [Fact (2^17 < p)]`, and `_poly` lemmas
apply naturally. Verified end-to-end: SubChip's `correct_sub`
elaborates clean, lake build 0 errors / 0 warnings, only standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).
