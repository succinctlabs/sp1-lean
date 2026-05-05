---
name: grind ring init fails on free Fin KB variables
description: In Lean 4.29, `grind` fails with "error while initializing grind ring operators" on goals containing a free `Fin KB` variable; substitute the variable before grind.
type: feedback
originSessionId: c0a287fd-0303-4b1e-9298-b1dd8412559d
---
When `grind` on a goal over `Fin KB` (KoalaBear field) reports:

```
error while initializing `grind ring` operators:
instance for `NatCast.natCast`
  KoalaBear.instFieldFinOfNatNat_...toNatCast
is not definitionally equal to the expected one
  Lean.Grind.Semiring.natCast
when only reducible definitions and instances are reduced
```

the cause is a free `Fin KB` variable in the goal (e.g. a generic `is_real : Fin KB` with a `is_real = 1` hypothesis). Grind eagerly initializes its ring machinery on `Fin KB`, but the Field instance comes from `ZMod.instField KB` and its `NatCast` is not reducibly-definitionally-equal to `Lean.Grind.Semiring.natCast`.

**Why:** Identified while un-sorrying `IsZeroWordOperation.spec.gen` on branch `dtumad/milestone-3`, then applied to `U16MSBOperation.spec.gen`. Sibling `spec` lemmas (with `is_real = 1` baked into the `constraints` call) worked; the `.gen` siblings (with `is_real` free) hit ring init. Tactic dry-run via `lean_multi_attempt` confirmed the fix in each case.

**How to apply:** Prefer `by simp [constraints]; intros; subst_vars; grind` over `by simp [constraints]; grind` whenever the `.gen` form of a lemma keeps an `is_real : Fin KB` variable free but the **remaining** `Fin KB` terms are structure fields / indexed vector entries (not further arithmetic unknowns). Substituting the numeral `1` through the goal sidesteps `grind ring` entirely.

**Where this fix does NOT work:** lemmas whose goal retains many ring-arithmetic free `Fin KB` variables even after substituting `is_real = 1`. Example: `LtOperationUnsigned.cl_are_U16` (the `sorry --grind (splits := 16)` on line 39) — after subst, goal still has `b[i] * cols.u16_flags[j]` style terms, so `grind` still initializes ring and fails; `grind -ring` clears the init error but then grind can't close a residual subgoal without ring reasoning. That one needs either a proper `Lean.Grind.CommRing (Fin KB)` instance, or a hand-written proof avoiding generic ring lemmas.
