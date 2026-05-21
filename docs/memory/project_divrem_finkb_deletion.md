---
name: project-divrem-finkb-deletion
description: DivRem chip is now _poly-only (Fin KB versions deleted 2026-05-15)
metadata: 
  node_type: memory
  type: project
  originSessionId: f091c771-7a7a-4c83-bd73-49c89a5ad4a3
---

# DivRem Fin KB deletion sweep COMPLETE (2026-05-15)

7 commits dropping all Fin KB versions where a `_poly` companion exists.
Chip's exposed API is `_poly` only, matching the Mul precedent (kept the
`_poly` suffix; Add/Sub dropped it). Per-file top-down order so each
commit built clean.

Commits on `dtumad/final-aggregation` (after `091b675` / `e653978` closed
the last sorries):

1. `221fc0d` — DivRemChip.lean: 8 Fin KB `correct_<v>`, `correct_prologue_facts`, `sp1_op`, top-level Fin KB variable. Kept the 8 Sail-level `spec_<v>` defs (no field dependence, used by `correct_<v>_poly`).
2. `94606a1` — DivRem.lean: bare `div_rem` + `spec.div` + `spec.rem`.
3. `73bc786` — DivuRemu.lean: `divu_remu` + `spec.divu` + `spec.remu`. Also dropped a stale STUB docstring above `spec.divu_poly`.
4. `ef0b1c5` — DivwRemw.lean: `divw_remw` + `spec.divw` + `spec.remw`.
5. `109b646` — DivuwRemuw.lean: `divuw_remuw` + `spec.divuw` + `spec.remuw`.
6. `5b6871c` — Common.lean: 4 Fin KB sections (`field_arithmetic`, `opcodes`, `entailed_constraints`, `operands`) plus `div_mod_decomposition_w` + `sum_zero_abs`.
7. `fcd36a2` — Constraints.lean: `allHold_constraints_iff` + `allHold_constraints_alu_ops`. Autogen parametric `constraints` def untouched.

**Why:** First execution of the long-deferred Track C2 "Fin KB deletion
sweep" from the field-genericization effort. Now that all 8
`correct_*_poly` are sorryAx-free, the parallel Fin KB layer is dead
weight. User-confirmed nothing outside `SP1Chips/DivRem*` referenced any
deleted name (one inventory pass before starting, plus a final
`grep -rn "DivRem\." SP1Chips/ SP1Foundations/ SP1Operations/` returned
empty).

**How to apply:** This sweep is a template for the future ShiftLeft /
ShiftRight migrations and any other chip that ends up with both layers.
Order matters: delete top-down (chip → spec wrappers → bare cores →
helpers → iff lemma) so each commit's per-module build stays clean.

## Inventory gotchas (worth catching for the next sweep)

Pre-deletion inventory wrongly flagged three solo Fin KB lemmas as
unused — they're actually field-agnostic and used by `_poly` proofs:

- `tdiv_tmod_unique_full {b c q r : ℤ}` — pure ℤ. Used by `div_rem_poly`
  + `divw_remw_poly` (DivRem.lean:975, DivwRemw.lean:477, 1296).
- `tdiv_tmod_unique_full_nat {b c q r : ℕ}` — pure ℕ. Field-agnostic.
- `extractLsb_is_toInt {x : BitVec 128}` — pure BitVec. Used by
  `divw_remw_poly` (DivwRemw.lean:477).

If a "Fin KB solo" lemma's signature has `{x : Fin KB}` or
`{x : Vector (Fin KB) N}` in it, it's truly Fin KB-specific. If the only
Fin KB connection is the section's `variable` block but the signature is
in ℤ/ℕ/BitVec, **it stays** — grep the whole repo before deleting.

## Sail-level spec_X defs are shared

`SP1Chips/DivRemChip.lean` defines 8 `def spec_<v> (rs2 rs1 rd : regidx)
: SailM Unit` (one per variant, e.g. `Div.spec_div`, `Divu.spec_divu`,
…). These have no Fin KB / ZMod p dependence — they're pure Sail-level
wrappers around `execute_DIV` / `execute_DIVW` / `execute_REM` / `execute_REMW`.
They were originally next to the deleted Fin KB `correct_<v>` theorems
but are ALSO referenced from `correct_<v>_poly` (e.g.
`(Div.spec_div ...).run s`). Keep them when deleting the chip's Fin KB
layer.

## Comment hygiene

Eight `/-- Polymorphic counterpart of `X`. -/` docstrings became
self-referential after the deletion (their `X` no longer exists).
Re-edited each to drop the lead sentence and keep substantive content.
Grep `Polymorphic counterpart` after each deletion to catch them.

## Verification (2026-05-15)

- 7 incremental `lake build SP1Chips` runs, all clean (0/0). Final full
  build: 8520 jobs, 0 errors, 0 warnings.
- `lean_verify` on all 8 `DivRem.Poly.correct_*_poly`: still axiom-clean
  (`propext`, `Classical.choice`, `Quot.sound` ± pre-existing
  `combine_MUL_MULH_poly._native.bv_decide.ax_*` /
  `combine_MUL_MULHU_poly._native.bv_decide.ax_*` /
  `extractLsb_is_toInt._native.bv_decide.ax_*`). Zero `sorryAx`.
- Net deletion: ~3290 lines across 7 files.

## File sizes after sweep

| File | Before | After | Δ |
|---|---|---|---|
| DivRemChip.lean | 946 | 667 | -287 |
| DivRem/DivRem.lean | 2401 | 1538 | -863 |
| DivRem/DivuRemu.lean | 1772 | 1014 | -758 |
| DivRem/DivwRemw.lean | 2401 | 1516 | -885 |
| DivRem/DivuwRemuw.lean | 1708 | 997 | -711 |
| DivRem/Common.lean | 851 | 687 | -164 |
| DivRem/Constraints.lean | 1313 | 967 | -346 |
