---
name: fin-kb-deletion-sweep-complete-all-chips
description: "On dtumad/final-aggregation as of 2026-05-15, every chip has zero Fin KB code. ShiftRight closed via `3db0db0` + `0f063b6` after merging the other session's _poly proofs."
metadata: 
  node_type: memory
  type: project
  originSessionId: be982432-c166-465e-a1f4-2bf1290233a2
---

As of 2026-05-15 on `dtumad/final-aggregation`, the Fin KB deletion sweep
across `SP1Chips/` is **COMPLETE for all chips**. Initial 7 commits
(`8bd92c7..ffe9189`) drained Lt/Branch/ShiftLeft/Bitwise/Mul/Load{Byte,
Double,Half,Word}; the merge `e81f2f2` brought in the other session's
ShiftRight `_poly` proofs (`bdf428b`); commits `3db0db0` and `0f063b6`
then deleted ShiftRight's Fin KB tree.

Initial sweep:
- `lt: drop Fin KB is_X defs + allHold_constraints_iff_X` — Lt/Constraints
- `branch: drop Fin KB is_real + single_op + signExtend lemmas` — Branch/Constraints
- `shiftleft: drop dead Fin KB variable declarations` — ShiftLeft/{Common,Constraints}
- `bitwise: drop dead Fin KB helper tree` — Bitwise/Constraints (309 lines)
- `mul: drop dead Fin KB helper tree` — Mul/Constraints (222 lines)
- `load: drop dead Fin KB is_l[bhwd]u? + allHold_constraints_iff_of_is_*` —
  Load/{LoadByte,LoadDouble,LoadHalf,LoadWord}/Constraints (364 lines)

ShiftRight closure (post-merge):
- `3db0db0 shiftright: drop 8 Fin KB namespaces in ShiftRightChip` (469 lines).
  Also includes a `show`→`change` cleanup at Srlw.lean:389/436 to silence
  two `linter.style.show` warnings from the merged code.
- `0f063b6 shiftright: drop Fin KB helper tree` — 1189-line removal across
  Constraints/Common/Srl/Sra/Srlw/Sraw (allHold_constraints_iff, single_op,
  single_su16, is_real, srl_real family, register_bounds, immediate_bounds,
  op_a_is_0, ops_U64_*, sp1_op_*, field_arithmetic helpers, per-op spec
  bodies, spec.<op>_common shared bodies).

**Verification (run after the sweep, all green):**

1. `rg 'Vector \(Fin KB\)' SP1Chips/` → only ShiftRight matches.
2. `rg '\.allHold\b' SP1Chips/` → only ShiftRight matches.
3. `rg 'Fin KB' SP1Chips/` → 9 hits left, ALL inside `--` doc comments
   referencing the old recipe ("the Fin KB version simps via..." etc.).
4. `lake build SP1Chips` clean: 0 errors, 0 warnings, 8520 jobs (final).

**State per chip:**

| Chip | Status |
|---|---|
| Add, Addi, Addw, Sub, Subw, UType, Jal, Jalr, LoadX0 | Was collapsed earlier |
| Lt, Branch, Bitwise, Mul, ShiftLeft, LoadByte, LoadDouble, LoadHalf, LoadWord | Cleaned this session |
| StoreByte, StoreDouble, StoreHalf, StoreWord | Was collapsed earlier (no Fin KB residue found) |
| DivRem | Was collapsed in the 7 commits ending `fcd36a2` (2026-05-15 morning) |
| ShiftRight | Cleaned this session (commits `3db0db0` chip + `0f063b6` helpers, ~1660 lines deleted) |

**Why the plan called these "near-collapsed" but they had hundreds of dead
lines:** the pre-flight grep used `rg -c 'Fin KB|allHold_poly|\.allHold\b'`
which sums all three patterns. Files like Bitwise/Mul/DivRem had 1 Fin KB
mention but actually contained whole helper trees (`is_real`, `single_op`,
`spec.<op>`, `register_bounds`, `sp1_op_*` etc.) that were duplicated
versions of `_poly` siblings. Verified each was dead before deletion via
`rg '\b<Chip>\.<helper>\b' SP1Chips/*.lean` and `rg '\b<helper>\b'
SP1Chips/<Chip>Chip.lean` (covering the `open <Chip>` import case).

**Same pattern in Load constraint files:** `is_l[bhwd]u?` + iff lemmas
were all dead too; chip files import `Load.<Width>.Constraints` and use
only `_poly`-suffixed siblings.

**Pattern that recurred** for clean deletion: each helper file had a
`section poly_helpers` (or just a `_poly` cluster at the end) that was
self-contained — defines its own `is_real_poly`, `is_<op>_poly`,
`allHold_constraints_iff_<...>_poly`, etc. Just remove everything between
`end constraints` and `section poly_helpers` plus the leading
`variable (Main : Vector (Fin KB) N)` + `def is_real` block.

**How to apply:** the same recipe should work for ShiftRight when ready.
Verify chip-side has no callers, then bulk-delete via Edit (one section
per call — sed bulk-deletes are blocked by the harness).

See [[project_field_generic_effort]] for the broader migration history,
and [[project_divrem_finkb_deletion]] for the original DivRem precedent.
