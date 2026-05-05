---
name: ShiftLeft generic allHold_constraints_iff_poly is intractable
description: Writing a Lt-style allHold_constraints_iff_poly for ShiftLeft (195-let constraints body, ~70-clause RHS) blows simp/tauto/simp_all elaboration limits even at maxHeartbeats 100M.
type: feedback
originSessionId: 3deaa0d0-a1f8-441b-acba-b385131a5eb3
---
When attempting to apply field-polymorphic Sub-style migration to `SP1Chips/ShiftLeftChip.lean`, the natural first step is `allHold_constraints_iff_poly` (the polymorphic mirror of the existing `allHold_constraints_iff` at `SP1Chips/ShiftLeft/Constraints.lean:288`). For Lt this works in seconds; for ShiftLeft it does not, regardless of terminal tactic.

**Why:** ShiftLeft's `constraints` body has ~195 `let` bindings and the iff RHS has ~70 conjuncts. Closing tactics tried, each on a fresh `lake env lean SP1Chips/ShiftLeft/Constraints.lean`:
- `simp [constraints, sub_eq_zero]` — leaves a chain of ~70 implications as residual (one direction unprovable from the other automatically).
- `simp [constraints, sub_eq_zero]; tauto` — runs >8 minutes, RSS climbs to 16GB, never terminates.
- `simp_all [constraints, sub_eq_zero]` — fails fast with `simp` failed: maximum number of steps exceeded.
- `simp (config := { maxSteps := 10000000 }) [...]` not tried but unlikely to help.

**Why:** The Lt counterpart succeeds because Lt's constraints def has ~50 let bindings and the iff RHS is smaller. The Sub/Add/Subw/Addi/Addw/UType chips that successfully migrated to Sub-style use `simp [constraints]` directly in `correct_*` (no iff_poly needed) — their constraints bodies are tiny and the per-chip `*Operation.spec_poly` from `SP1Operations` does the heavy lifting. ShiftLeft has no operation-level analogue (the four `spec.sll/slli/sllw/slliw` lemmas live chip-local at lines 528+), so without iff_poly there's no way to extract reader/CPU/operation hypotheses for the ZMod p chip proof.

**How to apply:** When asked to do Sub-style chip-proof migration on chips with large constraints bodies (DivRem ~247 cols, Mul, Bitwise, Branch ~46–52 cols), expect the same wall. Lt-style minimal (PARAMETRIC_CHIPS entry + `is_*_poly` companions, chip proof unchanged in Fin KB) is the realistic depth. ShiftLeft's current state matches LtChip exactly: parametric constraints def + simple type-companion helpers. Anything beyond that for ShiftLeft would require either (a) splitting `constraints` into smaller named sub-blocks (deep refactor of the auto-generated body, fights the constraint compiler), or (b) per-variant iff_poly lemmas where the variant's `is_*_poly` hypothesis collapses enough disjunctions — also untested but might fail similarly since the simp-on-constraints-body cost is the bottleneck.
