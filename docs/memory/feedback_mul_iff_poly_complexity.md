---
name: Mul iff_poly port has bound-source mismatches
description: Literal port of `MulOperation.allHold_constraints_iff_is_real` to ZMod p doesn't close — bounds in original come from heterogeneous sources (byte sends → field-level `<`; sub-constraint lists → `.val <`).
type: feedback
originSessionId: aa754f6f-4de9-42e7-98bd-ab3df0b0df17
---
When porting `MulOperation.allHold_constraints_iff_is_real` to a `_poly` version, a literal substitution (`Fin KB` → `ZMod p`, `< 256` → `.val < 256`) does NOT close via the same `simp [constraints]; split; split; ...; simp_all` proof.

**Why:** The original iff RHS bundles ~100 conjuncts whose bounds come from at least three different sources, and the polymorphic `SP1Constraint.toProp_poly` produces them in different shapes:

1. `MSB` byte sends (`(.byte ByteOpcode.MSB cols.b_msb E7 0)`) — `ByteOpcode.MSB.constrain_poly` (in `SP1Foundations/ByteOpcode.lean:115`) emits **field-level** `(a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b ≥ 128)`. So the polymorphic iff RHS for the b_msb / c_msb conjuncts must use `<` over `ZMod p` (not `.val <`), and `≤` (not `≤ .val`).
2. Sub-constraint lists from `U16toU8OperationSafe.constraints` — these stay as `List.Forall SP1Constraint.toProp_poly U16_b/U16_c` opaque blocks; the bbw[i].val < 256 / cbw[i].val < 256 bounds inside them aren't surfaced unless you also unfold `U16toU8OperationSafe.constraints`.
3. The `cols.carry[i].val < 65536` and `cols.product[i].val < 256` bounds in the original `Fin KB` iff (lines 865–888 of MulOperation/Constraints.lean) **don't have a clean source in the polymorphic constraint list**. The simp emits the constraint list with byte sends + assertZeros only — the explicit `.val <` bounds in the iff RHS are derived facts, not direct constraint outputs. In the `Fin KB` proof these come "for free" from the byte-range table sends inside U16toU8OperationSafe via field-level `<`, but in `ZMod p` the same sends produce field-level `<` (not `.val <`).

**How to apply:** Don't attempt a literal port. Either:

- Drop the `.val <` bounds from the iff_poly RHS and prove them at point-of-use via `Word.lt_cases_of_isU64_poly` or by lifting from the U16toU8OperationSafe `_poly` spec.
- Unfold `U16toU8OperationSafe.constraints` inside the simp set so the byte-range bounds surface, then re-collect them in the right `.val` form via `ZMod.val_lt_iff_*` or similar bridging lemmas.
- Use Branch's in-place destructure pattern (BranchChip.lean:232) instead of building a chip-level iff at all — destructure the constraint list per-arm in each `correct_*_poly`.

**Resolution (2026-05-04):** Pivoted to **direct destructure** at the chip level, sidestepping the iff entirely (Branch's pattern from `BranchChip.lean:232`). The recipe is:

```lean
simp only [SP1ConstraintList.allHold_poly, Mul.constraints, List.forall_append,
  List.Forall, SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
obtain ⟨⟨⟨h_mop, h_cpu⟩, h_alu⟩, b_77, b_78, b_79, b_81, b_80, sum_disj, h_M13⟩ := cstrs
```

The structure follows the chip's `CS0 ++ CS1 ++ CS2 ++ [...]` body literally:
- `((h_mop ∧ h_cpu) ∧ h_alu)` (3 sub-constraint lists, left-associated)
- 5 boolean disjunctions in compiler-emitted order `77, 78, 79, 81, 80`
- sum disjunction (after `sub_eq_zero` simp: `Σ = 0 ∨ Σ = 1`, no `- 1 = 0`)
- M13 = 0 (op_a_0)

Bound extraction (operand isU64) uses `RTypeReader.allHold_constraints_iff_is_real_poly`
on the `h_alu` sub-constraints, taking `h_is_real_eq_one : Σ = 1` as input
(derived once at the chip level via `sum_eq_one_of_eq_one_*` helpers).

The `_neq` facts for `(k : ZMod p) ≠ 0` (k ∈ {1..5}) bridge through
`ZMod.val_natCast_of_lt` + `congrArg ZMod.val` + omega, with explicit
`(2 : ℕ) < p` hypotheses bound from `Fact (2^17 < p)`.

The original "literal port of allHold_constraints_iff_is_real" approach is no longer
needed for this chip — the `single_op_poly` and `ops_U64_b_c_poly` helpers in
`SP1Chips/Mul/Constraints.lean` (commits `878332b`, `fb6c769`) and
`MulOperation.single_op_poly` (commit `41558f8`) demonstrate the clean path forward.

**Remaining for Mul:** the carry-chain `core_mul_poly` / `core_mulw_poly` lemmas
and 5 `MulOperation.spec.<variant>_poly` lemmas are still the heavyweight
remaining work. See `project_field_generic_effort.md` for the full status.
