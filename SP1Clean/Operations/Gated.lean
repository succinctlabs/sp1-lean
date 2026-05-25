import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Subcircuit

/-! # `Gated.assertion` pattern — design notes + lookup-restriction caveat

SP1's constraint compiler emits per-row constraints that are commonly
**gated** by a selector field: an `is_real` boolean, an `is_real - op_a_0`
xor, an `is_xor` / `is_or` / `is_and` per-opcode flag. The gating is
syntactic — every conjunct of the gated operation appears multiplied by
the selector. When the selector is 0 (padding rows, or rows for
different opcodes in a multi-opcode chip), every conjunct becomes `0 = 0`
and the inner operation is vacuously satisfied.

The SP1Clean pilot's first 13 chip-level `FormalAssertion` bundles either
(a) had no gated operation, or (b) dropped the gated clause from
`Assertion.main` and kept it in the chip's legacy `Spec` carried by
`iff_sp1` ("Path-2" promotion; see `feedback_path2_chip_promotion_recipe`).
Path-2 keeps the safety-floor of the Clean DSL intact at the cost of not
covering the operation inside the Clean FormalAssertion bundle.

Iter-5 introduces a pattern — **not a polymorphic combinator**, for the
reason below — for emitting gated operation constraints **inside** a
chip's `Assertion.main`. The first concrete instance is
`SP1Clean.GatedAddOp` (used by JalrChip's `is_real`-gated jump-target
sum).

## Why not a polymorphic `Gated.assertion`?

The naive design would be a function
`Gated.assertion : Expression → FormalAssertion α → FormalAssertion (Gated α)`
that lifts an arbitrary inner `FormalAssertion sub` into one whose
`main` emits `gate * <each constraint of sub.main>`. Two structural
obstacles make this impossible to implement cleanly today:

1. **Lookups cannot be gated by field multiplication.** Many inner
   operations (e.g. `SP1Clean.AddOp.assertion`) emit `Range(16)` or
   `U8Range` lookups on their result limbs. A lookup is table
   membership, not a polynomial equation: `lookup t v` is not the same
   as `lookup t (gate * v)`. On a padding row where `gate = 0`, we want
   the lookup to be **vacuous** (no multiplicity), not to fire with the
   value 0. Clean's lookup encoding has no per-row multiplicity field,
   so there's no shape-preserving rewrite from "ungated lookup" to
   "gated lookup".

2. **`Circuit` is monadic and its `Operations` list is opaque.** Even
   if we ignored (1), implementing `Gated.assertion sub` would require
   inspecting `sub.main`'s emitted operations and rewriting each
   `assertZero e` into `assertZero (gate * e)`. The `Circuit` monad
   exposes operations only through `do`-block scope, not as a
   first-class structure transformable by a polymorphic combinator.

## The pattern

For each inner operation that needs a gated form, **hand-write** a new
`FormalAssertion` whose:

- **Inputs** bundle the inner inputs plus a `gate : F` field.
- **`main`** emits the inner's `assertZero` constraints multiplied by
  `gate`, and **drops the inner's lookups entirely**. The dropped
  lookups remain in the chip's legacy chip-level `Spec` and are
  consumed by `iff_sp1`. On padding rows where `gate = 0`, the
  chip-level `Spec` is responsible for asserting that the lookups
  vacuously hold (which SP1's multiplicity-zero discipline guarantees
  at the trace level).
- **`Spec`** is `gate = 0 ∨ inner.Spec`, where `inner.Spec` is the
  *carry-only* fragment of the original (without range bounds — those
  go through the chip's lookup path).
- **`soundness`** uses `mul_eq_zero` (valid in a field) to discharge
  each gated `assertZero` into the disjunction.
- **`completeness`** case-splits on `Spec`: when `gate = 0`, every
  `gate * e = 0`; when `inner.Spec` holds, multiply the inner's
  scalar carries by `gate`.

## Files following this pattern

- `SP1Clean/GatedAddOp.lean` — first concrete instance. Gated form of
  `AddOp.assertion`, dropping the 4 `Range(16)` result-limb lookups.
  Used in `SP1Clean.Jalr.Assertion.main` for the `is_real`-gated
  jump-target sum.

When iter-6 picks up `LtChip` / `BranchChip`, a `GatedLtOperationSigned`
should follow this same pattern. -/

namespace SP1Clean.Gated

end SP1Clean.Gated
