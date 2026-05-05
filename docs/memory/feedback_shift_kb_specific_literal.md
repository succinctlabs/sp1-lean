---
name: ShiftLeft/ShiftRight constraints embed KB-specific literal 64⁻¹
description: Shift chip constraints use the magic constant 2097414145 = (64⁻¹ in KoalaBear), blocking field-generic _poly migration without an extra typeclass
type: feedback
originSessionId: c8b9f50a-f135-4584-9101-770fba082050
---
The constraint compiler emits `2097414145` as a literal in both
`SP1Chips/ShiftLeft/Constraints.lean` and `SP1Chips/ShiftRight/Constraints.lean`
(e.g. `let E84 : F := E83 * 2097414145` and `((c0 - m) * 2097414145).val < 1024`).
This number is `64⁻¹` in KoalaBear specifically — `2097414145 * 64 ≡ 1 mod KB`.
For any other prime, `2097414145` has no special meaning, so the lemmas that
encode "x is divisible by 64" via `((x - witness) * 2097414145).val < 1024`
cannot be proven polymorphic without an extra hypothesis.

**Why:** SP1's constraint compiler is optimizing the divisibility-by-64 check
using a KoalaBear-specific bit trick (multiply by precomputed inverse,
check the result is small). Universal field literals like `256` and
`65536` (used in Mul/DivRem) work in any large enough prime, but
`2097414145` is field-specific.

**Discovery method:**
```
grep -oE ' \* [0-9]{8,}' SP1Chips/<Chip>/Constraints.lean | sort -u
```
- Mul: empty (uses 256, 65536 only) → migrated cleanly
- DivRem: empty (uses 65535, 65536 only) → migrate cleanly
- ShiftLeft/ShiftRight: `* 2097414145` → blocked

**How to apply:** When deciding which chip to field-generalize next,
run the grep above first. Any chip with `2097414145` (or other
8+-digit literal) is KoalaBear-specific in its constraint encoding
and needs either:
(a) `Fact ((2097414145 : ZMod p) * 64 = 1)` as a precondition on
    every `_poly` theorem (honest: theorems hold for any field
    where the bit-trick holds, KB is one such), or
(b) constraint compiler refactor to emit `inv_64 : F` symbolically
    (out of scope — fights the compiler).

This is the deeper reason the prior author stopped ShiftLeft at
"Lt-style minimal" depth (per `feedback_shiftleft_iff_poly_blowup.md`).
The simp+tauto blowup is the surface symptom; the magic-literal
obstruction is the root.
