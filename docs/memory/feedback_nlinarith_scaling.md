---
name: nlinarith doesn't scale past ~4 limbs in Mul-style proofs
description: For proofs with sums of byte-level products (e.g. core_mul_poly), `nlinarith` for bound checks doesn't scale; use explicit `Nat.mul_le_mul (by omega) (by omega)` + `omega`.
type: feedback
originSessionId: c79007a4-e8a4-477f-be9f-d731659037b8
---
When porting `core_mul_poly` (16 byte-product limbs) over `ZMod p`,
the natural approach — `simp [L]; nlinarith` for the per-limb bound
checks `L < p` and `R < p` — works for 4 limbs (`core_mulw_poly`,
100s build) but **doesn't terminate at 16 limbs** (30+ minutes,
killed manually). With 32 nlinarith calls in scope, each having
to multiply 16 byte-bounds + 16 carry-bounds, the search space
explodes.

**Why:** `nlinarith` is exponential in `#hypotheses × #products`. With
many byte values in scope and a sum of byte products on the RHS, each
call has to try all multiplications. Doesn't scale.

**How to apply:** Replace `nlinarith` with explicit `Nat.mul_le_mul (by
omega) (by omega) : bw[i].val * cw[j].val ≤ 255 * 255` for each byte
product, then close with `omega` (which handles linear arithmetic with
opaque-bounded products as variables).

```lean
-- L bound (linear, just carry * 256): omega works
have hL_lt : L < p := by simp [L]; omega
-- R bound (sum of products): explicit byte bounds + omega
have hb_0_k : bw[0].val * cw[k].val ≤ 255 * 255 :=
  Nat.mul_le_mul (by omega) (by omega)
have hb_1_km1 : bw[1].val * cw[k-1].val ≤ 255 * 255 :=
  Nat.mul_le_mul (by omega) (by omega)
... (k+1 such bounds for limb k)
have hR_lt : R < p := by simp [R]; omega
```

For 16 limbs, total byte-product `have`s: 1 + 2 + ... + 16 = 136.
Verbose but mechanical and **fast**: 341s for `core_mul_poly` (down
from 30+ min and counting).

**Companion insight — `linear_combination` in factored form**: when
the polynomial identity has many terms with a common factor (e.g.
`* 2^128` for the i+j ≥ 16 cross-products in core_mul), prove `key`
**directly in factored form** (`+ (... + ... * 2^8 + ... * 2^16 + ...)
* 2^128`) rather than the expanded form. `linear_combination` over ℤ
after `zify` closes both forms, but the factored form avoids the big
final `ring` rewrite at the BitVec bridge — `Nat.add_mul_mod_self_right`
applies directly.

**Don't try `∀ (i j : Fin n)` quantified byte-product helper**: after
`fin_cases i`, the `bw[i.val]` indexing leaves `↑i < 16` side-conditions
that don't auto-close. Inline byte-product bounds are the way.
