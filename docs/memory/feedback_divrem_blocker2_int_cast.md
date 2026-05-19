---
name: divu_remu_poly Blocker 2 — `.cast` is Nat→ℤ, not ZMod.cast
description: The `.cast` form in the c=0 branch goal pretty-print is the Nat→ℤ coercion inserted to type-check `BitVec.ofNat 64 (q : ℤ)`, not ZMod.cast — so `push_cast [ZMod.cast_eq_val]; rfl` is the closer
type: feedback
originSessionId: 21d8404b-7f1c-4058-af39-ad3dc3261398
---
When porting `divu_remu_poly`'s c=0 branch (Blocker 2 from
`feedback_divrem_core_port_blockers.md`), the post-simp goal shows:
```
⊢ BitVec.ofNat 64 (b0.val + b1.val * 65536 + ...) =
    BitVec.ofNat 64 (b0.cast + b1.cast * 65536 + ...).toNat
```

**The `.cast` is misleading** — it's NOT `ZMod.cast`, it's the
**`Nat → ℤ`** coercion, and the outer `.toNat` is **`Int.toNat`**.
Source: `execute_DIV_REM_pure_int .DRU` does
```
let nop1 : ℤ := BitVec.toNat op1
...
let q := if nop2 = 0 then 2^64 - 1 else Int.tdiv nop1 nop2
let r := Int.tmod nop1 nop2
```
then `BitVec.ofNat 64 q` requires `q : ℕ`, so Lean inserts `.toNat`
on the Int. The `b.cast` chunks come from `op1.toNat` being unfolded
to `(BitVec.ofNat 64 (b0.val + ...)).toNat → b0.val + ...` (mod 2^64),
then implicitly coerced to ℤ, displayed via the `Nat.cast → ℤ` arrow
which pretty-prints as `b.cast`.

**Closer:** `push_cast [ZMod.cast_eq_val]; rfl`.

**Why plain `rfl` fails:** The LHS is `BitVec.ofNat 64 (Nat sum)`
and the RHS is `BitVec.ofNat 64 (Int.toNat (Int sum))`. They're
definitionally equal only after the casts are pushed through —
`push_cast` resolves the `(b.val : ℕ → ℤ).toNat = b.val` chain.

**Why `bv_decide` fails:** The expressions involve free `ZMod p`
variables — bv_decide doesn't have a path to relate `b.val` (a Nat
that depends on `p`) to a BitVec.

**Why `norm_cast` makes no progress:** It tries to push casts
toward the leaves, but the casts here are already at the leaves
(`b.val : ℤ`), and the `Int.toNat` blocking the further reduction
isn't a cast that `norm_cast` knows how to dispose of.

**How to apply:** When porting any chip-level `_poly` proof that
goes through `execute_*_pure_int` (DIV_REM is the standout, but
this pattern likely applies to other Sail-spec ops that compute
through Int), expect the same `Nat→ℤ`-cast residue and use
`push_cast [ZMod.cast_eq_val]; rfl` (or `push_cast; congr 1;
push_cast [ZMod.cast_eq_val]; rfl` if the outer BitVec.ofNat
needs peeling first) as the closer.
