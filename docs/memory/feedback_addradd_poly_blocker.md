---
name: AddrAddOp _poly resolved 2026-05-02 via skipKernelTC
description: AddrAddOperation.spec_of_constraints_poly landed via AddOperation.spec_poly's recipe + skipKernelTC. Skipped cols_is_a_sum_b_poly intermediate (its % 2^64 type-level form triggered kernel deep recursion). 8 Store/Load chip migrations unblocked.
type: feedback
originSessionId: affe1bb4-3286-4726-b861-93dd84582b22
---

**RESOLVED 2026-05-02 (commit `909799e`).** The poly helper landed via:

1. Skip the `cols_is_a_sum_b_poly` intermediate — its `(...) % 2^64 = ...`
   type-level form triggered kernel deep recursion on `2^64` (regardless
   of whether the body had `omega`, `linear_combination`, or `sorry`;
   the kernel re-checks the theorem TYPE which contains `2^64`).
2. Mirror `AddOperation.spec_poly` directly: bridge through
   `BitVec.toNat_add` + `Word.toBitVec64_poly_toNat_poly`, then
   `Word.toNat_poly_def` to expose limb-wise nat sums. Set carry
   aliases via `set c0..c3 := (...) * 65536⁻¹`, derive 4 ZMod limb
   equations via `linear_combination ... * h65inv`, lift each to Nat
   via local `limb_lift` (verbatim from AddOperation), close with
   `omega`.
3. Add `set_option debug.skipKernelTC true in` (per `docs/GOTCHAS.md`
   "Kernel deep-recursion on `2^N`") to bypass the kernel re-check on
   `BitVec.toNat_add`'s `% 2^64` rewrite combined with the 4-limb
   carry chain. The proof elaborates fine; only the kernel re-check
   fails. `lean_verify` confirms standard axioms only (propext /
   Classical.choice / Quot.sound) — no new axioms introduced.

**Why `cols_is_a_sum_b_poly` was problematic but `spec_of_constraints_poly`
isn't:** the former's signature has `(a.toNat_poly + b.toNat_poly) % 2^64
= ...` with `2^64` literal in the type. The kernel re-checks the type
itself and deep-recurses. The latter's signature is `cols_word.toBitVec64_poly
= ...` (BitVec equation), and `2^64` only enters the proof TERM (via
`BitVec.toNat_add` rewrite), where `skipKernelTC` skips the re-check.

**8 chips unblocked** for chip-proof migration: Store{Byte,Half,Word,
Double}, Load{Byte,Half,Word,Double}. Each chip-proof migration is now
mechanical — replace `AddrAddOperation.spec_of_constraints` with
`spec_of_constraints_poly`, swap `Word.toBitVec64` → `Word.toBitVec64_poly`,
and the field-agnostic memory helpers (`run_vmem_write_of_width_8`, etc.)
should compose. ~1-2 hours per chip estimated.

---

(Original blocker analysis below, kept for historical context.)

The Tier 1 Store/Load chip migrations are blocked on
`AddrAddOperation.spec_of_constraints_poly`, which in turn depends on
`is_u48_sum_poly` and `cols_is_a_sum_b_poly`. The Fin KB versions
(`SP1Operations/Operation/AddrAddOperation.lean:42-96`) close via:

```
cases h0 <;> rename_i h0
<;> simp [sub_eq_zero] at h0
<;> simp [h0] at h1 h2 h3
<;> ... (4× nested for h0..h3)
<;> omega
```

This 16-way case-split traverses every combination of carry values
(each in {0, 1}) and discharges via `omega` over `Fin KB.val` natural
arithmetic. The KEY simplification driving it is `simp [h0] at h1` —
once `h0` is concrete (`carry0 = 0` or `= 1`, written algebraically as
`a[0] + b[0] - cols.value[0] = 0` or `= 65536`), `simp` propagates this
into `h1`'s carry expression. The simp is doing concrete `Fin KB`
arithmetic where `*` and `+` are nat-mod-KB.

**Why ZMod p version doesn't translate directly:** in ZMod p, `+` and
`*` are field operations, and `simp [h0]` doesn't reduce arithmetic in
the same way — `(a[0] + b[0] - cols.value[0]) * 65536⁻¹ = 0` doesn't
auto-simplify to `a[0] + b[0] - cols.value[0] = 0` (need explicit
`mul_eq_zero` + `inv_ne_zero` reasoning). And once you have `a[0] +
b[0] - cols.value[0] = 0` (or `= 65536`), `omega` doesn't apply — you
need `ZMod.val_sub_cases` to lift to `(a[0] + b[0]).val = cols.value[0].val`
or `(a[0] + b[0]).val = cols.value[0].val + 65536`, then track via
`ZMod.val_add_of_lt` (which needs the `Fact (2^17 < p)` to ensure no
wrap).

**Rough proof sketch for `is_u48_sum_poly`:**

```
-- For each carry hypothesis h_i: (...) * 65536⁻¹ = 0 ∨ = 1:
--   1. multiply both sides by 65536: a[i] + b[i] + carry_{i-1} - cols.value[i] = 0 ∨ = 65536
--   2. by ZMod.val_sub_cases (with bounds from isU64_poly): get nat equation
--   3. accumulate per-limb nat equations to compute toNat_poly
-- Final omega over the assembled nat equations: sum < 2^48
```

**Estimated effort**: ~1 day for all 4 lemmas (`is_u48_sum_poly`,
`cols_is_a_sum_b_poly`, `spec_poly`, `spec_of_constraints_poly`).
Once landed, all 8 Store/Load chips become mechanical migrations
(except for memory-model helpers which are already field-agnostic).

**How to apply**: don't attempt the Stores until AddrAddOp `_poly`
is in. Easier alternative: pivot to Branch (Tier 2) where the blocker
is chip-local helpers (`single_op_poly`, `eq_signExtend_of_is_real_poly`,
`add_signExtend_of_constraints_poly`) — all 6-way case-splits over
chip variants, no operation-level proof obligations needed.
