---
name: project-divrem-poly-complete
description: DivRem _poly conversion fully closed (no sorries) — patterns + helper additions
metadata: 
  node_type: memory
  type: project
  originSessionId: c7b9736a-8511-460b-af3e-102c10573d7e
---

# DivRem _poly conversion VERIFIED COMPLETE (2026-05-15, commits e653978 + 091b675)

The 2026-05-14 "fully complete" claim was premature — commit `a62938b` later
documented a real blocker on `spec.divw_poly` / `spec.remw_poly` (3-form
`w_eq_msb_*` hypothesis variance across `all_goals` side-goals). Today's
work re-closes those plus the analogous arms in `spec.div_poly` /
`spec.rem_poly`, verifies the full closure under `lake build` (zero errors,
zero warnings), and audits all 8 `correct_*_poly` axiom sets via
`lean_verify` — only `propext`/`Classical.choice`/`Quot.sound` (+ standard
`bv_decide` native axioms) remain. **No `sorryAx` anywhere.**

All 4 spec wrapper sorries closed:
- `spec.divw_poly`, `spec.remw_poly` in `SP1Chips/DivRem/DivwRemw.lean`
- `spec.div_poly`, `spec.rem_poly` in `SP1Chips/DivRem/DivRem.lean`

Plus a separate Word.lean refactor (commit `e653978`) dropping
`debug.skipKernelTC true` from `extend_true_is_signExtend_poly` across
Word/BWord/BHWord — splits on `isNegative_poly` and dispatches via
`BitVec.signExtend_eq_setWidth_of_msb_false` /
`signExtend_eq_not_setWidth_not_of_msb_true` rewrites, which keeps the
elaborated proof term shallow enough for kernel re-check. Verified clean
across 7 known callers (DivRem, MulOperation, SailM).

**Why:** Final step of DivRem migration from Fin KB to ZMod p (`_poly` suffix). User invoked the existing `correct_*_poly` chip theorems require sorry-free spec wrappers to be axiomatically sound. Confirmed: `#print axioms DivRem.Poly.correct_<v>_poly` returns `axioms: []` (only kernel built-ins).

**How to apply:** The two failure modes have different fixes.

## .DRWS (divw/remw) — sign-extension at 32-bit boundary

Goal arms after `all_goals` reduce to `Word.isU64_poly #v[?, ?, m * 65535, m * 65535]` where `m ∈ {0, 1}` is one of msb_b/msb_c/msb_rem/msb_quot. Fix:

1. **Derive msb_? ∈ {0, 1}** in the `all_goals` block via the post-`gen_poly` form of `w_eq_msb_?`. The hypothesis appears in **3 forms** across side-goals (blocker commit `a62938b`); use `first | (have h : ... := w_eq_msb_? h_iw_1; ...) | ...` with the three antecedent shapes ((32768 : ZMod p) ≤ ?x / ?x.val ≥ 32768 / raw List.Forall via `U16MSBOperation.spec.gen_poly`).
2. **Resolve_left** the w_eq_*_w disjunctions to peel `rbc/qbc = msb_? * 65535`.
3. **Use `msb_arm_closer_poly`** (new helper in `SP1Chips/DivRem/Common.lean`) in the closer chain: `apply msb_arm_closer_poly u16_r0 u16_r1 h_msb_rem_01` etc. Closes shape `#v[x, y, m * 65535, m * 65535]` given u16 bounds + `m ∈ {0, 1}`.

## .DRS (div/rem) — no sign-extension; bounds-only fix

Surprise: the rbc/qbc arms didn't actually need msb derivations. Simply pre-extracting U64 limb bounds was enough:

```lean
have ⟨_hb0, _hb1, _hb2, _hb3⟩ := Word.lt_cases_of_isU64_poly is_U64_b
have ⟨_hc0, _hc1, _hc2, _hc3⟩ := Word.lt_cases_of_isU64_poly is_U64_c
```

Inserted into the `all_goals` block before the simp. This exposes `c?.val < 65536` and `b?.val < 65536` to `simp_all` in the existing closer arms (`Word.isU64_of_cases_poly <;> simp_all; done`), which then closes the previously-sorry arms.

**Lesson:** for sorry-free closures, always try pre-destructuring U64 hypotheses first — it's often enough on its own and is much cheaper than adding msb closer arms.

## New artifact

`SP1Chips/DivRem/Common.lean:msb_arm_closer_poly` — closes `Word.isU64_poly #v[x, y, m * 65535, m * 65535]` given two u16 bounds + `m ∈ {0, 1}`. Used by divw_poly / remw_poly only; div_poly / rem_poly don't need it.

Also added `omit [Fact (2 ^ 17 < p)] in` before `maco_arm_closer_poly` because the new helper introduced a use of `Fact (2 ^ 17 < p)` in the section, triggering `linter.unusedSectionVars` on `maco_arm_closer_poly`.

## Verification (2026-05-15)

- `lake build` (full): 0 errors, **0 warnings** (8522 jobs). The "24 warnings" mentioned in the 2026-05-14 entry were `set_option maxHeartbeats` blocks missing the explanatory `-- <reason>` comment + 4 unreachable `first` alternatives in DivuwRemuw introduced by commit `a7c6233`; both fixed in commit `091b675`.
- `lean_verify` on all 8 `DivRem.Poly.correct_*_poly` theorems: zero `sorryAx`. Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`, plus `combine_MUL_MULH_poly._native.bv_decide.ax_*` / `extractLsb_is_toInt._native.bv_decide.ax_*` for the bv_decide-using arms).

## Build cycle note

15 build iterations on DivwRemw.lean (~10-25 min each). The key insight that unblocked div/rem (vs divw/remw) was discovered by accident: simplifying div_poly's helpers showed the msb stuff was never reached because `simp_all` was already closing arms using the pre-extracted limb bounds.

## 2026-05-15 verification round (overnight)

Six clean `lake build`s in sequence (Foundations → MulOp + SailM parallel → DivRem.Common → DivRem.DivRem → DivRem.DivwRemw → DivRem.DivuRemu + DivRem.DivuwRemuw parallel → DivRemChip → full lake build). The 3-form `first | … | … | …` chain in DivwRemw closed all side-goals on the first build attempt — no need for the aggressive `apply U16MSBOperation.spec.gen_poly at` upfront-rewrite fallback. Total wall ≈ 100 min (well under the 4.5 h nominal budget).
