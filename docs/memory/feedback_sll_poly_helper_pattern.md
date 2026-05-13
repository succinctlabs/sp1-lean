---
name: spec-sll-poly-fully-closed-via-5-layer-helper-architecture-sll-within-byte-shift-0-1-2-3-poly-4-case-wrappers
description: All 64 sub-cases (4 byte-shifts × 16 within-byte cb patterns) close uniformly via wrapper helpers per byte_shift. spec.sll_poly is complete (only spec.slli_poly + pre-existing Fin-KB sorries remain).
metadata: 
  node_type: memory
  type: feedback
  originSessionId: d13f597f-47d0-47b7-9a65-f20721f2701f
---

When porting `spec.sll_poly` (or analogous SLLI/SLLW/SRL/SRA) from Fin-KB `simp_all`-brute-force to `_poly` over ZMod p, use the **5-layer helper architecture** in `SP1Chips/ShiftLeft/Common.lean`:

1. **Core within-byte helpers** (one per byte_shift k ∈ {0,1,2,3}):
   - `sll_within_byte_shift_poly` (k=0): output `#v[ll_0·v0123, ll_1·v0123+hl_0, ...]`
   - `sll_within_byte_shift_1_poly` (k=1): output `#v[0, ll_0·v0123, ll_1·v0123+hl_0, ll_2·v0123+hl_1]`
   - `sll_within_byte_shift_2_poly` (k=2): output `#v[0, 0, ll_0·v0123, ll_1·v0123+hl_0]`
   - `sll_within_byte_shift_3_poly` (k=3): output `#v[0, 0, 0, ll_0·v0123]`
   
   Each takes generic M, N (with M·N=65536), bounds, and decompositions; concludes `... * M * 2^(16k) % 2^64`.

2. **Case wrappers** (one per cb4,cb5 selector):
   - `sll_close_cb4cb5_zero_case` (cb4=cb5=0)
   - `sll_close_cb4cb5_one_zero_case` (cb4=1, cb5=0)
   - `sll_close_cb4cb5_zero_one_case` (cb4=0, cb5=1)
   - `sll_close_cb4cb5_one_one_case` (cb4=cb5=1)
   
   Each takes (S, M, N) plus h_v_val, h_inner_eq, h_total_eq, original bounds + h_b_dec; bridges `<<<` to `*`, internally normalizes bounds, calls the matching within-byte helper.

**Result (verified 2026-05-12):** `spec.sll_poly` is fully closed — all 64 sub-cases (4 byte-shifts × 16 within-byte cb patterns) close uniformly. Only remaining sorries in `Sll.lean`: `spec.slli_poly` (out of scope) and the pre-existing Fin-KB `spec.sll` with its `stop` marker.

**Key proof step** for each within-byte helper (Common.lean, e.g. line 226 for k=0):
```lean
linear_combination
  (hl0.val + hl1.val * 2^16 + hl2.val * 2^32 + hl3.val * 2^48) * 2^(16k) * h_MN
-- Then: conv_rhs => rw [Nat.mul_assoc, Nat.mod_mul_mod, ← Nat.mul_assoc]
-- Then: rw [h_key, Nat.add_mul_mod_self_right]
```
For k=0 the `* 2^(16k)` factor is `1` and the simpler `rw [Nat.mod_mul_mod, h_key, ...]` works. For k>0, the `conv_rhs` reassociation is needed because `(B mod 2^64) * M * 2^(16k)` requires moving the inner `mod 2^64` past two multiplications.

**Per-sub-case call (~10 lines, identical across all 64 cases except wrapper name + S + M + N + val lemma):**
```lean
· -- cb0..3 = <pattern>: S=<shift_value>
  have hv0123_val : v0123.val = M := by
    have h : v0123 = M := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
    rw [h]; exact val_M_zmod_p
  exact sll_close_cb4cb5_<branch>_case S (by omega) M N (by decide) (by omega) rfl rfl
    hv0123_val
    (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
    lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
    h_b0_dec h_b1_dec h_b2_dec h_b3_dec
```

**Per-byte-shift branch scaffolding** (~40 lines): for each non-zero byte_shift k, derive which `Main[45+k] = 1` (others = 0) via h_su_sum + `linear_combination` contradictions, extract `a_j = lr_?` from `rest` (with appropriate `obtain ⟨_, _, ..., h_a_j_45+k, ..., _rest_other⟩` skipping previous byte_shift conjuncts), then `rw [h_a_j_eq, eq_lr_?]` to expand goal into the byte_shift=k canonical form, then 16-way rcases.

**Linear-combination sign trick (subtle):** for h of form `(LHS = 0 disjunct contradiction)`:
- h : `0 + ... = i` (sum on LHS, e.g. cb4=cb5=0 case): use `linear_combination -h`
- h : `↑N = i` (NatCast LHS, e.g. cb4=0/cb5=1 case): use `linear_combination h` (sign flips)
- h : `1 = i` (literal LHS, e.g. cb4=1/cb5=0 case): use `linear_combination -h`

When ring fails with `2 = 0` residual, the sign is wrong — flip it. The goal-side `(1 : ZMod p) = 0` or `(2 : ZMod p) = 0` and h's LHS-RHS together determine the coefficient.

**Why it works for k > 0** (algebraic intuition): For byte_shift k, the LHS = `2^(16k) * (within-byte-k_LHS_truncated)`. The within-byte helper proves the un-truncated identity. Multiplying both sides by `2^(16k)` mod `2^64` makes the dropped lr_j's vanish (they get shifted to ≥ 2^64). This identity is captured by the `linear_combination ... * 2^(16k) * h_MN` step in each within-byte helper.

**File line counts after full closure:**
- `Sll.lean`: 1294 lines (was 762; +532 lines for the 3 byte-shift branches with 16 sub-cases each, ~10 lines per case + ~40 lines outer scaffolding per branch).
- `Common.lean`: 1209 lines (+450 lines for the 3 new within-byte helpers and 3 new case wrappers).

**Total spec.sll_poly proof structure:**
- Outer setup (~200 lines): destructure cstrs, derive bounds, prepare lr expansions.
- 4 byte-shift branches × (~40 lines scaffolding + 16 × ~10 lines per case) = ~800 lines.
- All-zeros sub-case (kept specialized, ~22 lines).
- Total: ~1000 lines for spec.sll_poly's body.

**Reusable across:** SLLI/SLLW/SLLIW (same constraint shape, possibly slight variations for width=32 in SLLW), SRL/SRA (sign-extension adjustments needed). The 4 byte-shift wrappers are the new infrastructure; the call-site pattern is identical to cb4=cb5=0.
