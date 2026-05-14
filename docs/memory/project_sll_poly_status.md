---
name: shiftleft-poly-migration-status-as-of-2026-05-13
description: All four _poly spec lemmas and all four _poly chip-level correct theorems closed. Remaining work is the Phase 6 Fin-KB collapse — delete spec.{sll,slli,sllw,slliw} and correct_{sll,slli,sllw,slliw} stubs that still carry `stop` markers.
metadata:
  type: project
---

**Current state of ShiftLeft `_poly` migration (as of commit `f5ba642`):**

All eight `_poly` artifacts are **fully closed, no sorries**:

| Layer | sll | slli | sllw | slliw |
|---|---|---|---|---|
| `spec.*_poly` (Sll.lean / Sllw.lean) | ✅ | ✅ | ✅ | ✅ |
| `correct_*_poly` (ShiftLeftChip.lean) | ✅ | ✅ | ✅ | ✅ |

**`lake build SP1Chips.ShiftLeftChip` reports 0 errors.** 25 warnings remain, all pre-existing: 4 `declaration uses sorry` (the Fin-KB `stop` markers, see below) and 21 unused-variable warnings on the cb4_zero / cb4_one branch lemma signatures in `Sllw.lean` (lt_ll2, lt_lh2, lt_ll3, lt_lh3, h_b2_dec, h_b3_dec, eq_lr2, eq_lr3, eq_sllw, h_no_sll — present because sllw byte_shift cases only consume the low HWord, never the high two limbs).

## What's left — the Phase 6 collapse

Four Fin-KB declarations still carry `stop` markers (the in-repo "TEMP" convention that aborts the proof and registers an implicit sorry, used to keep builds fast while `_poly` was being completed):

- `SP1Chips/ShiftLeft/Sll.lean:14` — `spec.sll` (Fin KB, line 97 has the `stop`)
- `SP1Chips/ShiftLeft/Sll.lean:2234` — `spec.slli` (Fin KB, line 2317 `stop`)
- `SP1Chips/ShiftLeft/Sllw.lean:1035` — `spec.sllw` (Fin KB, line 1101 `stop`, plus 1126/1233 secondary stops)
- `SP1Chips/ShiftLeft/Sllw.lean:1166` — `spec.slliw` (Fin KB)

And four Fin-KB chip-level theorems consume these:

- `SP1Chips/ShiftLeftChip.lean:34` — `correct_sll`
- `SP1Chips/ShiftLeftChip.lean:90` — `correct_slli`
- `SP1Chips/ShiftLeftChip.lean:146` — `correct_sllw`
- `SP1Chips/ShiftLeftChip.lean:202` — `correct_slliw`

**Recommended next step:** delete the Fin-KB versions entirely. The `_poly` versions cover all needed correctness — any downstream consumer can be migrated to the `_poly` API. Deletion checklist:

1. Confirm nothing outside `SP1Chips/ShiftLeft*` references the Fin-KB names. Search for `spec.sll`, `spec.slli`, `spec.sllw`, `spec.slliw`, `correct_sll` (without `_poly`) and `correct_sllw`/`correct_slli`/`correct_slliw` across the tree.
2. Remove the four spec lemmas and their `stop` placeholders.
3. Remove the four chip-level theorems (and their `namespace Sll/Slli/Sllw/Slliw` blocks that no longer have content).
4. Also remove the Fin-KB-only helpers in `Common.lean` if they become orphans (`sll_close_cb4cb5_*` already has `_poly` variants — check whether the non-poly versions are still consumed).
5. Drop the 21 unused-variable warnings: thin the branch lemma signatures (`spec.sllw_poly_cb4_zero` and `..._one`) to drop `eq_sllw`/`h_no_sll`/`lt_ll2`/`lt_lh2`/`lt_ll3`/`lt_lh3`/`h_b2_dec`/`h_b3_dec`/`eq_lr2`/`eq_lr3` — none of these are referenced in the branch bodies. Update the two call sites in `spec.sllw_poly` / `spec.slliw_poly`'s outer dispatch.

## What landed in commit `f5ba642`

Three logically separable fixes bundled in one commit:

1. **Fix `spec.sllw_poly_cb4_zero` / `spec.sllw_poly_cb4_one` signature mismatch** (from `7de55d8`). The outer simped `h_su16i` via `[mul_zero, add_zero]`, leaving `Main[46] = 0 ∨ Main[40] = k`, but the branch lemma signatures declared the unsimplified `Main[46] = 0 ∨ Main[40] + Main[41] * 2 * 0 = k`. Aligned the signatures to the simplified form and dropped the now-redundant inner `rw [hcb4]; simp` from each branch body.

2. **Resolve the `↑2` vs `2` cast inconsistency** in the cb_sum_lt bound chain. Lean's elaborator was producing `Main[37] * 2` (`OfNat`) in some `have` declarations and `Main[37] * ↑2` (`Nat.cast`) in others within the same proof, so `omega` couldn't unify the hypothesis with the goal after `rw [ZMod.val_add_of_lt]`. The pattern that worked:

   ```lean
   have h_2_cast : ((2 : ℕ) : ZMod p) = 2 := by push_cast; rfl
   have h_4_cast : ((4 : ℕ) : ZMod p) = 4 := by push_cast; rfl
   have h_8_cast : ((8 : ℕ) : ZMod p) = 8 := by push_cast; rfl
   have h_16_cast : ((16 : ℕ) : ZMod p) = 16 := by push_cast; rfl
   ```

   Then inside every `rw [ZMod.val_add_of_lt]` subgoal:

   ```lean
   all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
              have := h_prev; have := h_curr; have := hp; omega)
   ```

   The `at *` is load-bearing — it normalizes both the hypothesis (carrying the old form) and the goal (carrying the new form) so omega sees identical terms. See `feedback_poly_proof_patterns.md` (and consider linking from there).

3. **Wire `correct_sllw_poly` / `correct_slliw_poly`**, mirroring `correct_sll_poly` / `correct_slli_poly`. The chip-level form difference between `execute_RTYPEW_pure` (`BitVec.setWidth 5 X` shamt) and `execute_RTYPEW_pure_w_poly` (`X.toNat % 32` shamt) is bridged by applying `exec_RTYPEW_pure_bv_to_w_poly` before the `by_cases Main[6] = 0` (not after, like the SLL analog) — otherwise the positive branch never gets the conversion and `rw [← spec_eq]` mismatches.

   For `correct_slliw_poly`, the h_shift_zero claim must use `#v[Main[25], (0 : ZMod p), 0, 0]` (not `#v[Main[25], Main[26], Main[27], Main[28]]`) because `simp_all` in the `Main[6] = 0` branch rewrites `Main[26..28]` to 0 in `spec_eq` (via `bounds_poly`'s `h_imm1` output `h_26, h_27, h_28`) but leaves the in-goal h_shamt_eq form untouched — same quirk as `correct_slli_poly`.

## Helpers in place (`SP1Chips/ShiftLeft/Common.lean`, unchanged this session)

- `sll_within_byte_shift_poly` (byte_shift=0 core), `sll_within_byte_shift_{1,2,3}_poly`
- `sll_close_cb4cb5_{zero,one_zero,zero_one,one_one}_case`
- `sllw_within_byte_shift_poly`, `sllw_within_byte_shift_1_poly`
- `sllw_close_cb4_{zero,one}_case`, `sllw_subcase_cb4_{zero,one}`
- `is_mod_64_poly`, `cancel_mul_65536_poly`, `single_op_poly`, `bounds_poly`, `is_real_eq_one_of_{sll,sllw}`, `ops_U64_b_c_poly`

## File line counts after this session

- `Sllw.lean`: ~1300 lines (was ~1040 at session start; +258 for the outer body of `spec.slliw_poly` and the cast-normalization bridges in both outer lemmas)
- `ShiftLeftChip.lean`: ~560 lines (was ~458; +99 for `correct_sllw_poly` and `correct_slliw_poly`)
- `Sll.lean` and `Common.lean`: unchanged

## Build state

`lake build SP1Chips.ShiftLeftChip`: 0 errors. 25 warnings = 4 pre-existing `sorry` (the Fin-KB `stop` placeholders) + 21 pre-existing unused-variable warnings on the branch lemma signatures.
