---
name: shiftleft-poly-migration-status-as-of-2026-05-13
description: ShiftLeft `_poly` migration is complete. All four spec.*_poly lemmas, all four correct_*_poly chip theorems, AND the Phase 6 collapse have landed — Fin-KB versions deleted. `lake build SP1Chips.ShiftLeftChip` is fully clean (0 errors, 0 warnings).
metadata:
  type: project
---

**ShiftLeft `_poly` migration is complete (as of commit `cfa6c8d`).**

All `_poly` artifacts are closed, **Phase 6 collapse has landed**, and `lake build SP1Chips.ShiftLeftChip` reports **0 errors, 0 warnings**.

## What's in the codebase now

| Artifact | Location | Status |
|---|---|---|
| `spec.sll_poly` | `SP1Chips/ShiftLeft/Sll.lean` `section sll_poly` | ✅ closed |
| `spec.slli_poly` | `SP1Chips/ShiftLeft/Sll.lean` `section sll_poly` | ✅ closed |
| `spec.sllw_poly` | `SP1Chips/ShiftLeft/Sllw.lean` `section sllw_poly` | ✅ closed |
| `spec.slliw_poly` | `SP1Chips/ShiftLeft/Sllw.lean` `section sllw_poly` | ✅ closed |
| `correct_sll_poly` | `SP1Chips/ShiftLeftChip.lean` `namespace Sll.Poly` | ✅ closed |
| `correct_slli_poly` | `SP1Chips/ShiftLeftChip.lean` `namespace Slli.Poly` | ✅ closed |
| `correct_sllw_poly` | `SP1Chips/ShiftLeftChip.lean` `namespace Sllw.Poly` | ✅ closed |
| `correct_slliw_poly` | `SP1Chips/ShiftLeftChip.lean` `namespace Slliw.Poly` | ✅ closed |

## What's gone (Phase 6 collapse, commit `cfa6c8d`)

Net diff: **-985 / +16** across 5 files. Deletions:

- **`SP1Chips/ShiftLeftChip.lean`**: `namespace Sll`, `Slli`, `Sllw`, `Slliw` (Fin-KB chip-level correctness theorems and their `spec_*` / `sp1_*` helpers).
- **`SP1Chips/ShiftLeft/Sll.lean`**: `section sll` and `section slli` (Fin-KB `spec.sll` / `spec.slli` — both had `stop` markers).
- **`SP1Chips/ShiftLeft/Sllw.lean`**: `section sllw` and `section slliw` (Fin-KB `spec.sllw` / `spec.slliw` — both had `stop` markers).
- **`SP1Chips/ShiftLeft/Constraints.lean`**: `allHold_constraints_iff` (non-poly variant).
- **`SP1Chips/ShiftLeft/Common.lean`**: Fin-KB orphans `is_real`, `cancel_mul_65536`, `is_mod_64`, `is_sll`/`is_sllw`/`is_slli`/`is_slliw`, `single_op`, `sll_real`/`sllw_real`, `bounds`, and the five `sp1_op_a`/`sp1_op_b`/`sp1_op_c`/`sp1_op_c_imm`/`sp1_op_c_imm_w` getters. Also three poly orphans that fell out: `is_real_poly`, `sll_real_poly`, `sllw_real_poly` (only the deleted Fin-KB lemmas had referenced them).

Also thinned the `spec.sllw_poly_cb4_zero` / `spec.sllw_poly_cb4_one` branch lemma signatures: dropped the 10–11 unused parameters (`eq_sllw`, `h_no_sll`, `lt_ll2/3`, `lt_lh2/3`, `h_b2_dec`, `h_b3_dec`, `eq_lr1/2/3` — the sllw byte-shift cases only touch the low HWord, so high-limb hypotheses were never consumed). Updated call sites in `spec.sllw_poly` and `spec.slliw_poly` accordingly; dropped the correspondingly orphaned `have lt_ll2 := lt_ll2' h_sum_ne` lines.

## Reusable infrastructure (kept)

In `SP1Chips/ShiftLeft/Common.lean`:

- **Within-byte helpers** (`sll_within_byte_shift_{poly,1_poly,2_poly,3_poly}`, `sllw_within_byte_shift_{poly,1_poly}`)
- **Case wrappers** (`sll_close_cb4cb5_{zero,one_zero,zero_one,one_one}_case`, `sllw_close_cb4_{zero,one}_case`, `sllw_subcase_cb4_{zero,one}`, `sllw_a2_a3_eq_msb_byte`)
- **Cast/bound infrastructure** (`is_mod_64_poly`, `cancel_mul_65536_poly`, `single_op_poly`, `bounds_poly`, `is_real_eq_one_of_sll`/`sllw`, `ops_U64_b_c_poly`, `sll_or_sllw_of_real`)
- **Opcode predicates** (`is_sll_poly`, `is_sllw_poly`, `is_slli_poly`, `is_slliw_poly`)
- **Operand getters** (`sp1_op_a_poly`, `sp1_op_b_poly`, `sp1_op_c_poly`, `sp1_op_c_imm_poly`, `sp1_op_c_imm_w_poly`)

## Key landmines for the next chip migration

1. **Lean elaboration introduces inconsistent `↑N` Nat casts** in cb_sum bound chains. Use bridge lemmas + `simp only [...] at *` to normalize:

   ```lean
   have h_2_cast : ((2 : ℕ) : ZMod p) = 2 := by push_cast; rfl
   have h_4_cast : ((4 : ℕ) : ZMod p) = 4 := by push_cast; rfl
   -- ...
   rw [ZMod.val_add_of_lt]
   all_goals (simp only [h_2_cast, h_4_cast, h_8_cast, h_16_cast] at *
              have := h_prev; have := h_curr; have := hp; omega)
   ```

   The `at *` is load-bearing — normalizes both hypothesis and goal so omega sees identical terms. (Documented in `feedback_poly_proof_patterns.md`.)

2. **Outer chip-level `correct_*_poly` form-bridging.** The chip-level `execute_RTYPEW_pure` (BitVec `setWidth 5 X` shamt) and the spec-level `execute_RTYPEW_pure_w_poly` (Nat `X.toNat % 32` shamt) differ syntactically. Apply `exec_RTYPEW_pure_bv_to_w_poly` **before** the `by_cases Main[6] = 0` (not after) — otherwise the positive branch keeps the un-bridged form and `rw [← spec_eq]` mismatches. For the imm variant (`correct_slliw_poly`), `simp_all` rewrites `Main[26..28]` to `0` in `spec_eq` via `h_imm1`'s outputs; the `h_shift_zero` claim must use `#v[Main[25], (0 : ZMod p), 0, 0]` (matching `spec_eq`'s post-simp form), not `#v[Main[25..28]]`.

3. **3-lemma decomposition pattern** (used by sllw_poly's outer + cb4_zero/cb4_one branch lemmas): keeps each piece below elaboration heartbeat limits. Apply when the inlined 64-way split times out.
