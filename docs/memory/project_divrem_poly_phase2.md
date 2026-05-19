---
name: divrem-poly-phase-2-core-sorries-complete-2026-05-14
description: "All 3 inner sorries of `div_rem_poly` closed (h_sign, h_abs, h_prod); div_rem_poly is sorry-free; 8 chip-level correct_*_poly stubs remain in DivRemChip.lean"
metadata: 
  node_type: memory
  type: project
  originSessionId: 93420f78-893c-4c42-b56b-fa3d06d8314d
---

**Phase 2 of the DivRem `_poly` migration COMPLETE 2026-05-14** (3 commits):

`SP1Chips/DivRem/DivRem.lean`'s `div_rem_poly` (signed 64-bit core) is now sorry-free. All 4 cores done:

| Core | File | Status |
| --- | --- | --- |
| `divu_remu_poly` | `DivuRemu.lean:337` | ✅ |
| `divuw_remuw_poly` | `DivuwRemuw.lean:314` | ✅ |
| `divw_remw_poly` | `DivwRemw.lean:489` | ✅ |
| `div_rem_poly` | `DivRem.lean:883` | ✅ (this phase) |

**Commits this phase**:
- `3d996c9` — h_sign (msb_b=0/1 case-split, 3-step ZMod.val_add_of_lt chain under Fact (2^24 < p) for the 4-limb r-sum=0 derivation)
- `e4d7a83` — h_abs (4-way rcases × b_rem_neg/b_c_neg; case 4 has 4 sub-cases handling the -2^63 edge cases that the HWord-template omega-shortcut doesn't handle at 64-bit)
- `c01ebd4` — h_prod (Stage A: combine_MUL_MULH_poly + Word.extend_true_is_signExtend_poly + BitVec.toInt_signExtend_of_le + Int.bmod_eq_of_le; Stage B: 8-limb DWord carry chain from divu_remu_poly with msb_b/msb_rem * 65535 in upper limbs)

**Project state after this phase**:
- 21 chips have at least one `correct_*` (unchanged — chip-level work is Phase 3-4).
- `lake build`: 0 errors, 8 warnings — all 8 are `SP1Chips/DivRemChip.lean:458/468/478/488/498/508/518/528 'declaration uses sorry'` stubs for `correct_<variant>_poly` × 8 (8 variants: div/divu/rem/remu/divw/remw/divuw/remuw).
- `#print axioms DivRem.div_rem_poly` lists only standard axioms (Classical.choice, propext, Quot.sound, plus combine_MUL_MULH_poly's bv_decide axiom) — no sorryAx.

**Remaining work for DivRem chip migration** (Phase 3-4 of `make-a-plan-to-iterative-snail.md`):
1. **Phase 3 — 8 `spec.<variant>_poly` wrappers** in `DivuRemu/DivuwRemuw/DivwRemw/DivRem.lean` (~200 lines each). Mechanical mirror of Fin KB `spec.<variant>` with `_poly` substitutions. Plan ordering: easy unsigned first (`spec.divu_poly`, `spec.remu_poly`).
2. **Phase 4 — 8 chip-level `correct_<variant>_poly`** in `DivRemChip.lean:458-536`. Fill the existing sorry stubs. Pattern: `correct_prologue_facts_poly` for variant-independent prep + per-arm refinement of op_b/c < 32 via opcode reduction + `spec.<variant>_poly` invocation. Mirror MulChip:correct_mul_poly.

**Key reusable patterns from Phase 2** (worth recording for Phase 3-4 and similar future ports):

- **Post-prologue `eq_msb_*` form**: After `simp [rem_*, c_*, b_msb_*] at *`, `eq_msb_b/c/rem` collapse from `is_word = 0 → msb_b = if 32768 ≤ b3 then 1 else 0` to a direct `(¬)32768 ≤ b3/c3/r3` form (the antecedent already discharged with `is_word = 0` propagated). Use them via `apply eq_msb_b` + `change (32768 : ZMod p).val ≤ b3.val; rw [val_32768_zmod_p]; exact h` pattern (the HWord template's idiom). Do NOT try `rw [if_pos hge] at eq_msb_b; exact zero_ne_one eq_msb_b` — that's the pre-simp form that's no longer present.

- **`unfold Word.toInt_poly` beats `rw [Word.toInt_poly, if_neg ...]` when both LHS and RHS use Word.toInt_poly**: the `rw [name]` form only unfolds the first occurrence. Use `unfold Word.toInt_poly` (unfolds all) then `rw [if_neg hr_nneg, if_neg hac_nneg]` to handle both ifs.

- **`simp at *` after `simp [rem_*, c_*] at *` is redundant** for the case-1/2/3/4 setup — it returns "simp made no progress" and indicates the prior simp already finished the work.

- **For Word width, the HWord template's `· omega` close (case 2 then-branch on `Word.toInt_poly c = -2^63`) DOESN'T work** because Word.toInt's bounds are [-2^63, 2^63), making `= -2^63` consistent (HWord's [-2^31, 2^31) makes it contradictory). Use explicit `rw [is_c_lb]; rw [show |(-2^63 : ℤ)| = 2^63 from by norm_num]; rw [abs_of_nonneg hr_int_nneg]; exact Word.toInt_poly_ub is_U64_r` instead.

- **`combine_MUL_MULH_poly` gives the signed product directly** (no need for separate `eq_eq` / `eq_ec` matching q/c's sign extension to `msb_quot * 65535` / `msb_c * 65535`): q and c sign-extension is internal to the lemma's conclusion `(Word.extend_poly q true).toBitVec128_poly * (Word.extend_poly c true).toBitVec128_poly`. Only need eq_eb (for b) and eq_er (for r).

- **`rw [eq_comm] at nof_eq_ctqpr4..7`** is required BEFORE `rw [← add_sub_right_comm]` for the upper limbs, because they're stated as `LHS_with_subtraction = RHS_simple` (e.g., `ctq4 + msb_rem * 65535 - cry4 * 65536 + cry3 = msb_b * 65535`) and `← add_sub_right_comm` only matches the `LHS_simple = RHS_with_subtraction` form expected by `div_mod_decomposition_w_poly`.

Plan files: `make-a-plan-to-dapper-muffin.md` (this phase), `make-a-plan-to-iterative-snail.md` (full plan).

## Phase 3 attempt 2026-05-14: spec.divu_poly stubbed with documented blockers

Mechanical port of Fin KB `spec.divu` body (~250 lines) attempted; commit `99cf51e` has the stub + 240-line commented-out draft. Three structural blockers surfaced that need coordinated fixes before any Phase 3 wrapper closes:

1. **NatCast normalization** (Fix attempted via `simp only [Nat.cast_one]` — works in isolation): chip constraints emit `↑(1 : ℕ) - is_word` (NatCast'd by the constraint compiler's parametric-`F` emission), while `divu_remu_poly`'s signature uses literal `1 - is_word`. Resolution: insert `simp only [Nat.cast_one] at eq_lb2 eq_lc2 ... eq_is_real_not_word eq_b_neg_not_overflow ... eq_maco10 ... eq_rcm` after the U16MSB applies block.

2. **U16MSB output form mismatch** (Fix attempted via Prop-eq bridge — works in isolation): `U16MSBOperation.spec.gen_poly` returns `msb = if a.val ≥ 32768 then 1 else 0` (Nat-level), `divu_remu_poly` expects `msb = if (32768 : ZMod p) ≤ a then 1 else 0` (ZMod-level). Resolution: add `msb_bridge_eq : ∀ a, ((32768 : ZMod p) ≤ a) = (a.val ≥ 32768)` (proved via `propext` + `change` + `val_32768_zmod_p`), then `simp only [← msb_bridge_eq] at eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot`.

3. **`set is_word` alias trailing-arm reduction** (BLOCKER — Fin KB's `simp_all [-h_is_divu]` does this implicitly; _poly's `simp [h_is_divu, z0..z6] at *` does NOT): the trailing `all_goals` arms include goals like `Word.isU64_poly #v[c0, c1, c2 * (1 - is_word) + msb_c * (is_div + ...) * is_word * 65535, ...]`. After substituting off-variants to 0, this should reduce to `Word.isU64_poly #v[c0, c1, c2, c3] = is_U64_c`, but `is_word` (a `set` alias for `is_divw + is_remw + is_divuw + is_remuw`) doesn't unfold under `simp` (mathlib `set` introduces a let-bound def, not auto-unfolded). Fix attempted: each `· exact is_U64_c` arm (3 occurrences: arms 6, 16, 18) becomes `· simp [is_word]; exact is_U64_c` to force unfold. NOT YET VERIFIED — needs build iteration.

After these 3 fixes, `spec.divu_poly` should close. Same 3 patterns apply to all 8 Phase 3 wrappers (`spec.divu_poly`, `spec.remu_poly`, `spec.div_poly`, `spec.rem_poly`, `spec.divw_poly`, `spec.remw_poly`, `spec.divuw_poly`, `spec.remuw_poly`).

Pickup state for next focused session: revive the draft body from `DivuRemu.lean`'s commented-out block (commit `99cf51e`); apply fixes 1+2 (mechanical insertions) + fix 3 (try `· simp [is_word]; exact is_U64_c` for the 3 trailing arms); rebuild (~2-3 min cycle).

## Phase 3 attempt 2 (2026-05-14): all 3 fixes applied + 4th blocker found

Revived draft body + applied fixes 1/2/3 (NatCast normalization, msb_bridge_eq, `simp [is_word]` for 3 trailing arms). Build failed with **18 unsolved trailing goals** at line 1221:

**4. Trailing-arm shape mismatch** (NEW BLOCKER): `divu_remu_poly`'s body emits goals with shapes that differ from `divu_remu`'s. Examples observed:
- `Word.isU64_poly #v[ar0, ar1, ar2, ar3]` (×2)
- `Word.isU64_poly #v[is_c_0 + (1 - is_c_0) * ac0, (1 - is_c_0) * ac1, (1 - is_c_0) * ac2, (1 - is_c_0) * ac3]` (the `maco` form)
- `Word.isU64_poly #v[r0, r1, rbc2, rbc3]` (with `rbc` not `r`)
- `Word.isU64_poly` of the sign-extended c form (`c2 * (1 - is_word) + msb_c * (...) * is_word * 65535`)
- `Word.isU64_poly #v[ac0, ac1, ac2, ac3]`
- `q1.val < 65536` / `r1.val < 65536` / `c1.val < 65536` / `b1.val < 65536` (single-limb bounds, ×4)
- `r3.val < 65536` / `c3.val < 65536` / `b3.val < 65536` (single-limb bounds, ×3)
- `Word.isU64_poly #v[q0, q1, qbc2, qbc3]` (with `qbc` not `q`, ×2)
- Several more `Word.isU64_poly` forms

These differ from Fin KB's `divu_remu` trailing goals because (a) my `set is_word := ...` alias doesn't unfold the way Fin KB's analog does and (b) `divu_remu_poly`'s body has additional internal isU64 derivations the Fin KB version doesn't (visible from `Word.isU64_of_cases_poly <;> simpa` at lines ~580-582 of `DivuRemu.lean`).

**Resolution requires per-arm reshape**: not a mechanical substitution. Each of 18 trailing arms needs its tactic adapted for the new goal shape. The arms `· apply Word.isU64_of_cases_poly <;> simp <;> omega` work for plain-limb goals (q/r/b/c bounds). The arms with `rbc`/`qbc`/`maco`/`lc-form` need new handling — likely `simp [rbc2, rbc3, qbc2, qbc3, maco10, maco11, maco12, maco13]` to unfold the `set` aliases, then the existing tactic. Plus the bound-goals (`q1.val < 65536` etc.) need `· exact u16_q1` style direct-from-hypothesis discharges (the hypotheses `u16_q0..3, u16_r0..3, u16_c0..3, u16_b0..3` exist after the destructure).

Net: porting `spec.divu_poly` requires not just the 3 known fixes but also full rewrite of the 18 trailing arms. Total scope per Phase 3 wrapper: ~300 lines (vs my initial estimate of ~250). Across 8 wrappers: ~2400 lines.

## Phase 3 attempt 3 (2026-05-14): kitchen-sink closer failed, reverted

Tried `all_goals try first | exact ... | apply Word.isU64_of_cases_poly <;> first | ...` covering ~20 alternatives (every u16_X exact, every is_U64_X exact, isU64_of_cases_poly + branches). Build still failed with same 18 unsolved goals. Two hypotheses:

1. The `try` swallows ALL failures including legitimate ones — so even if a `first` chain partially succeeds and leaves sub-goals, `try` silently ignores it. Net effect: no progress on any of the 18 goals.

2. The prior `simp [h_is_divu, z0..z6, is_word, eq_is_word] at *` may be leaving the u16_X/is_U64_X hypotheses in unexpected forms — the goals reference `rbc2`, `qbc2`, `is_c_0 + (1-is_c_0) * ac0`, `c2 * (1-is_word) + msb_c * (...) * 65535` etc. that don't match u16_X / is_U64_X's literal form.

The fundamental issue: `divu_remu_poly`'s body produces 18 trailing goals with structurally specific shapes that need targeted tactics — not coverable by a generic kitchen-sink. Each arm needs to be matched 1:1 with a specific tactic.

**Status**: Reverted to committed stub state (99cf51e). Phase 3 spec.divu_poly close requires:
- Interactive (non-loop) debugging session to inspect each of the 18 goals' shape post-simp.
- Per-arm tactic design, likely 4-8 lines each (50-150 lines total just for trailing arms).
- Plus the documented fixes 1+2+3.

Realistic estimate for one wrapper close: 4-8 hours of focused work. Across 8 wrappers, the patterns share so the second through eighth could go faster (~1 hour each).

## Phase 3 attempt 4 (2026-05-14): spec.divu_poly 17/18 arms closed

Through ~12 build iterations, ported the full `spec.divu_poly` body with 4 structural fixes for _poly infrastructure mismatches (commits `fdf16fc`, `3f0bc07`):

1. **NatCast bridge** (`exact_mod_cast`): on `eq_lc2/3, eq_lb2/3` and `eq_b_neg_not_overflow / eq_not_b_neg_not_overflow` during the `specialize` chain. Closes the `↑(1 : ℕ) - is_word` vs `1 - is_word` mismatch from the constraint compiler's parametric-F emission.

2. **U16MSB bridge** (`msb_bridge_eq` + `simp only`): converts U16MSB's `a.val ≥ 32768` output to `(32768 : ZMod p) ≤ a` form expected by `divu_remu_poly`.

3. **`b_is_real_not_word'` derivation**: replace Fin-KB's `omega` with `linear_combination ±h` (4 alternatives in `first` chain since simp_all may flip arm direction).

4. **Pre-unpacked b/c bounds**: `have ⟨hc0_lt, hc1_lt, hc2_lt, hc3_lt⟩ := Word.lt_cases_of_isU64_poly is_U64_c` (same for b) before the trailing `all_goals` so omega has hc_i_lt / hb_i_lt directly.

Trailing 18-arm closer (minimal — replaces the kitchen sink which had 21 unused-tactic warnings):
```lean
all_goals first
  | (rw [← this, eq_d_a0, eq_d_a1, eq_d_a2, eq_d_a3])     -- main equality
  | omega                                                   -- single-limb bounds
  | (apply Word.isU64_of_cases_poly <;> simp_all; done)    -- most isU64 forms
  | sorry                                                   -- 1 maco-form arm
```

The 18th arm (`Word.isU64_poly #v[is_c_0 + (1-is_c_0)*c0, ...]` after `is_c_0 = if c's all zero then 1 else 0` unfolding) needs:
- `apply Word.isU64_of_cases_poly` (produces 4 sub-goals with if-expressions in `.val` argument).
- `split_ifs` on each sub-goal to case-split on the if (cases: c's all zero → expr = 1; else → expr = c_i).
- `simp_all` + `omega` to close each case.

Combining all three into one `first` alternative breaks because `split_ifs` fails on sub-goals from non-maco isU64 forms (no if to split). A correct fix needs either (a) a `try split_ifs` variant (untested), (b) a dedicated `· ...` for the maco arm position (requires identifying its position in the 18-arm sequence), or (c) reshaping `divu_remu_poly`'s signature to take `Word.isU64_poly` of the maco form as an input rather than producing it as a trailing obligation.

**State after Phase 3 attempt 4**: `lake build` green, 9 warnings (8 pre-existing DivRemChip stubs + 1 spec.divu_poly maco-arm sorry). Substantial progress vs the bare-stub state, with all infrastructure issues resolved.
