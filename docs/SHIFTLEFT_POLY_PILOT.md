# ShiftLeft `_poly` pilot — status

Tracking the in-progress `spec.sll_poly` migration (and its `slli/sllw/slliw` siblings) for the ShiftLeft chip's `_poly` rollup. This is the operation-level bridge proving `Word.toBitVec64_poly #v[a0..a3] = execute_RTYPE_pure_w_poly #v[b..] #v[c..] .SLL` from the polymorphic constraints. Companion to `docs/FIELD_GENERIC.md`.

## Where it lives

All in `SP1Chips/ShiftLeft/Constraints.lean` (single-file work):

- **`spec.sll_poly`** (line 1189) — the actual lemma. Full destructure + 64-way case split + RHS bridge factored. **Case 0/64 (cb0..cb5 = 0, shift = 0) is fully closed end-to-end with all 6 bridge facts derived.** Remaining 63 cases land on `all_goals sorry` at line 1443.
- **`_spec_sll_poly_shift0_omega_test`** (line 1451) — private witness lemma proving the omega-close pattern works for shift = 0 given 6 sorry'd bridge facts. Kept as a reference; can be deleted once `spec.sll_poly` is fully closed.

`lake build SP1Chips` completes successfully. `grep -cE '^(error|warning):' build.log` reports **2** — both `declaration uses sorry`. Drops to 0 once cases 2..64 land and `_spec_sll_poly_shift0_omega_test` is removed.

## What's already factored (outer scope of `spec.sll_poly`, lines ~1196–1318)

These are computed once before the case split, so per-case work skips them:

- `NeZero p` instance + `hp_lt : 131072 < p`
- `bounds_poly` extraction → `hpc, is_U64_b, is_U64_c`
- `Word.lt_cases_of_isU64_poly` → `b0_16..b3_16, c0_16..c3_16`
- `single_op_poly` → `sop_1, sop_2`; derive `h_63_zero : Main[63] = 0`
- Direct `simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly] at cstrs`
- All 35+ `set` aliases (b0..b3, c0..c3, a0..a3, cb0..cb5, ll0..ll3, hl0..hl3, lr0..lr3, v01/v012/v0123, su160..su163, msb, sll, sllw, imm)
- Big `obtain ⟨...⟩ := cstrs` — names: `h_msb_a1, cpu, alu, _one_of_ops, _b_sll, _b_sllw, b_cb0..b_cb5, diff, h_su160..h_su163, b_su160..b_su163, one_of_su16s, eq_v01, eq_v012, eq_v0123, lt_ll0..lt_ll3, lt_lh0..lt_lh3, h_b0_dec..h_b3_dec, eq_lr0..eq_lr3, nw_00..nw_15, _w_00..._w_05, _eq_m64, _h13`
- **RHS bridge** (`← BitVec.toNat_inj` + `execute_RTYPE_pure_w_poly` unfolding + `BitVec.shiftLeft_eq'` + `BitVec.toNat_shiftLeft` + `Word.toBitVec64_poly_toNat_poly is_U64_b` + `Word.toNat_poly_def`)
- `h_setWidth : (BitVec.setWidth 6 (Word.toBitVec64_poly #v[c0..c3])).toNat = c0.val % 64`. **Important**: closes via `change ... % 64 = c0.val % 64; omega`. Uses `c_i_16 < 2^16` bounds and the fact that 64 | 2^16. Per the project lint: use `change`, NOT `show`.
- `h10_val + h10_cast`: `(10 : ZMod p) = ((10:ℕ):ZMod p)`, `((10:ℕ):ZMod p).val = 10` → applied to `diff` to convert `2 ^ ZMod.val 10` literal to `1024`
- **9 ZMod literal distinctness lemmas**: `h_2_ne_0, h_2_ne_1, h_2_ne_3, h_1_ne_0, h_0_ne_1, h_1_ne_2, h_1_ne_3, h_3_ne_0, h_3_ne_1, h_3_ne_2, h_0_ne_2, h_0_ne_3` (all derived from generic `h_zmod_lit_ne`). Used by the post-case-split `simp only` to collapse `K = K'` second disjuncts in `h_su16*` to False.
- `h_real_ne : ¬(sll + sllw = 0)` (from `eq_sll : sll = 1` + `h_63_zero : sllw = 0` + `norm_num`); also `h_sll_ne_zero : sll ≠ 0`.
- 64-way `rcases b_cb0..b_cb5` chain + `simp only [...] at *` substituting concrete cb values, collapsing `K=K'` disjuncts via the distinctness lemmas, reducing `mul_one`/`zero_mul`/`zero_add`/`add_zero`.

## Per-case template (case 0/64 implementation, lines ~1320–1440)

Mechanical for the remaining 63 cases. The case-0 body shows the full chain:

1. **Discharge `¬sll+sllw=0 →` prefix** on `lt_lh*`, `lt_ll*`, `diff`:
   ```lean
   have lt_lh0' := lt_lh0 h_real_ne
   ...
   have diff' := diff h_real_ne
   ```

2. **Reduce ZMod literal constants** in the bound expressions:
   ```lean
   have hZ0 : (0 : ZMod p).val = 0 := ZMod.val_zero
   have h16 : ((16 : ZMod p) - 0).val = 16 := by
     rw [show ((16:ZMod p) - 0) = ((16:ℕ):ZMod p) by push_cast; ring,
         ZMod.val_natCast_of_lt (by omega)]
   rw [hZ0] at lt_lh0' lt_lh1' lt_lh2' lt_lh3'
   rw [h16] at lt_ll0' lt_ll1' lt_ll2' lt_ll3'
   ```
   For non-zero shift cases, reduce `((16 - cb_sum).val = 16 - k)` and `((cb_sum).val = k)` analogously. Each different k requires its own simp.

3. **Derive `hl_i = 0`** (only for k = 0 cases; k > 0 needs cancel_mul_65536_poly). The `lt_lh_i' : hl_i.val < 2^k` becomes `hl_i.val = 0` when k = 0:
   ```lean
   simp only [Nat.pow_zero, Nat.lt_one_iff] at lt_lh0' lt_lh1' lt_lh2' lt_lh3'
   have hl0_eq : hl0 = 0 := (ZMod.val_eq_zero hl0).mp lt_lh0'
   ```

4. **Determine active `su16_j`** flag. After the global `simp only` distinctness pass, `h_su16_other : su_j' = 0` for inactive arms, and `h_su16_active : True` for the active arm (its second disjunct is `K = K` which `or_true` collapses). Then:
   ```lean
   -- For shift = 0 (j = 0): active is su160.
   have h_su160_one : su160 = 1 := one_of_su16s.resolve_left h_real_ne
   have h_su160_ne : su160 ≠ 0 := by rw [h_su160_one]; exact h_1_ne_0
   ```
   For j = 1, 2, 3: same pattern but `one_of_su16s` after `rw [h_su16i_other_zeros]` reduces to `su16j = 1` directly (or with re-association via `linear_combination`).

5. **Chain `v0123 = 2^k`** through eq_v0123, eq_v012, eq_v01:
   ```lean
   have h_v0123_one : v0123 = 1 := by   -- for k = 0
     have h := eq_v0123; rw [eq_v012, eq_v01] at h; exact h
   ```
   For k > 0, the chain produces `v0123 = some_expr`; need to compute the expression to `2^k` (e.g., for cb0=1: `v0123 = (1+1)*(1) * 1 * 1 = 2`).

6. **Substitute `v0123 = 2^k`** in `h_b_*_dec` and `eq_lr_*`:
   ```lean
   rw [h_v0123_one] at h_b0_dec h_b1_dec h_b2_dec h_b3_dec eq_lr0 eq_lr1 eq_lr2 eq_lr3
   ```

7. **Derive `b_i = ll_i`** (k = 0) or `b_i = hl_i*M + ll_i` (k > 0 via `cancel_mul_65536_poly`):
   ```lean
   have h_b0 : b0 = ll0 := by
     have h := h_b0_dec; rw [hl0_eq] at h; linear_combination h
   ```
   For k > 0: `apply cancel_mul_65536_poly (by decide : (2^k:ℕ) ∣ 65536) (by decide : 0 < 2^k) at h_b0_dec` first, then derive `b_i.val = hl_i.val * (65536/2^k) + ll_i.val`.

8. **Reduce `eq_lr_*`** to concrete forms after `hl` substitution:
   ```lean
   simp only [mul_one] at eq_lr0 eq_lr1 eq_lr2 eq_lr3
   rw [hl0_eq] at eq_lr1; rw [hl1_eq] at eq_lr2; rw [hl2_eq] at eq_lr3
   simp only [zero_add, add_zero] at eq_lr1 eq_lr2 eq_lr3
   ```

9. **`a_i` values from active `nw_*`** (3-way disjunction `sll = 0 ∨ su16_active = 0 ∨ a_i = expr`):
   ```lean
   -- For su160 active: nw_00..nw_03 give a0..a3 = lr0..lr3.
   have h_a0_eq : a0 = lr0 :=
     (nw_00.resolve_left h_sll_ne_zero).resolve_left h_su160_ne
   ```
   For su161 active: nw_04..nw_07 (a0=0, a1=lr0, a2=lr1, a3=lr2). For su162: nw_08..nw_11 (a0=a1=0, a2=lr0, a3=lr1). For su163: nw_12..nw_15 (a0=a1=a2=0, a3=lr0).

10. **Derive `a_i.val = b_i.val`** (or shifted version per j) by chaining a_i → lr_{i-j} → ll_{i-j-1}+hl_{i-j-2} → b_{i-j-1}:
    ```lean
    have h_a0_val : a0.val = b0.val := by rw [h_a0_eq, eq_lr0, ← h_b0]
    ...
    ```

11. **`Word.isU64_poly #v[a0..a3]`** — case-by-case using a_i.val expressions and b_i.val < 2^16:
    ```lean
    have h_a_isU64 : Word.isU64_poly (#v[a0, a1, a2, a3] : Word (ZMod p)) := by
      apply Word.isU64_of_cases_poly
      · simp only [Vector.getElem_mk, ...]
        rw [h_a0_val]
        have := b0_16; simp only [Vector.getElem_mk, ...] at this
        exact this
      · ... (similar for a1, a2, a3)
    ```
    For j > 0 (some a_i = 0), use `ZMod.val_zero` instead of b_i_16.

12. **`c0.val % 64 = (k + 16*j)`** via `is_mod_64_poly`:
    ```lean
    -- For shift = 0 (m = 0):
    have h_c_mod : c0.val % 64 = 0 := by
      have hm : ((0 : ZMod p)).val < 64 := by rw [hZ0]; omega
      have hdiff' : ((c0 - 0) * (64 : ZMod p)⁻¹).val < 1024 := by simpa using diff'
      have := is_mod_64_poly hm hdiff'
      rw [hZ0] at this; exact this
    ```
    For shift = k+16j: `m = (k+16j : ZMod p)`. Need `m.val = k + 16*j` (via `ZMod.val_natCast_of_lt`).

13. **omega close**:
    ```lean
    rw [Word.toBitVec64_poly_toNat_poly h_a_isU64, Word.toNat_poly_def]
    rw [h_c_mod]
    simp only [Nat.pow_zero, Nat.mul_one, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ, Nat.reduceAdd]
         at b0_16 b1_16 b2_16 b3_16 ⊢
    omega
    ```
    For shift > 0: `Nat.pow_zero, Nat.mul_one` won't fire (shift = `2^(k+16j)`, not `2^0`); use `Nat.reducePow` or explicit `2^k` literal handling.

## Variation across cases

| Axis | Range | Affects |
|---|---|---|
| **j** = cb4 + 2·cb5 | 0..3 | active su16_j → which `nw_*` group → a_i mapping (a_i = 0 for i < j, a_i = lr_{i-j} for i ≥ j) |
| **k** = cb0 + 2·cb1 + 4·cb2 + 8·cb3 | 0..15 | shift kernel size; v0123 = 2^k; bounds `hl_i.val < 2^k`, `ll_i.val < 2^(16-k)`; for k > 0 need `cancel_mul_65536_poly` to extract `b_i = hl_i*(65536/2^k) + ll_i` |
| Total shift | 0..63 | `c0.val % 64 = k + 16*j` |

64 cases total = 4 j-groups × 16 k-values. Within a j-group, the active `nw_*` is fixed; within a k-value, the v0123 expression and hl/ll bounds are fixed. The proof body is structurally identical; only the substitutions and constants differ.

## Next steps to continue

1. **Add cases 2..64 one at a time** following the case-0 template above. Suggested order: by j-group (j=0 first since su160 nw_*s are simplest), then by k within each group.
2. **For k > 0 cases**: the `cancel_mul_65536_poly` step is the main novelty. It takes `(k_pow : (2^k : ℕ) ∣ 65536)` and `(0 < 2^k)`, both `by decide`-able for concrete k. Apply via `apply cancel_mul_65536_poly (by decide) (by decide) at h_b_i_dec`.
3. **For j > 0 cases**: `one_of_su16s.resolve_left h_real_ne` gives `su160 + su161 + su162 + su163 = 1`. After `rw [h_su16_inactive_zeros]` substitutions, this reduces to `su16_active = 1` (or with `linear_combination` if rearrangement is needed).
4. **Once all 64 cases close**: drop the `_spec_sll_poly_shift0_omega_test` private lemma (it was a witness for the close pattern, no longer needed).
5. **Then replicate to `spec.slli_poly`**: identical core, only differs in the I-type immediate handling — see `spec.slli` (lines 637–740 in Constraints.lean) for the Fin KB shape; the `_poly` form needs `sp1_op_c_imm_poly` for the shift count (already exists, line 1168).
6. **Then `spec.sllw_poly` and `spec.slliw_poly`**: 32-bit truncation variants. Need `is_mod_32_poly` (mirrors `is_mod_64_poly` at line 1075 with 64→32, 1024→2048 budget) — ADD it just above `is_mod_64_poly` when starting the sllw arm.

## Key infrastructure references

- `cancel_mul_65536_poly` — `SP1Chips/ShiftLeft/Constraints.lean:1024`
- `single_op_poly` — `:1053`
- `is_mod_64_poly` — `:1075`
- `bounds_poly` — `:1107`
- `Word.toBitVec64_poly_toNat_poly` — `SP1Foundations/Word.lean:496`
- `Word.isU64_of_cases_poly` — `:348`
- `Word.lt_cases_of_isU64_poly` — `:361`
- `BitVec.shiftLeft_eq'` — Lean 4.29 `Init/Data/BitVec/Lemmas.lean:2040` (BitVec-shift-by-BitVec → BitVec-shift-by-Nat bridge)
- `execute_RTYPE_pure_w_poly` — `SP1Foundations/SailM.lean:414` (NOT `execute_RTYPE_pure_w` — that's the Fin KB form and forces a `.cast` through Fin KB on operands)

## Constraint shape gotchas

- `h_b_i_dec` after `simp` is `b_i * v0123 = hl_i * 65536 + ll_i * v0123` — an *equation*, not a disjunction. (Earlier draft had it as disjunction; that was a wrong-edit transient.)
- `nw_*` are 3-way disjunctions: `sll = 0 ∨ su16_j = 0 ∨ a_i = expr`. Use `.resolve_left h_sll_ne_zero` then `.resolve_left h_su16_active_ne` (in that order — `sll = 0` is the first disjunct).
- `eq_v01`, `eq_v012`, `eq_v0123` form a chain: each defines the next. `simp only` does NOT chain them; explicit `rw [eq_v012, eq_v01] at eq_v0123` (or sequentially apply at h) is needed.
- `lt_lh*`, `lt_ll*`, `diff` carry a `¬sll+sllw=0 →` prefix — must be discharged via `h_real_ne` before use.
- The `simp only` distinctness pass at *all* hypotheses (`at *`) handles `h_su16*` second disjuncts. Don't skip the `h_0_ne_*` and `h_*_ne_0` symmetric pairs — both orientations are needed since the disjunct can appear as either `K = K'` or `K' = K`.
- `set_option maxHeartbeats N in <decl>` requires a one-line `--` comment between the `set_option` and the declaration; otherwise the lint fires (`Please, add a comment explaining...`).

## Build + test

- Per-file: `lake env lean SP1Chips/ShiftLeft/Constraints.lean`
- Library: `lake build SP1Chips`
- Project policy: `grep -cE '^(error|warning):' build.log` must be 0. Currently 2 (the two sorries). Drops to 0 after cases 2..64 land + `_spec_sll_poly_shift0_omega_test` removed.

## Local plan file

`~/.claude/plans/make-a-plan-to-graceful-petal.md` — original plan from the planning session that started this work; references the template patterns from BranchChip's `_poly` rollup and Mul's `core_mulw_poly`. Not in-repo; sync separately if continuing on another machine.
