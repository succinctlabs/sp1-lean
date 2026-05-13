---
name: divrem _poly migration progress (as of 2026-05-11 late)
description: BranchChip + MulChip Fin-KB-vs-_poly hybrid collapsed to _poly only (-963 LoC); ShiftLeft/ShiftRight remain Fin-KB-only and DivRem still has 11 sorries
type: project
originSessionId: caa2556b-4a1f-4fb4-974c-e8f4426ced0c
---

**Project-wide migration state (audited 2026-05-11):**

| Status | Count | Chips |
|---|---|---|
| ZMod p only (done) | 19 | Add, Addi, Addw, Bitwise, Branch (newly), Jal, Jalr, 4×Load, LoadX0, Lt, Mul (newly), 4×Store, Sub, Subw, UType |
| Hybrid (both forms) | 1 | DivRem (1 Fin-KB theorem + 8 _poly stubs with sorry) |
| Fin KB only (not migrated) | 2 | ShiftLeft, ShiftRight (DivRem-style file split landed 2026-05-11; per-opcode files in place, ready for _poly migration) |

**ShiftLeft/ShiftRight file layout (post-2026-05-11 split):**
- `SP1Chips/ShiftLeft/{Constraints,Common,Sll,Sllw}.lean` — Constraints holds only autogen + iff; Common has `is_real`, `is_*` opcode preds (Fin KB + _poly siblings interleaved), `field_arithmetic`, `bounds`, `operands`; Sll = sll+slli specs, Sllw = sllw+slliw specs.
- `SP1Chips/ShiftRight/{Constraints,Common,Srl,Srlw,Sra,Sraw}.lean` — same shape, 4 opcode files pair reg+imm (Srl=srl+srli, Srlw=srlw+srliw, Sra=sra+srai, Sraw=sraw+sraiw). Each opcode file holds a private `spec.X_common` core + thin reg/imm wrappers.
- Each `_poly` def lives immediately next to its Fin KB sibling in Common.lean (no separate `poly_helpers` section). User preference: paired siblings for side-by-side migration reads.

**This session (2026-05-11 late) — Branch + Mul collapse:**

- `SP1Chips/BranchChip.lean`: 2104 → 1428 lines (−676). Deleted: `branch_addr_eq` lemma + `close_branch_addr_eq` macro + Fin KB `variable`/`sp1_op_a`/`sp1_op_b`/`sp1_imm`/`sp1_branch` + 6 Fin KB `correct_b{eq,ne,lt,ge,ltu,geu}` theorems.
- `SP1Chips/MulChip.lean`: 757 → 471 lines (−286). Deleted: 5 Fin KB namespaces `Mul`/`Mulh`/`Mulhu`/`Mulhsu`/`Mulw` (with their `spec_X`, `sp1_X`, `correct_X` triples) + the stale "Mirror the Fin KB" docstring.
- Both build clean (33s/34s) with 0 new errors/warnings. Full `lake build` 0 errors, 10 warnings — all 10 are the pre-existing DivRem sorries.
- Method: `sed -i` with bottom-up line ranges (Edit's exact-string match too fragile for 6 × 100-line block deletions). Backed up before deletion.
- Naming: `_poly` suffix preserved (matches user-selected "keep only _poly" option); did NOT rename to AddChip's no-suffix style. Renaming to `correct_mul` style would be a separate follow-up.

**Remaining 11 DivRem sorries unchanged:**
- 8 chip stubs in `SP1Chips/DivRemChip.lean` (lines 458, 468, 478, 488, 498, 508, 518, 528) — blocked by qbc/lc bridge layer
- 2 witness sorries: `DivwRemw.lean:1035` (h_abs), `DivwRemw.lean:1044` (h_sign) — moderate difficulty, all _poly infra in place
- 1 body sorry: `DivRem.lean:1064` (div_rem_poly, ~700 lines needed for signed 64-bit core)

**User-decided sequencing for next sessions:**
1. ~~Branch~~ DONE
2. ~~Mul~~ DONE
3. ~~ShiftLeft/ShiftRight file split~~ DONE (2026-05-11)
4. ShiftLeft `_poly` migration — **READY TO RESUME** (Phase A `is_trusted` cascade closed 2026-05-11 evening, full `lake build` green with only the 10 pre-existing DivRem sorries as warnings). State of Fin KB groundwork unchanged from below:
   - ✅ `allHold_constraints_iff_poly` (Constraints.lean) — note: RHS uses `< 2 ^ (10 : ZMod p).val` not `< 1024` (Fin KB's simp reduces `2^10.val` to `1024`, ZMod p simp doesn't; matching the unreduced form keeps `simp [constraints, sub_eq_zero]` as the closer). Wrapped with `omit [Fact (2^17 < p)] in set_option maxRecDepth 1000000 in`.
   - ✅ `sp1_op_a_poly`, `sp1_op_b_poly`, `sp1_op_c_poly`, `sp1_op_c_imm_poly`, `sp1_op_c_imm_w_poly` — trivial `BitVec.ofNat 5 Main[i].val` (or 6 for the imm variant).
   - ✅ `single_op_poly` — uses iff_poly + case split on b_sll/b_sllw + `linear_combination` to contradict the (1,1) case via `val_2_zmod_p`.
   - ❌ `bounds_poly` — SORRY. Attempted; left with 18+ type-mismatch errors (h5.mpr direction `Main[13] = 1` vs `¬Main[13] = 0`, h_imm0/h_imm1 destructure mismatches with `r_type_constraints_poly`/`shift_i_type_constraints_poly`/`w_shift_i_type_constraints_poly`). Skeleton is in git history but reverted to sorry.
   - ❌ `cancel_mul_65536_poly` — SORRY. **BLOCKED by KB-specific constant**: the constraint compiler emits `2097414145` (= inverse of 64 in Fin KB only). For general ZMod p, `(64 : ZMod p) * 2097414145 ≢ 1`. Lemma is provable only with extra `[Fact ((64 : ZMod p) * 2097414145 = 1)]` or equivalent, which restricts p essentially to KB.
   - ❌ `is_mod_64_poly` — SORRY. Same KB-specific constant blocker as `cancel_mul_65536_poly`. The constraint `((c0 - m) * 2097414145).val < 1024` only encodes "c0 ≡ m (mod 64)" when `2097414145` is the multiplicative inverse of 64 — which holds only for p ∈ {3, 7, KB} given `64 * 2097414145 = 63 * KB + 1`.
   - ❌ `spec.sll_poly`, `spec.slli_poly`, `spec.sllw_poly`, `spec.slliw_poly` — NOT STARTED. Each is ~100 lines with 64-way `rcases b_cb0 <;> rcases b_cb1 <;> ...` + `simp_all` cascade + `Word.toBitVec64_toNat` + `omega`. The Fin KB version relies heavily on simp reducing `Fin.val_add, Fin.val_mul`; ZMod version needs `ZMod.val_add_of_lt, ZMod.val_mul_of_lt` (guarded by < 65536 bounds).
   - ❌ Chip-level `correct_*_poly` (ShiftLeftChip.lean): NOT STARTED. Mirror MulChip's `Mul.Poly` namespacing.
   - ❌ Phase 5 collapse: NOT STARTED.
5. ShiftRight `_poly` migration (Common.lean has `is_real_poly` + 8 `is_X_poly` defs landed)
6. DivRem last (~10-15 hours wall-clock for full finish)

**ShiftLeft iff_poly proof recipe** (verified 2026-05-11): just `simp [constraints, sub_eq_zero]` works once the RHS matches simp's normal form. The Fin KB `< 1024` literal must be written as `< 2 ^ (10 : ZMod p).val` on the `_poly` iff RHS (because `(10 : ZMod p).val` doesn't auto-reduce). All other conjuncts match verbatim. The DivRem-style `and_assoc` + `iterate rw eq_comm` + `simp [neg_eq_zero]` recipe is NOT needed for ShiftLeft (DivRem only needs it because its constraint set has more `-1 = 0` style equations).

**KB-specific constant issue RESOLVED (2026-05-11 evening)**: The user added `64` to `KNOWN_BASES` in the SP1 constraint compiler (`/home/dtumad/Documents/sp1/crates/hypercube/src/ir/expr_impl.rs:146`). Regenerated constraints now emit `((64 : F)⁻¹)` instead of `2097414145`. The `is_mod_64_poly`/`cancel_mul_65536_poly` can now use the generic field identity `(64 : ZMod p)⁻¹ * 64 = 1` (provable from `Field` axioms — no extra Fact needed). My previous concern about restricting p to KB is moot.

**BUT**: the regen also pulled in an unrelated upstream change (the `is_trusted` re-add — see `project_is_trusted_readd_cascade.md`). That cascade broke the build project-wide. Phase A is to sync this; Phase B resumes ShiftLeft `_poly` here.

**Pickup state for Phase B (after Phase A green)**:
- Update ShiftLeft iff_poly RHS in `SP1Chips/ShiftLeft/Constraints.lean`: replace `2097414145` with `((64 : ZMod p)⁻¹)` (single occurrence) AND update the inner ALU call to drop `#v[E195, E186, E178, E181]` and append `(Main[62]+Main[63])` at end.
- `bounds_poly` destructure pattern in `Common.lean` needs adjustment for the new ALU iff shape (after readers' iffs are updated in Phase A).
- The spec.*_poly cores are the heaviest porting effort (4 × ~100 lines each, with 64-way case splits + bv_decide). Reference AddChip for the chip-level correct_*_poly pattern.

**Session 2026-05-12: ShiftLeft `_poly` skeleton landed (10 sorries, build green)**

Phases 1, 2 (partial), 4 (stubs), 5 (stubs) complete. Total state after this session:
- ✅ `SP1Chips/ShiftLeft/Constraints.lean`: `allHold_constraints_iff_poly` PROVEN with one-liner `simp [constraints, sub_eq_zero]` (RHS uses `((64 : ZMod p)⁻¹)` symbolic + `< 2 ^ (10 : ZMod p).val` for unreduced bound; needs `omit [Fact (2^17 < p)] in set_option maxRecDepth 1000000 in` wrapper).
- ✅ `SP1Chips/ShiftLeft/Common.lean`: `single_op_poly`, `is_real_eq_one_of_{sll,sllw}`, `sp1_op_{a,b,c,c_imm,c_imm_w}_poly` all PROVEN (no sorry). `single_op_poly` uses `linear_combination` to refute the 1+1=0/1 case via `val_2_ne_zero` + explicit `ZMod.val_one p` under `Fact (1 < p)`.
- 🟡 `SP1Chips/ShiftLeft/Common.lean`: `ops_U64_b_c_poly` and `bounds_poly` STUBBED (2 sorries). Attempted ops_U64_b_c_poly with opcode case-split (6 vs 21); blocked on Nat.beq reduction for the trusted_instr simp + the imm=1 `c0 < 2^k` → `.val < 65536` lift. Recommended approach: split into `bounds_b_a_poly` (op_a, op_b, U64 b — these don't need imm/opcode split) and a separate `bounds_c_imm_poly` for the imm=1 path.
- 🟡 `SP1Chips/ShiftLeft/Sll.lean`: `spec.sll_poly`, `spec.slli_poly` STUBBED (2 sorries).
- 🟡 `SP1Chips/ShiftLeft/Sllw.lean`: `spec.sllw_poly`, `spec.slliw_poly` STUBBED (2 sorries).
- 🟡 `SP1Chips/ShiftLeftChip.lean`: `correct_{sll,slli,sllw,slliw}_poly` STUBBED in `Sll.Poly` / `Slli.Poly` / `Sllw.Poly` / `Slliw.Poly` namespaces (4 sorries). Pattern follows MulChip:9-108 verbatim minus `Fact (2 ^ 24 < p)`. Each uses `sp1_op_*_poly Main` directly (no cstrs args, deferring bounds to inside the proof).
- ❌ Phase 3 (field arith) NOT STARTED: `cancel_mul_65536_poly` and `is_mod_64_poly` still not written. Field.lean bridges `val_64_zmod_p`, `val_64_ne_zero`, `val_1024_zmod_p` not added.
- ❌ Phase 6 (collapse) NOT STARTED.

**Build state:** full `lake build` green; error count 0; warning count 20 = 10 pre-existing DivRem + 10 new ShiftLeft sorries.

**Next session pickup order:**
1. `ops_U64_b_c_poly` finalize — preferred approach: split into 2 lemmas (b-only direct from ALU iff, c-with-imm-case-split). The opcode case-split blocker is the `Nat.beq 6 0 = false ... Nat.beq 6 6 = true` simp resolution — recommend using `decide` or fully spelled-out `Opcode.ofNat 6 = .SLL` lemma first.
2. `bounds_poly` finalize — mirror Fin-KB `bounds` proof structure but with `_poly` machinery (val_*_zmod_p bridges for the < 32 conversions).
3. `cancel_mul_65536_poly`: cleaner in ZMod p than Fin KB (no modular wrap to undo); use `mul_inv_cancel₀` + `ZMod.val_mul_of_lt`.
4. `is_mod_64_poly`: hardest. Strategy is `bv_decide` on a 64-bit BitVec lifted via `BitVec.ofNat 64 (c0 - m).val`; need NeZero p and the val bounds to hoist through.
5. `spec.{sll,slli,sllw,slliw}_poly`: mechanical port from Fin-KB, ~100 lines each. Wait until 1-4 done.
6. `correct_{sll,slli,sllw,slliw}_poly`: mechanical port from MulChip pattern, ~70 lines each.
7. Phase 6 collapse: delete Fin-KB triples via `sed` (Edit too fragile for 6 × 100-line blocks).

**Wall-clock estimate to finish:** 10-15h based on Branch/Mul migration cadence + DivRem complexity adjusted downward for ShiftLeft's smaller constraint set (65 cols vs 247 for DivRem, 82 for Mul).

**Session 2026-05-12 (continued): Phase 3 complete; ops_U64_b_c_poly + helpers proven**

Field.lean: `val_64_zmod_p`, `val_64_ne_zero`, `val_1024_zmod_p` added.

Common.lean (Phase 3 ✅ DONE):
- `cancel_mul_65536_poly`: cleaner in ZMod p than Fin KB — just `mul_right_cancel₀` after lifting `x.val * z = 65536` to ZMod p. Signature takes `x.val ∣ 65536 ∧ 0 < x.val`.
- `is_mod_64_poly`: cleaner than Fin KB — no bv_decide. From `c0 - m = k * 64` with `k.val < 1024`, get `c0.val = m.val + k.val * 64 < 65600 < p` (no wrap), so `c0 % 64 = m`.

Common.lean (Phase 2 partial helpers ✅ DONE):
- `sll_or_sllw_of_real`: from `Main[62] + Main[63] = 1`, conclude exactly one flag is 1 (uses `val_2_ne_zero` to refute `1 + 1 = 0 or 1` in char > 2).
- `ops_U64_b_c_poly`: ALU iff for op_b directly; case-split on SLL vs SLLW for op_c under imm=1 (uses `shift_i_type_constraints_poly` / `w_shift_i_type_constraints_poly` decomposition). Required `dsimp only at alu` to force cols struct-projection reduction so `simp only [Vector.getElem_mk]` could land. Opcode evaluation uses explicit `((6 : ℕ) : ZMod p)` cast in rewrite (the literal `1 * 6` in poly mode prints as `1 * ↑6` because of NatCast); the matching `key` form is `1 * ((6 : ℕ) : ZMod p) + 0 * 21 = ((6 : ℕ) : ZMod p)`.

Common.lean (still sorry):
- `bounds_poly` (1 sorry) — needs same case-split pattern as `ops_U64_b_c_poly` but for more conjuncts. Should be straightforward port given the field-arith now lands.

Sll.lean / Sllw.lean (Phase 4 — 4 sorries, no bodies yet):
- The 64-way case split + `BitVec.toNat_shiftLeft` rewrite needs `simp [BitVec.toNat_shiftLeft, BitVec.shiftLeft_eq']` (verified via `lean_multi_attempt`) instead of the Fin-KB `rw [BitVec.toNat_shiftLeft]; rw [Nat.shiftLeft_eq]` two-step. The reduced goal has the form `(toBitVec64_poly a).toNat = (toBitVec64_poly b).toNat <<< ((toBitVec64_poly c).toNat % 64) % 2^64`. From there, `Word.toBitVec64_poly_toNat_poly` substitutes, then `is_mod_64_poly` gives `c0 % 64 = cb_sum`, then the 64-way rcases + `cancel_mul_65536_poly` close.

ShiftLeftChip.lean (Phase 5 — 4 sorries, full namespace skeletons in place):
- `Sll.Poly` / `Slli.Poly` / `Sllw.Poly` / `Slliw.Poly` namespaces have `spec_*_poly`, `sp1_*_poly`, `correct_*_poly` declarations. Bodies sorry. Pattern follows MulChip:9-108.

**Total project state after this session:** 19 warnings = 10 DivRem sorries (pre-existing) + 9 ShiftLeft sorries (1 bounds_poly + 4 spec.*_poly + 4 correct_*_poly). Build green.

**Commits this session:**
- 9806606: shiftleft _poly skeleton: iff_poly + helpers + spec/chip stubs
- 594143c: shiftleft _poly: field-arith helpers + ops_U64_b_c_poly proven
- c88bb47: shiftleft _poly: bounds_poly proven; Phase 2 complete
- 27e85ef: shiftleft _poly: spec.sll_poly partial — c0%64 reduction landed
- fb0467a: shiftleft _poly: spec.sll_poly progress + val_2^k bridges to Field.lean
- 678af71: shiftleft _poly: spec.sll_poly cb4=cb5=0 case scaffolding
- 935e4cf: shiftleft _poly: fix show → change in spec.sll_poly
- b286958: shiftleft _poly: spec.sll_poly 16-way cb0..3 case split scaffolded

**KEY UNBLOCK: kernel deep recursion was 2^N literal trigger (matches docs/GOTCHAS.md exactly)**

User flagged the deep recursion as the canonical "large literal" issue. `docs/GOTCHAS.md` "Kernel deep-recursion on 2^N" describes the exact failure mode:
- `Word.toBitVec64_poly_toNat_poly` unfolds to `BitVec.toNat (BitVec.ofNat 64 ...)` which contains `2^64` literal
- Kernel re-check tries to evaluate `2^64` definitionally → succ-chain overflow
- Trigger threshold is `2^N` with `N ≥ 15`; our 2^16/32/48/64 literals all qualify

**FIX**: `set_option debug.skipKernelTC true in` bypasses the kernel re-check. **Does not introduce new axioms** (`lean_verify` confirms standard axiom set). Per GOTCHAS doc this is "treat as last resort" but already used in `SP1Operations/Operation/AddrAddOperation.lean:165` and `SP1Operations/Operation/MulOperation/Constraints.lean:261` — established workaround in the codebase.

**With `skipKernelTC` applied to `spec.sll_poly`, the all-zeros sub-case CLOSES CLEANLY** (commit `74f771a`). The proof body is exactly the chain I drafted:
```lean
simp only [hcb0, hcb1, hcb2, hcb3, zero_mul, zero_add, mul_zero, add_zero, one_mul, mul_one]
  at eq_v01 eq_v012 eq_v0123 h_b0_dec ... lt_ll3 lt_lh3
rw [eq_v01] at eq_v012; rw [eq_v012] at eq_v0123
rw [eq_v0123] at h_b0_dec ... eq_lr3
simp only [Nat.cast_one, mul_one] at h_b0_dec ... eq_lr3
simp only [h_v0_val, pow_zero, Nat.lt_one_iff] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
have h_hl0_zero : hl0 = 0 := (ZMod.val_eq_zero hl0).mp lt_lh0
... (similar for hl1, hl2, hl3)
rw [h_hl0_zero] at h_b0_dec eq_lr1
... (rest of the chain)
simp only [eq_v0123, eq_lr0, eq_lr1, eq_lr2, eq_lr3, Nat.cast_one, mul_one, add_zero,
  h_hl0_zero, h_hl1_zero, h_hl2_zero, zero_add, add_zero]
rw [← h_b0_dec, ← h_b1_dec, ← h_b2_dec, ← h_b3_dec]
have h_cb_sum_zero : (cb0 + cb1 * 2 + ...).val = 0 := by simp only [hcb0..hcb5, ...]; exact h_v0_val
rw [h_cb_sum_zero]; simp only [Nat.shiftLeft_zero]
rw [Nat.mod_eq_of_lt (BitVec.isLt _)]
```

**Pickup state for next session:**
- Replicate the all-zeros proof pattern for the other 15 cb0..3 sub-cases within cb4=cb5=0.
  Each case has different cb_sum_low (0..15) and v0123 (= 2^cb_sum_low). For cases with cb_sum_low > 0, hl_i is no longer 0 — instead we use `cancel_mul_65536_poly` to get `b_i = hl_i * 2^(16-cb_sum_low) + ll_i`, then prove `(toBitVec64 lr).toNat = (toBitVec64 b).toNat << cb_sum_low % 2^64` via omega.
- For the other 3 cb4/cb5 cases (byte_shift 1, 2, 3): structurally similar but `Main[45+i] = 1` for the respective i, and rest gives byte-shifted a_j equations.
- Apply same pattern (with skipKernelTC) to spec.slli_poly, spec.sllw_poly, spec.slliw_poly.
- Chip-level correct_*_poly: mechanical from MulChip template.
- Phase 6 collapse.

**Suggested generic helper (NOT YET WRITTEN) to reduce code duplication:**
A helper at the `Nat` level taking `(cb_sum_low : ℕ)` and the byte-decomposition + bound hypotheses, proving the within-byte shift identity. The 16 cb0..3 sub-cases per cb4/cb5 branch then become applications with different specific values. Estimate: ~150-line helper + 64 × ~30-line case applications.

**KEY DIAGNOSIS for spec.*_poly 64-way case split (verified via Plan agent + lean_multi_attempt):**

The Fin-KB `rcases <;> simp_all` strategy DOES NOT transport to ZMod p — kernel deep recursion occurs because:
1. `rest` (24 deeply-nested conjuncts of `Main[62] = 0 ∨ Main[45+i] = 0 ∨ a_j = ...`) overwhelms simp_all's `at *` traversal in poly mode.
2. ZMod p lacks the cheap `(0/1 : Fin KB).val` reduction that Fin KB has; each .val check needs `val_*_zmod_p` + `NeZero` + `Fact (1 < p)` searches.
3. Auto-discharge of side conditions in cancel_mul_65536_poly fails to terminate quickly.

**The working strategy (used in commit 678af71):**
1. **Preprocess `rest` BEFORE the case split**: `rw [eq_sll, h_no_sllw] at rest; simp only [h_1_ne_0, false_or, true_or, or_true] at rest`. This collapses `Main[62]=0` to False and `Main[63]=0` to True.
2. **Split into two stages**: outer rcases on cb4, cb5 (4 cases) determines byte-shift offset; inner rcases on cb0..3 (16 cases per branch) determines within-byte shift.
3. **Use `rw [hcb_i]` not `subst`** because cb_i are `set`-aliases (let-bound). `subst` only works for free variables.
4. **Use `simp only [list]` not `simp_all`** to avoid the deep recursion.
5. **For each case, derive which Main[45+i] = 1** via the h_su_sum constraint + `val_i_ne_zero` contradictions (where i ∈ {1, 2, 3}).
6. **Extract a_j = lr_j (or 0)** from the 16 relevant rest conjuncts using h_45+i_eq + h_1_ne_0.

**Current state in spec.sll_poly cb4=cb5=0 case (commit 678af71):**
- Steps 1-6 done: a0..3 = lr0..3 extracted.
- After `rw [h_a_eq, eq_lr_eq]`, goal is the within-byte shift identity.
- Remaining: 16-way rcases on cb0..3, cancel_mul_65536_poly on h_b_dec, omega closer.

**Per-case closer template** (still to be fleshed out per cb0..3 subcase):
```
rw [hcb0]; rw [hcb1]; rw [hcb2]; rw [hcb3]  -- substitute literals
simp only [zero_mul, one_mul, ..., val_*_zmod_p] at eq_v0123 eq_v012 eq_v01 h_b0_dec ...
have hv_dvd : Main[44].val ∣ 65536 := by rw [eq_v0123_specialized]; decide
have hv_pos : 0 < Main[44].val := by rw [eq_v0123_specialized]; decide
apply cancel_mul_65536_poly hv_dvd hv_pos at h_b0_dec
... (similarly for b1, b2, b3)
-- Now use Word.toBitVec64_poly_toNat_poly + omega.
```

**Remaining work** (still 8 sorries: 1 in spec.sll_poly cb4=cb5=0, 3 in other cb4/cb5 cases of spec.sll_poly, 4 in other spec.*_poly + 4 chip-level correct_*_poly):
- Complete spec.sll_poly cb4=cb5=0 (16-way cb0..3 split): probably ~80 lines.
- Replicate for cb4=1/cb5=0, cb4=0/cb5=1, cb4=1/cb5=1 (3 more analogous blocks): ~250 lines total.
- spec.slli_poly: similar but imm=1 branch (Main[21]=Main[25] from h_imm1_op_c) — simpler since c1=c2=c3=0.
- spec.sllw_poly, spec.slliw_poly: same with execute_RTYPEW_pure_w_poly + truncation to 32 bits.
- 4 chip-level correct_*_poly: mechanical from MulChip:34-108 template.
- Phase 6 collapse.

**Final session state — Phases 1, 2, 3 COMPLETE:**
- 18 total project sorries = 10 DivRem (pre-existing) + 8 ShiftLeft (4 spec.*_poly + 4 correct_*_poly)
- Zero sorries in Constraints.lean and Common.lean for ShiftLeft
- All field-arith and bounds infrastructure proven

**Pickup state for next session (Phase 4):**
- `spec.sll_poly` blueprint: the verified tactic for the BitVec shift step is `simp [BitVec.toNat_shiftLeft, BitVec.shiftLeft_eq']` (NOT the Fin-KB two-step `rw [BitVec.toNat_shiftLeft]; rw [Nat.shiftLeft_eq]`). This reduces the goal to `(toBitVec64_poly a).toNat = (toBitVec64_poly b).toNat <<< ((toBitVec64_poly c).toNat % 64) % 2^64`. Then `Word.toBitVec64_poly_toNat_poly is_U64_c` + `Word.toNat_poly` + arithmetic gives `c0.val % 64` in the shift amount. `is_mod_64_poly` converts that to `cb0 + cb1*2 + ... + cb5*32`. The 64-way rcases + `cancel_mul_65536_poly` + `Word.toBitVec64_poly_toNat_poly is_U64_b` + omega close each branch.
- spec.sll_poly destructure of the iff_poly conjuncts works (verified via lean_multi_attempt — see snippet 2 in the goal output).
- The cancel_mul_65536_poly signature differs from Fin-KB: needs `(h_x_dvd : x.val ∣ 65536) (h_x_pos : 0 < x.val)` rather than just `(x : ℕ) ∣ 65536`. The positivity comes from the divisor being one of v0123's factors which are all nonzero products.

**Critical-gotcha note (saved for the next session):**
1. The opcode `Main[62] * 6 + Main[63] * 21` in polymorphic mode prints with `↑6` (NatCast from ℕ) — to do `rw [..., show ... = ((6 : ℕ) : ZMod p) from by push_cast; ring]`, the rewrite source must use `((6 : ℕ) : ZMod p)` on the LHS to match.
2. The ALU iff_poly RHS uses struct projections `cols.op_a`, etc., that DON'T reduce automatically after `rw [ALUTypeReader.allHold_constraints_iff_is_real_poly ...]`. Need explicit `dsimp only at alu` after the rw to force projection.
3. The h_imm1_op_c conjuncts in the ALU iff produce `#v[Main[21..24]][i] = ...` form; need `simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]` to reduce the vector indexing.
