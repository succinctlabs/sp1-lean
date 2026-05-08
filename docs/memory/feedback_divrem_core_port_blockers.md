---
name: DivRem core _poly port: 3 specific blockers
description: Fin KB → ZMod p port of divu_remu (DivRem core) — divu_remu_poly closed 2026-05-07 (commit bb6d325); divuw_remuw_poly closed 2026-05-08 with HWord prereqs and 4-limb carry chain adaptations.
type: feedback
originSessionId: de207b62-f4b6-46d7-8765-7450afd1306f
---

**divuw_remuw_poly LANDED 2026-05-08** (4-limb carry chain, 32-bit unsigned):

Adjustments from divu_remu_poly:
- 4 new HWord _poly companions in `SP1Foundations/Word.lean` (just before `end HWord`):
  `extend_poly`, `extend_U32_U64_poly`, `extend_true_is_signExtend_poly`,
  `extend_false_is_setWidth_poly`. Plus `low_toNat_poly`. Mirror BHWord recipe.
- ext_q/ext_r helpers need a value-bridge: `(32768 : ZMod p) ≤ q1 ↔ 32768 ≤ q1.val`
  via `show (32768 : ZMod p).val ≤ q1.val ↔ _; rw [h32768_val]`. Without this,
  `split_ifs` can't unify the LE on ZMod p with the LE on ℕ inside `HWord.isNegative_poly`.
- c=0 branch destructure: `nzc : c0 = 0 ∧ c1 = 0` (only 2 conjuncts, since high
  limbs are constrained to 0 separately in the is_word=1 path). `simp [div_zero] at *`
  resolves the `is_c_0 = 0 ∨ ...` ORs in c0_eq_q*/r* automatically (one_ne_zero
  is in mathlib's default simp set).
- ≠ 0 proofs (`HWord.toNat_poly #v[c0,c1] ≠ 0`) need explicit ZMod-to-Nat bridging
  via `(ZMod.val_eq_zero c).mp` after deriving `c.val = 0` via omega.
- 4-limb carry chain (vs 8 for divu_remu): nof_eq_ctqpr2/3 have `0 = ctq_i + cry_{i-1}
  - cry_i * 65536` (no r_i, no b_i — both zeroed in is_word=1 path).
- `simp at *` collapses `h0v : (0:ZMod p).val = 0` to `True`. After this, must
  use `simp only [ZMod.val_zero] at h1` instead of `rw [h0v]` (the latter hits
  max recursion).
- `omega` for the final 4-limb closure handles `cry3.val * 2^64` carry: don't
  try to prove cry3.val = 0 (it can be 1 in edge cases); instead include
  `cry3.val * 18446744073709551616` in `main_eq` and let omega chase mod 2^64.
- Need `set_option maxRecDepth 1000000` (in addition to `maxHeartbeats 32000000`
  and `debug.skipKernelTC true`). Without it, the `omega` on eq3 hits depth limit.
- `simp [execute_DIV_REM_pure, ..., -BitVec.toNat_setWidth]` — keep
  `-BitVec.toNat_setWidth` to preserve the `Word.setWidth_eq_low_poly` pattern
  for the rewrite chain.

**RESOLUTION 2026-05-07:** The Fin-KB-style joins/divs/conv chain doesn't translate to ZMod p — the conv-LHS substitution leaves `(ctq + r + cry).val % 65536` form (with cry still ZMod), which `rw [j1, d1, j2, d2, j3]` can't pattern-match because cry's substitution requires a Nat `cry_i.val = .../65536` form, not a ZMod `cry_i = ...` form. The fix bypasses this entirely:
- Distribute `.val` over `+` for each `(ctq + r + cry).val` and `(ctq + cry).val` via `ZMod.val_add_of_lt` (8 hsum*'s)
- Combine `nof_eq_ctqpr_i.1` (mod 65536 form) with `.2` (div 65536 form) into a single Nat eq per limb (8 eq*'s of form `b_i.val + cry_i.val * 65536 = ctq_i.val + r_i.val + cry_{i-1}.val`)
- Linear combination eq0..eq7 weighted by 2^(16i) → `main_eq` (Nat poly equality, omega closes)
- Reduce `DWord.toBitVec128_poly` to `BitVec.ofNat 128 (...)` via `simp [DWord.toBitVec128_poly, DWord.toNat_poly]` (8-element vector indexing reduces under simp)
- Lift to `.toNat` via `← BitVec.toNat_inj`, fold `BitVec.toNat_add`/`ofNat`, omega closes mod 2^128 equation using main_eq

**Three gotchas hit:**
1. `(by omega)` for `(0:ZMod p).val < 65536` (in the 4 nof_eq_ctqpr_{4..7} `div_mod_decomposition_w_poly` rewrites) FAILS because `simp at *` upstream collapsed `h0v : (0:ZMod p).val = 0` to `True`. Replace with `(by simp)` — simp knows `ZMod.val_zero`.
2. `obtain ⟨h1, h2⟩ := nof_eq_ctqpr_i` for i ∈ {5,6,7} hits "max recursion depth" — likely a unification depth issue with the 8-conjunct form. Replace with `have h1 := nof_eq_ctqpr_i.1; have h2 := nof_eq_ctqpr_i.2`. Direct projection avoids the recursion.
3. omega cannot close the final modular equation directly because `2^128` is too large. Workaround: provide `main_eq` (explicit 9-term linear combination from eq0..eq7), `lhs_b` (LHS-mod-65536 reduction using eq0..eq3), `dctq`/`dr` (DWord literal → BitVec.ofNat unfolds via simp). Then omega has small bounds + linear forms to chain.

How to apply: when porting `div_rem`, `divuw_remuw`, `divw_remw` (the other 3 cores), use this fresh approach and skip the Fin-KB joins/divs/conv chain entirely. Each core takes ~70 lines of replacement code (8 hsums + 8 eqs + main_eq + lhs_b + dctq/dr + 2 simp lifts + omega).

**Mid-session checkpoint 2026-05-05 (NOT yet committed):**
`SP1Chips/DivRem/Constraints.lean` lines ~2455–2793 contain the
in-progress `divu_remu_poly` lemma. Stage 1 (upfront prep), Blocker 1
(opening rcases), Blocker 2 (c=0 branch), and the c≠0 "have arm"
all landed. **Sorry placeholder** at line ~2793 for the 8-way
`b_cry3` end-game (Blocker 3 territory).

**Blocker 1 resolution (landed):** Replace
```lean
rcases b_is_divu <;> rcases b_is_remu <;> simp_all
```
with explicit 4-case `rcases ... with h_du | h_du <;> rcases ... with
h_ru | h_ru` plus four bullets:
- `(0,0)`: `exfalso; rw [h_du, h_ru, zero_add] at divu_remu;
   exact h01 divu_remu.symm`
- `(0,1)`: `exact ⟨this.1, this.2.2.1, this.2.2.2.1,
   this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩` where
   `this = sop4 h_ru`. **Note** sop4 returns
   `is_div ∧ is_divu ∧ is_rem ∧ is_divw ∧ is_remw ∧ is_divuw ∧
   is_remuw` (so `.2.2.1 = is_rem`, NOT `is_remu`).
- `(1,0)`: `exact ⟨this.1, this.2.1, this.2.2.2.1, this.2.2.2.2.1,
   this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩` where `this = sop2 h_du`.
   sop2 returns `is_div ∧ is_rem ∧ is_remu ∧ is_divw ∧ ...`.
- `(1,1)`: `exfalso; rw [h_du, h_ru] at divu_remu; have :
   (1+1:ZMod p)=2 := by ring; rw [this] at divu_remu; exact h21
   divu_remu`.

Upfront prep `clear *-` must include `h01 h21` so the contradictions
remain in scope.

**Blocker 2 resolution (landed):**
```lean
simp [Word.toBitVec64_poly_toNat_poly is_U64_b]
simp [Word.toBitVec64_poly, Word.toNat_poly, h65535_val, h0v]
push_cast [ZMod.cast_eq_val]
rfl
```
**Critical insight:** the `.cast` shown in the pretty-printed goal is
**`Nat → ℤ`** (not `ZMod.cast`), and the outer `.toNat` is
`Int.toNat` — `push_cast [ZMod.cast_eq_val]` pushes both through
and `rfl` closes. Plain `rfl` fails because the LHS shows `b.val`
form and the RHS shows `(b.cast + b.cast * 65536 + ...).toNat` form,
which are equal only after pushing the Int casts through.

**Blocker 3 status (paused at sorry):** All upstream rewrites into
the 8-way end-game are in place. The `div_mod_decomposition_w_poly`
calls use `(by omega : cry_i.val < 2)` (NOT `hcv_i : cry_i.val ≤ 1`
— the lemma wants strict `< 2`). The `conv` block on the LHS plus
the `joins`/`divs` helpers + `simp [← BitVec.toNat_inj]; repeat rw
[BitVec.toNat_add]; iterate 2 rw [DWord.toBitVec128_poly_toNat_poly
(...)]; simp [DWord.toNat_poly, h0v]; ring_nf` are in place. The
remaining work is the 8-way `rcases b_cry3 with of | nof <;> subst
cry3 <;> simp at *` end-game (corresponds to lines 2416–2442 of
Fin KB original).

The auxiliary `div_mod_decomposition_w_poly` landed 2026-05-05
(commit `ab6def6`, ~30 lines, clean). It's at `c.val < 2` (not the
KB-bound `2130706433/65536`) since at every use site `c` is a carry bit;
wrap-around branch ruled out via `Fact (2^17 < p)`.

The next step (Phase 3b first core, `divu_remu_poly`, ~310 lines) was
attempted in the same session and pulled back — the body needs more
focused tactic work than fits in one auto-mode session. Three specific
blockers identified:

**1. The `simp_all` opening contradiction at the `obtain ⟨z_div,...⟩` step:**
```lean
rcases b_is_divu <;> rcases b_is_remu <;> simp_all
```
For Fin KB this closes by `decide`. For ZMod p, the (1,1) case
needs `(2 : ZMod p) ≠ 1` (from `Fact (2^17 < p)` ⇒ `p > 2`), and
the (0,0) case needs `(0 : ZMod p) ≠ 1`. Add explicit:
```lean
have h01 : (1 : ZMod p) ≠ 0 := one_ne_zero
have h21 : (2 : ZMod p) ≠ 1 := by ...
```
then `simp_all [h01, h21]` or chain `<;> first | (exfalso; ...) | done`.

**Why:** `simp_all` collapses `Fact (2^17<p)` to `Fact True` per the
`feedback_chip_migration_tactics.md` warning; lift the contradiction
to a literal Prop hypothesis BEFORE the `simp_all`.

**2. The c=0 branch's `rfl` closure on the all-65535 quotient:**
After `subst c0 c1 c2 c3 q0 q1 q2 q3 r0 r1 r2 r3`, the goal contains
`BitVec.ofNat 64 (ZMod.val 65535 + ZMod.val 65535 * 65536 + ZMod.val 65535
* 4294967296 + ZMod.val 65535 * 281474976710656) = 18446744073709551615#64`
plus a `(b0.cast + ...).toNat = b0.val + ...` form.

The Fin KB version closes via `simp [Word.toBitVec64, Word.toNat]; rfl`
because `(65535 : Fin KB).val = 65535` reduces by `decide`. For poly,
`(65535 : ZMod p).val = 65535` requires explicit
`ZMod.val_natCast_of_lt` (with `Fact (2^17 < p)` ⇒ `65535 < p`).
**Fix:** add upfront `have h65535_val : (65535 : ZMod p).val = 65535 :=
ZMod.val_natCast_of_lt (by omega)` and pass to the simp set, plus
the `b.cast.toNat = b.val` bridge (likely follows from
`Word.toBitVec64_poly` definition + `BitVec.toNat_ofNat`).

**Why:** Project memory `feedback_chip_migration_tactics.md` already
notes that opcode literals need explicit `val_<N>_zmod_p` helpers;
65535 is a missing entry alongside 32/256/65536.

**3. The `Nat.mod_eq_of_lt` calls at lines 2402, 2378 (after
`bv_ctqr` rewrite) and inside the 8-way `b_cry3` rcases (lines 2417-2442):**

The Fin KB version uses `Nat.mod_eq_of_lt (b := 2130706433)` to
strip `% KB` from sums of carry/byte values (each < 65536). For
ZMod p, the mod is `% p` instead. The discharges need:
- 4-limb sums up to ~4·65535 (~2^18) under `Fact (2^17 < p)`.
  **`Fact (2^17 < p)` is BARELY insufficient** for full 4-limb sums
  involving multiplication by 65536 (which gives ~2^32). Need to
  use `ZMod.val_add_of_lt` step-by-step with explicit each-step
  bounds, OR upgrade to `Fact (2^32 < p)` if cleaner.
- For the 8-way `b_cry3` end: each `cry_i = 0 ∨ cry_i = 1` must be
  bridged to `cry_i.val ≤ 1` explicitly before `omega` can close.
  Use `have h_cry_i_val : cry_i.val ≤ 1 := by rcases b_cry_i <;>
  simp` upfront.
- The `nlinarith` at line 2381 (`q*c+r < 2^128`): use `nlinarith` 
  directly (matches original); explicit `Nat.mul_le_mul` with
  `Nat.le_of_lt` gives `q*c ≤ 2^128` not `q*c < 2^128`, requiring
  strict-via-Nat.mul_lt_mul' route.

**Recommended fresh approach for the next session:**

1. Upfront prep: derive `h_cry_i_val : cry_i.val ≤ 1` for each
   carry, `h65535_val : (65535 : ZMod p).val = 65535`, and the
   contradictions `(2 : ZMod p) ≠ 1` etc.
2. Body: copy the Fin KB body verbatim, apply mechanical
   substitutions (Word.X → Word.X_poly, Fin.val_add → ZMod.val_add,
   2130706433 → p), and patch the spots where my upfront prep
   above is needed.
3. Allocate **32M heartbeats** (not 16M) and `set_option
   debug.skipKernelTC true in` — precedent: `core_mul_poly`.
4. **Iteratively** debug via `lean_diagnostic_messages` — fix one
   error at a time, don't try to write the whole proof in one shot.

How to apply: when picking up Step 2, start by adding the upfront
prep (Stage 1: `have` lemmas for the 3 blocker-resolution forms);
then literal-port the body; then debug iteratively. Allocate a
2-3 hour focused block — not safe to attempt at the end of a long
session.
