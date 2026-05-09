---
name: DivRem core _poly port: status + blockers
description: Fin KB → ZMod p port — 3 of 4 cores landed; div_rem_poly STUB added 2026-05-08 (signature only, sorry body); 8 chip-level correct_<v>_poly STUBS added in DivRemChip.lean (sorry bodies); divw_remw_poly h_abs/h_sign sorries remain. Phase C spec wrappers (~1600 lines) deferred.
type: feedback
originSessionId: de207b62-f4b6-46d7-8765-7450afd1306f
---

**SCAFFOLDING checkpoint 2026-05-08** (this session):
Per user direction "sorry on hard blocker, continue downstream" + bottom-up
closure intent, the migration's API surface was completed structurally even
though several internal proof obligations remain `sorry`:

- **`div_rem_poly` stub** added before `end div_rem` in
  `SP1Chips/DivRem/Constraints.lean` (~180 lines: signature + `:= by sorry`).
  Signature is a verbatim mirror of Fin KB `div_rem` (line 1311) with
  `Fin KB → ZMod p`, `Word.isU64 → Word.isU64_poly`,
  `Word.toBitVec64 → Word.toBitVec64_poly`,
  `Word.toNat → Word.toNat_poly` substitutions. Set-options match
  `divw_remw_poly` (`debug.skipKernelTC, maxHeartbeats 32M, maxRecDepth 1M`).
- **8 chip-level `correct_<variant>_poly` STUBS** added at the end of
  `SP1Chips/DivRemChip.lean` inside a new `namespace DivRem.Poly` section.
  Includes `sp1_op_poly` chip-wide def (mirroring Fin KB `sp1_op` with
  `_poly` substitutions). Each theorem ~12 lines: signature + `:= by sorry`.
  The 8 namespaces (`Div`/`Divu`/`Divw`/`Divuw`/`Rem`/`Remu`/`Remw`/`Remuw`)
  are referenced from a single shared poly section via fully-qualified
  `<NS>.spec_<variant>` calls (the spec_<variant> SailM defs are
  field-agnostic).

**What's still open** (in priority order for next session):
1. **`divw_remw_poly` h_abs (line 4371) + h_sign (line 4375)**: existing
   sorries from prior session. Per memory's prior multi-attempt SO history,
   recommended approach is to extract case lemmas (`divw_remw_h_abs_case{1,2,3,4}_poly`)
   as top-level helpers above `divw_remw_poly` plus an h_sign extraction.
   Existing bridge `Word_toInt_poly_neg_form_eq_HWord_toInt_poly` (line 1291)
   already handles negative-case bridging.
2. **`div_rem_poly` body**: ~600 lines port mirroring `divw_remw_poly`'s
   signed structure at full Word width. h_prod follows divuw_remuw_poly
   8-limb carry chain pattern; h_abs/h_sign mirror divw_remw_poly's 4-way
   structure. `sum_zero_abs_poly` (line 1256) usable as-is for 64-bit signed
   (operates on `Word`, which is 4-limb-of-16-bit-each = 64 bits total).
3. **8 `spec.<variant>_poly` chip-local wrappers** in
   `SP1Chips/DivRem/Constraints.lean` (~200 lines each, ~1600 lines total).
   Mechanical mirror of Fin KB `spec.<variant>` (lines 1746/1957/2930/3141/
   4380/4591/5496/5707) with `_poly` substitutions. Each unpacks Main columns,
   destructures cstrs, applies operation `_poly` specs (MulOperation,
   IsEqualWordOperation, U16MSBOperation, AddOperation, LtOperationUnsigned,
   IsZeroWordOperation), then calls the corresponding core (div_rem_poly,
   divu_remu_poly, divw_remw_poly, divuw_remuw_poly) and threads the
   conclusion through `all_goals` closing.
4. **8 `correct_<variant>_poly` chip theorem bodies**: each ~25-30 lines.
   Mirrors Fin KB `correct_<variant>` (DivRemChip.lean:122 etc.) calling
   `correct_prologue_facts_poly` (line 78) for prologue and
   `<NS>.spec.<variant>_poly` (Phase 3 above) for the witness.

**Why this checkpoint shape**: realistic build cycle is 17-21 min for
`lake build SP1Chips.DivRem.Constraints`, so iterating on full proof bodies
in one session burns hours per iteration. The scaffolding strategy delivers
the complete API surface (8 `correct_*_poly` discoverable signatures +
matching `sp1_op_poly` operational spec) so future sessions can fill bodies
incrementally without churning the file shape.

**`divw_remw_poly` h_prod LANDED 2026-05-08** (uncommitted, verified under `lake build`):
Closed the h_prod sorry inside `divw_remw_poly` at `SP1Chips/DivRem/Constraints.lean:4204`.
Build #7 (lake build SP1Chips.DivRem.Constraints) exited 0 with only the expected
`declaration uses sorry` warning from h_abs/h_sign. Build cycle: 17–21 min.

Recipe: mirrors Fin KB `divw_remw` lines 3611–3672 with `_poly` substitutions, plus
divuw_remuw_poly's hsum/eq/main_eq carry chain pattern (lines 5273-5372) for the inner
`bv_ctqr` proof. Key local helpers introduced in h_prod's body:
- `u16_msb_b_v / u16_msb_c_v / u16_msb_rem_v / u16_msb_quot_v`: `(msb_X * 65535).val < 65536`
  via `rw [w_eq_msb_X]; split_ifs <;> simp [h0v, h65535_val]`.
- `heq32_b1`/`heq32_c1`: ZMod LE → .val LE bridges (heq32_q1/heq32_r1 already in outer scope).
- `eq_eb / eq_er / eq_eq / eq_ec`: 4-limb sign-extended forms equal `HWord.extend_poly _ true`,
  proved by `simp [HWord.extend_poly, HWord.isNegative_poly, w_eq_msb_X, heq32_X1]`.
- `bv_ctqr`: 4-limb BitVec64 carry-chain equality. Stage A derives h_prod from bv_ctqr via
  `extractLsb_is_toInt` + signed multiplication via `HWord.extend_true_is_signExtend_poly` +
  `BitVec.toInt_signExtend_of_le` + `Int.bmod_eq_of_le`. Stage B proves bv_ctqr via
  hsum01..hsum3 (`ZMod.val_add_of_lt`) → eq0..eq3 (Nat carry equations with `(msb_b * 65535).val`
  and `(msb_rem * 65535).val` in upper limbs) → main_eq (linear combination weighted by 2^16i)
  → `← BitVec.toNat_inj` + 3 `rw [show Word.toBitVec64_poly ... = BitVec.ofNat 64 ... from by
  simp [Word.toBitVec64_poly, Word.toNat_poly]]` rewrites + `omega`.
Heartbeats: 32M (existing on lemma, sufficient).

Two non-obvious gotchas hit during port (would have saved ~2 build cycles):
1. **`div_zero'` derivation**: the `if c0 = 0 ∧ c1 = 0` synthesized condition is
   already a 3-conjunction (`c0 = 0 ∧ c1 = 0 ∧ msb_c * 65535 = 0`) since `div_zero`
   from constraints expands `Word.eq_pointwise` over 3 limbs. Direct projection
   `exact hzc ⟨hvec.1, hvec.2.1⟩` works; do NOT try `rw [← Word.eq_pointwise]` —
   `hvec` is the conjunction, not a Word equality.
2. **`simp only [...] at h1 h2 \n h3 h4` is a syntax error.** Lean 4's `colGt` rule
   requires every identifier in the `at` list be on the same line as `at` OR have
   column strictly > `at`'s column. With deep indentation, easier to put the whole
   `at` list on one line (linter.style.longLine is globally off in this repo).

**h_abs attempts 2026-05-08 — 3 attempts, all failed**:

**Attempt 1 (build #8)**: subst-based, 42 errors. `subst msb_rem`/`subst msb_c`
consumed `rem_nneg`/`c_nneg`/`rem_neg`/`c_neg` before downstream uses.
Other issues: `(by decide)` for `(0:ZMod p) ≠ 1` (need `zero_ne_one` under
free p); `c_neg_sum_zero rfl` (need `c_neg_sum_zero c_neg`).

**Attempt 2 (build #9)**: refined — no subst msb_*, `zero_ne_one` instead
of decide, `c_neg_sum_zero c_neg`, plus `clear` of ~30 unused hypotheses
(is_U64_b/c, u16_ctqpr*, u16_q*, b_cry*, u16_ctq*, b_is_*, b_b_neg_*,
eq_b_neg*, main_mul_low, is_U32_bl, lb/ub_b/q, ext_q/r, nof_eq_ctqpr0..7,
sgn_msb_b, h_prod). **Result: "Stack overflow detected. Aborting." at
903s wall (15 min).** Even with reduced context + tstack=400000, the
4-way case-split body (each case ~25 lines with `have`/`subst`/`obtain`
chains plus `sum_zero_abs_poly` applications) overwhelms the elaborator
stack.

**Conclusion**: under `lake build` (proper tstack=400000), h_abs as
an in-place `have` block in `divw_remw_poly`'s body is **NOT viable**.
The hypothesis context (~150 ZMod p Nat predicates) plus the 4-way case
proof's tactical depth exceeds the 400000-byte stack.

**Attempt 3 (build #10)**: extracted `divw_remw_h_abs_witness_poly` as a
top-level lemma BEFORE `divw_remw_poly` with ~40 explicit args. Build
**also failed with "Stack overflow detected. Aborting."** at 8 min wall
(faster than the 15 min in-place attempt). **This proves the SO is in
TACTIC COMPLEXITY, not just hypothesis context size.** The 4-way case
split with `sum_zero_abs_poly` applications + `unfold` + nested
`Word.toInt_poly` ↔ `HWord.toInt_poly` bridges (each case ~25 lines)
overwhelms the elaborator stack even when the hypothesis context is
small. Reverted; sorry preserved.

**Attempts 4-7 (builds #11-#16)**: 4-per-case-lemma split strategy.
- **Build #11**: case 1 alone (~70 lines, no sum_zero_abs_poly): COMPILES
  cleanly under 21 min. Per-case extraction is viable for simple cases.
- **Build #13**: cases 1+2+3+4 + h_abs combiner: SO at 6:24.
- **Build #14**: cases 1+2+3+4 (bodies) + sorry combiner: SO at 6:24.
- **Build #15**: cases 1+2 (bodies) + cases 3+4 (sorry'd bodies): SO at
  6:31. So even one extra case body (case 2) plus sorry'd 3+4 SO's.
- **Build #16**: cases 1+2 (bodies) + cases 3,4 deleted: SO at 6:19.

**Conclusion**: case 1 alone is fine but adding ANY of cases 2-4 with full
body triggers SO at ~6 min wall. The shared structure of cases 2-4 that
case 1 lacks: `sum_zero_abs_poly` application + the `Word.toInt_poly`
↔ `HWord.toInt_poly` bridge proof (`unfold` of 6 definitions + `simp only` +
`rw [if_pos]` + `push_cast; ring`). The 6-def `unfold` chain is the
prime suspect.

**Path forward for the next attempt**: extract the bridge as a separate
top-level lemma `Word_toInt_poly_eq_HWord_toInt_poly_when_neg_poly`:
```
lemma ... {p : ℕ} [NeZero p] [Fact (2^17 < p)] {c0 c1 : ZMod p}
    (is_U32 : HWord.isU32_poly #v[c0, c1])
    (h_neg : (32768 : ZMod p) ≤ c1)
    (h32768_val : (32768 : ZMod p).val = 32768)
    (h65535_val : (65535 : ZMod p).val = 65535) :
    Word.toInt_poly #v[c0, c1, 65535, 65535] = HWord.toInt_poly #v[c0, c1] := ...
```
Prove it ONCE outside any case lemma. Then cases 2/3/4 use just
`rw [Word_toInt_poly_eq_HWord_toInt_poly_when_neg_poly is_U32_cl h_c1_ge32k h32768_val h65535_val]`
without their own unfold chain. This should avoid the SO.

Same approach almost certainly applies to h_sign (which also has nested
case splits and similar bridges).

**divw_remw_poly h_abs STILL OPEN** (attempted 2026-05-08, two stack overflows at SAME timing):

**Attempt 1 — full 4-case proof with `eqWH` universal helper using `unfold`** (~120 lines):
Triggered "Stack overflow detected. Aborting." at lean elapsed ~16:08.

**Attempt 2 — case 1 only, no `eqWH`, `simp only` instead of `unfold`** (~80 lines):
Also triggered "Stack overflow detected. Aborting." at lean elapsed ~16:11.

**The consistent timing across two structurally different attempts strongly suggests the
SO trigger is NOT in my specific tactics** (eqWH unfold, simp_all, etc.) but in something
common to both — most likely the destructive `simp [rem_nneg, c_nneg] at *` against the
200+ hypothesis context, OR the cumulative haveset (helper lemmas at h_abs entry +
case-specific haves) overwhelming the elaborator stack. The h_sign proof which DOES use
`simp [b_msb_nneg] at *` works, but it has only ONE flag rewrite, not two.

Empirically known to be safe: `rcases b_rem_neg <;> rcases b_c_neg <;> sorry` (structural
case split alone) compiles fine. So the SO is in the case bodies.

**Stack overflow ROOT CAUSE FOUND 2026-05-08**: `lake env lean` does NOT pass
`--tstack=400000` (only `lake build` does). Running with `lake build` fixes the
SO. So previous SO attempts were a tooling artifact, not a tactic problem. With
`lake build`, h_prod compiles cleanly in ~17 min for the full Constraints.lean
file. h_abs is still sorry'd but no longer blocked by tstack.

**IMPORTANT 2026-05-08**: After running with `lake build` (proper tstack), the
extracted h_prod proof I had written (~150 lines) DID NOT actually compile
cleanly — it errored at line 4258 (`apply HWord.isU32_of_cases_poly <;> simpa`
fails because `c0.val < 65536` and `c1.val < 65536` are NOT in scope as
hypotheses; only `is_U64_c : Word.isU64_poly #v[c0,c1,c2,c3]` is given). The
earlier "successful" `lake env lean` builds were fooled — the SO during h_sign
elaboration short-circuited the build before reaching h_prod's failure mode.
Multiple OTHER errors in the divw_remw_poly body also surface under `lake build`:
- Line 4043: `obtain ⟨h0, h1⟩ := h_zc` in `div_zero'` — unknown identifier
- Lines 4291, 4292, 4386: omega failures
- Line 4395: `c, q, r` unknown in h_sign's `all_goals`
- Lines 4258, 4479: `simpa` and `assumption` failures

This means **the entire user-supplied divw_remw_poly was never actually
verified** under proper tstack — its h_prod, h_abs, h_sign proofs all rely on
hypotheses that aren't there, OR have name-shadowing issues with the imported
`divw_remw` Fin KB lemma. Reverted: divw_remw_poly's three witnesses
(h_prod/h_abs/h_sign) are ALL `sorry` again. The h_prod body I wrote is
preserved at `/tmp/h_prod_body.lean` and `/tmp/h_sign_body.lean` for reference;
they need to be re-attempted with `lake build` after fixing the missing-bound
issues (need to derive `c0.val < 65536` etc. via `Word.lt_cases_of_isU64_poly
is_U64_c`).

**Extraction-to-helper-file attempted 2026-05-08 — REVERTED**: tried to lift
`divw_remw_poly` into `SP1Chips/DivRem/DivWRemWPoly.lean` (importing
`SP1Chips.DivRem.Constraints`) to enable per-iteration ~3-4 min builds instead
of the 15-18 min full Constraints.lean rebuild. The lemma compiled at the
signature/early-body level but exhibited subtle elaboration differences vs
in-file context — `apply Int.split_nzp q ... [skip; simp_all; skip]; all_goals`
in h_sign reported `Unknown identifier c, q, r` inside `all_goals` body (the
`set q := ... ; set c := ...; set r := ...; clear *- rpos h_abs hw` chain
worked in-file but the let-bindings appear to not survive the elaborator's
handling once h_sign is in a separate file). Also when h_sign was sorry'd to
isolate, *additional* errors appeared at lines 264 (`obtain ⟨h0, h1⟩ := h_zc`),
326, 305, 422, 402, 479, 512, 513 — suggesting the elaboration in the smaller
file context differs from the in-place version in multiple subtle ways.
Root cause not isolated; likely `simp at *` normalization differences, or the
imported `divw_remw` (Fin KB) lemma name shadowing the local `intro divw_remw`
hypothesis (renaming to `h_divw_remw` resolved the line 264 error specifically
but exposed others).

Reverted: DivWRemWPoly.lean deleted, `divw_remw_poly` restored in
Constraints.lean. The user wanted helper files for compile-time speedup, but
this particular lemma's body has too many subtle elaboration dependencies on
its surrounding file to extract cleanly without further refactoring (e.g.,
extracting it as a *standalone top-level lemma* with all hypotheses as
explicit arguments, rather than as a body of a wrapping ∀-statement, would
likely sidestep the issues — strategy #2 from the prior list).

**Mitigation strategies (untried) for the next h_abs attempt:**
1. **Avoid `simp at *` entirely.** Use `subst msb_rem` (since `rem_nneg : msb_rem = 0` is in
   the form `var = expr`) to do the variable substitution structurally, then targeted
   `simp only [...] at <specific>` for any remaining cleanup.
2. **Extract h_abs as a separate top-level lemma** (outside divw_remw_poly's body) with its
   own argument list. The smaller fresh hypothesis context inside the new lemma's body would
   give the elaborator a much smaller stack footprint per tactic.
3. **Reduce upfront helpers**: skip `is_U64_ar/is_U64_ac/cls/rls/heq32_c1/h65535_v` at h_abs
   entry; derive them inline per case where needed. Smaller initial context → smaller
   per-case context.
4. **Alternative approach**: instead of bridging Word↔HWord toInt_poly via the
   `Word.toInt_poly = HWord.toInt_poly` equality, work directly at `Word.toNat_poly` /
   `Word.toInt_poly` level using `sum_zero_abs_poly`'s output directly. This avoids the
   deeply nested term unfolding that may stress elaboration.

Now that the tstack issue is resolved (use `lake build`, not `lake env lean`),
build cycle is ~17 min for the full Constraints.lean rebuild. Each h_abs
attempt costs ~17 min.

Plan file: `/home/dtumad/.claude/plans/make-a-plan-to-velvety-meteor.md`.

---

**divw_remw_poly PARTIAL 2026-05-08** (signed 32-bit, ~290 lines landed with 4 named sorries):

What's done (mirrors `divuw_remuw_poly` recipe):
- Lemma scaffold: same option block (`debug.skipKernelTC, maxHeartbeats 32M, maxRecDepth 1M`), same 113-arg ZMod p signature, intro guard `is_divw + is_remw = 1`.
- Upfront prep: `h01, h21, h65535_val, h32768_val, h0v, h1v, hcv0..hcv3` (carry bounds derived BEFORE any `simp_all` to keep `Fact (2^17 < p)` from collapsing to `Fact True`).
- 6-way sopX collapse: explicit `rcases b_is_divw <;> rcases b_is_remw` with `(0,0)/(1,1)` exfalso via `h01/h21` and `(0,1)/(1,0)` destructure of `sop6/sop5`. Mirrors divuw_remuw_poly pattern; sop6/sop5 conjunction order is `is_div ∧ is_divu ∧ is_rem ∧ is_remu ∧ {is_divw|is_remw} ∧ is_divuw ∧ is_remuw`.
- Pre-suffices setup: subst chain (lb*/lc*/qbc*/rbc*/abs_*/b_neg/rem_neg/c_neg), `simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, Bool.cond_eq_ite, -BitVec.toInt_setWidth]`, `Word.setWidth_eq_low_poly`, `Word.isU64_poly_low_poly_isU32_poly`, `simp [Word.low_poly] at *`, `HWord.toBitVec32_poly_toInt_poly` (signed!), `heq32_q1`/`heq32_r1` value bridges, `ext_q`/`ext_r` with sign-extend (`HWord.extend_poly _ true` — NOT false like unsigned), `HWord.extend_true_is_signExtend_poly`, signed bound helpers `lb_b/ub_b/lb_c/ub_c`.
- c=0 branch (clean, no sorry): obtain ⟨zc0, zc1⟩, derive `hzero_int : HWord.toInt_poly #v[(0:ZMod p), 0] = 0`, simp + `BitVec.toInt_signExtend_of_le` + `HWord.toBitVec32_poly_toInt_poly` + `Int.bmod_eq_of_le` close.
- Overflow branch (clean, no sorry): rcases on `b_is_overflow`, splits on `w_overflow_b`/`w_overflow_c`, uses `of_eq_q*/r*`, closes via simp on `HWord.toBitVec32_poly, HWord.toInt_poly, HWord.isNegative_poly, HWord.toNat_poly` with explicit `[h0v, h32768_val, h65535_val]` for the literal vector reductions.
- c≠0, non-overflow main path: scaffolded with `is_U32_rl/ql`, `lb_q/ub_q/lb_r/ub_r`, the `suffices` pattern, `sgn_msb_b/c/rem` Int.sign helpers, `cnz : HWord.toInt_poly #v[c0, c1] ≠ 0`, then `tdiv_tmod_unique_full cnz` (field-agnostic, usable as-is).

What's NOT done (4 sorries):
1. **`div_zero'` derivation** (line ~4032): The Fin KB `aesop` close fails for ZMod p because aesop doesn't have `Fact (2^17 < p)` in scope after `clear *-` and can't decide `(65535 : ZMod p) ≠ 0`. **Fix attempted**: explicit `split_ifs with hc heq` + 4-case proof using `h65535_ne` + `simp at heq ⊢`. Still need to verify.
2. **`h_prod`** (line ~4192): Signed product witness (~60 lines). Mirrors Fin KB `divw_remw` lines 3589-3650. Uses `extractLsb_is_toInt` (field-agnostic), bv_decide on `BitVec.extend` form, `extend_true_is_signExtend_poly`, the signed bv_ctqr arm with `msb_b * 65535` / `msb_rem * 65535` sign-extends (NOT zero-extends like unsigned). Carry chain mirrors divuw_remuw_poly's `hsum*/eq*/main_eq` pattern but with sign-extended b.
3. **`h_abs`** (line ~4196): 4-way abs witness (~95 lines). Mirrors Fin KB lines 3652-3748. Uses `sum_zero_abs_poly` helper (just landed in same commit as the partial). 4-way `b_rem_neg × b_c_neg` case analysis — each case uses `sum_zero_abs_poly` to bridge `Word.toBitVec64_poly = ...sum...` to abs values.
4. **`h_sign`** (line ~4202): Sign witness (~25 lines). Mirrors Fin KB lines 3750-3774. b_msb_nneg branch closes via `HWord.sign_cases_poly` + `h_prod` + `h_abs` + nlinarith. b_msb_neg branch closes via `Int.sign_eq_neg_one_of_neg sgn_msb_b` + the `r_pos_b_pos` case-split. Second branch's `simp_all` close in Fin KB (for `r0+r1+r2+r3 = 0` → `HWord.toInt = 0`) needs explicit ZMod-to-Nat bridging in poly.

How to apply: the 4 sorries are well-bounded with explicit named TODOs in the file. Each will need ~30-90 min focused work. Recommend tackling in order: div_zero' (smallest, mostly tactical), h_sign (smallest of the witnesses), h_prod (heaviest mathematical content, mirror divuw_remuw_poly carry chain at sign-extended width), h_abs (4-way case analysis using sum_zero_abs_poly).

Helpers already landed in same commit:
- `sum_zero_abs_poly` (in `SP1Chips/DivRem/Constraints.lean` near line 1256, beside `sum_zero_abs`).

Key helpers from `SP1Foundations/Word.lean` (all exist):
- `HWord.{toBitVec32_poly_toInt_poly, toInt_lb_poly, toInt_ub_poly, eq_toInt_eq_poly, sign_cases_poly, isNegative_poly_toInt_poly, isU32_of_cases_poly, lt_cases_of_isU32_poly, toNat_poly_lt_of_isU32_poly, isNegative_poly}`
- `Word.{isU64_poly_toInt_poly, isNegative_poly_toInt_poly, toBitVec64_poly_toInt_poly, isU64_poly_low_poly_isU32_poly, low_poly, setWidth_eq_low_poly}`

Field-agnostic helpers (usable as-is):
- `tdiv_tmod_unique_full` (line 1180), `extractLsb_is_toInt` (line 1254 → 1276 after sum_zero_abs_poly insertion)

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
