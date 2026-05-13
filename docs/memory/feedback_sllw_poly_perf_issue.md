---
name: spec-sllw-poly-build-time-blowup-needs-restructure
description: My first spec.sllw_poly attempt elaborates >17 min vs spec.sll_poly's ~80s baseline. The outer setup needs to be split into smaller named lemmas that elaborate independently — landing the proof inline blows past Sllw.lean's ~5 min existing baseline.
metadata:
  type: feedback
  originSessionId: d13f597f-47d0-47b7-9a65-f20721f2701f
---

When porting `spec.sllw_poly` (and its W-variant siblings), do NOT inline the
entire proof in one `lemma spec.sllw_poly := by ...` block. Even though
`spec.sll_poly` (Fin-KB version's analog) builds Sll.lean in 87s with 64
sub-cases, my Sllw.lean attempt with the analogous outer setup + just 1 of 32
sub-cases hung past 17 min build time and never completed.

**Backup of the attempted proof body**: `/tmp/Sllw.lean.bak` (in this session).

**Most likely culprits in the slow outer setup** (in decreasing suspicion order):
1. `simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly,
   LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]` — `Word.low_poly`
   does not get unfolded by these simp lemmas, leaving the goal RHS in a
   weird half-reduced state.
2. The `change Word.toBitVec64_poly #v[a0,a1,a2,a3] = BitVec.signExtend 64 (...)`
   tactic that follows the simp — `change` has to defeq-check the full
   `Word.low_poly #v[b0,b1,b2,b3] = #v[b0,b1]` reduction, which is expensive.
3. The `h_setWidth5 : BitVec.setWidth 5 (HWord.toBitVec32_poly #v[c0,c1])
   = BitVec.ofNat 5 (c0.val % 32)` derivation.
4. Duplicate `h_cb_sum_lt` (6-bit < 64) and `h_cb_sum_5_lt` (5-bit ≤ 31)
   computations — each is ~80 lines of `ZMod.val_mul_of_lt` + `ZMod.val_add_of_lt`
   chains.

**Suggested restructure for next attempt:**

Split `spec.sllw_poly` into 3 lemmas:
- `spec.sllw_poly_outer_facts` (private): takes `cstrs` + `h : is_sllw_poly Main`,
  returns a tuple of named hypotheses (h_a2_eq, h_a3_eq, h_msb_a1, h_su45_46_sum,
  h_cb_sum_lt, h_c_mod_64, w_*' resolution, etc.). This isolates the heavy
  outer-setup elaboration into one lemma.
- `spec.sllw_poly_cb4_zero` (private): handles cb4=0 branch, takes the named
  hypotheses + hcb4 = 0, proves the goal.
- `spec.sllw_poly_cb4_one` (private): same for cb4=1.
- `spec.sllw_poly` (public): outer setup + dispatch.

Each lemma elaborates within its own heartbeat budget. Even if each is slow
individually, they don't compound.

**Alternative: avoid the simp+change chain entirely** by using `rw [← BitVec.toNat_inj]`
+ direct toNat manipulation (the way spec.sll_poly does for its
`execute_RTYPE_pure_w_poly .SLL` case). The challenge: `sign_extend` mixes
Nat/Int reasoning, so it's not a pure toNat reduction. Need a different bridge
lemma — perhaps prove a `Word.toBitVec64_poly_eq_iff_limbs` form that
decomposes the goal into 4 limb equalities.

**Helpers landed (all in Common.lean, building clean)** — these are valid
infrastructure for the next attempt:
- `sllw_within_byte_shift_poly` (byte_shift=0, HWord level)
- `sllw_within_byte_shift_1_poly` (byte_shift=1, HWord level)
- `sllw_close_cb4_zero_case` (case wrapper, S ≤ 15)
- `sllw_close_cb4_one_case` (case wrapper, S ∈ [16, 31])
- `sllw_a2_a3_eq_msb_byte` (sign-extension bridge using U16MSBOperation.spec_poly)
- `sllw_subcase_cb4_zero` (combined per-sub-case closer — proven on its own
  at 800K heartbeats, but applying it from spec.sllw_poly was the perf killer)
- `sllw_subcase_cb4_one` (mirror for cb4=1)

The two `sllw_subcase_cb4_*` helpers may be the wrong abstraction — they
do too much per call. Consider DROPPING them and instead having the spec
proof apply `sllw_close_cb4_*_case` directly + handle sign_extend inline.

**Estimated wall-clock to finish**: 4-6h with the restructured architecture
(split into 3 lemmas, simpler per-sub-case closure), vs. the indefinite hang
from the inline approach.

**UPDATE 2026-05-12 (commit `d61dfc3`)**: the 3-lemma restructure SIGNATURES are
landed in `SP1Chips/ShiftLeft/Sllw.lean` with sorry bodies. Sllw.lean builds
clean in ~6 min. Architecture validated. The sketched signatures:

- `private lemma spec.sllw_poly_cb4_zero` — 35 explicit args, body sorry
- `private lemma spec.sllw_poly_cb4_one` — same shape, body sorry
- `lemma spec.sllw_poly` — outer setup commented as TODO, body sorry
- `lemma spec.slliw_poly` — body sorry (mechanical port from spec.sllw_poly)

Next session: fill in the sorry bodies. Detailed execution plan in
`/home/dtumad/.claude/plans/sllw_poly_restructure_sketch.md`.

Key implementation notes for next session:
- Use Strategy B for goal expansion: `simp only [execute_RTYPEW_pure_w_poly,
  execute_RTYPEW_pure_32_w_poly, LeanRV64D.Functions.sign_extend,
  Sail.BitVec.signExtend]` followed by `rw [show #v[Main[15],...].low_poly =
  #v[Main[15], Main[16]] from rfl, ...]` — avoid `change`.
- Apply SHIFTIOP→RTYPE bridge BEFORE `by_cases` to preserve `Fact (2^17 < p)`
  instance (lesson from correct_slli_poly).
- The h_is_op_a_0 = true case needs explicit `h_shift_zero` via `← spec_eq`
  + `Word.toBitVec64_poly` of all-zero vector + `if_pos`.
