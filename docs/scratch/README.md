# Scratch / proof attempts

Contains in-progress proof bodies that didn't compile cleanly under `lake build`
but may be useful as starting points for future work.

## divw_remw_poly_full_body_with_partial_proofs.lean

The full `divw_remw_poly` lemma signature + body (623 lines) as it stood
mid-session 2026-05-08, with my attempted h_prod proof, h_abs as `sorry`, and
the user's pre-existing h_sign body. **None of these compile under `lake build`
with `--tstack=400000`** — multiple errors throughout (line 4043 in `div_zero'`
derivation; line 4258 in h_prod; line 4395 in h_sign). After spending
substantial time iterating, reverted to a fully-`sorry` body in
`SP1Chips/DivRem/Constraints.lean` so the file builds cleanly.

Use this file as the source-of-truth for the existing proof structure when
attempting to fix the witnesses individually. The other two files
(divw_remw_poly_h_prod_attempt.lean and divw_remw_poly_h_sign_original.lean)
are slices from this larger file.

## divw_remw_poly_h_prod_attempt.lean

`h_prod` proof body for `divw_remw_poly` (signed-32-bit DivRem). Originally
written and tested under `lake env lean` (which does NOT pass
`--tstack=400000`); appeared to compile but `lake env lean`'s default tstack
caused the build to short-circuit before reaching the actual elaboration
failure. Under `lake build SP1Chips.DivRem.Constraints` (proper tstack=400000)
the proof errors at the `apply HWord.isU32_of_cases_poly <;> simpa` step:
`simpa` cannot close `c0.val < 65536` / `c1.val < 65536` because those bounds
aren't direct hypotheses (only `is_U64_c : Word.isU64_poly #v[c0,c1,c2,c3]`).

**Fix needed:** derive `c0.val < 65536` and `c1.val < 65536` first via
`have ⟨_, _, _, _⟩ := Word.lt_cases_of_isU64_poly is_U64_c` before the apply
step, then `simpa` will succeed.

## divw_remw_poly_h_sign_original.lean

The user's supplied `h_sign` body (closed before this session per memory but
never verified under `lake build`). Contains `apply Int.split_nzp q ... ;
all_goals` pattern that errors with `Unknown identifier c, q, r` inside
`all_goals` — the `set q := ... ; clear *- rpos h_abs hw` chain doesn't
preserve the `set` let-bindings under proper elaboration.

**Fix needed:** restructure to either (a) use `set` AFTER `clear *-` so the
clear doesn't remove them, or (b) extract h_sign into a separate top-level
lemma with explicit hypotheses (avoids the in-body context issue entirely),
or (c) replace `all_goals` + `simp_all` with explicit case splits where each
case has its own access to the local context.
