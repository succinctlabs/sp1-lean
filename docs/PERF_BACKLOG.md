# Proof-perf backlog: known repeated slowdowns

This doc catalogs perf opportunities surveyed after the `BitwiseU16Operation` fix landed, so a future session can plan an approach without re-deriving the survey.

`docs/PERF_PATTERNS.md` covers wins from PR #92 (instance priorities, breaking obtain chains, etc.). This file covers what is *still* slow and looks fixable with the same toolkit.

## Calibrated next-session proposals (2026-04-25)

A first attempt at the items below already landed the SailM `if_neg` cluster
(Pattern 2). LSP probing during that session showed the original Pattern-1
plan was too optimistic — the post-`simp_all` LHS shape inside the 64-way
ShiftLeft/ShiftRight cascades is heterogeneous, so a single shared helper
does not unify. The proposals below are calibrated to that finding.

A clean **lake build** without changes takes **~600s** end-to-end; ShiftRight
Constraints alone is **366s**, DivRem **271s**, ShiftLeft chip ~15s but its
Constraints file is on the same 100M-heartbeat tier. Optimising those three
files is where almost all the wall-clock leverage sits.

### Proposal A — `clear`-bracketed omega in heavy-context sites (LANDED)

**Status (2026-04-25): measured wins on ShiftLeft + ShiftRight, srlw_common
held back due to omega-context fragility, DivRem in progress.**

The bottleneck the `mod_KB_collapse` win actually exploited was *omega's
context size*, not the `Nat.mod_eq_of_lt` rewrite itself. Wrapping each
`(by omega)` side condition with
`(by clear * - <bound names>; omega)` shrinks omega's hypothesis set to a
small named subset, regardless of how the goal shape varies across rcases
case branches.

**Measured wins (single-file rebuild times):**

| File | Before | After | Δ | Notes |
|---|---|---|---|---|
| `SP1Chips/ShiftLeft/Constraints.lean` | 306s | 196s | **−36%** | All 8 mod-KB sites in sll/slli/sllw/slliw |
| `SP1Chips/ShiftRight/Constraints.lean` | 366s | 284s | **−22%** | Only `srl_common` (1032). `srlw_common` reverted. |
| `SP1Operations/Operation/MulOperation/Constraints.lean` | 119s | 95s | **−20%** | `iterate 15` at line 169 (`core_mul`) + `iterate 3` at line 247 (`core_mulw`). Bound names: `bw00..bw15`, `cw00..cw15`, `lt_cp00..lt_cp15`. |
| `SP1Foundations/SailM.lean` | 32s | 32s | — | (separate `if_neg` cleanup, see Pattern 2) |

**srlw_common gotcha**: After `simp [eq_hl2, eq_ll2, eq_hl3, eq_ll3] at *`
substitutes `hl2 = ll2 = hl3 = ll3 = 0`, the `lt_hl2/lt_hl3/lt_ll2/lt_ll3`
bounds become trivial and `simp_all` removes them. A `clear *-` listing
those names then fails. Workarounds:
1. List only the surviving bound names (`b0_16 b1_16 lt_ll0 lt_ll1 lt_hl0 lt_hl1`),
   plus whatever else omega needs for the now-32-bit-only arithmetic.
2. Wrap with `first | (clear *- ...; omega) | omega` so the fallback to
   plain omega keeps the proof correct when `clear` fails.

The `first` fallback pattern (option 2) was used for the DivRem application
since the per-site context there is harder to predict.

**Sites intentionally NOT changed:**
- `ShiftRight/Constraints.lean:528, 542` (`is_mod_64`) — small lemma, no
  case-split, omega context is already minimal.
- `ShiftRight/Constraints.lean:567` (`limb_16_of_cancel`) — same; the
  surrounding `clear *-` already reduces context.
- `ShiftRight/Constraints.lean:1342, 1343, 1530, 1531` — already preceded
  by an explicit `clear *-` (lines 1340 and 1528). Already optimal.

### Proposal B — Profile before optimising (highest information value)

`mcp__lean-lsp__lean_profile_proof` (description: "SLOW!") will show which
tactic is actually expensive in a given theorem. None of the heavy theorems
have been profiled, so the perf model is hypothesis. Concrete targets:

- `srl_common` / `srlw_common` / `sra_common` / `sraw_common` in
  `SP1Chips/ShiftRight/Constraints.lean` (366s file).
- `sll` / `slli` / `sllw` / `slliw` in `SP1Chips/ShiftLeft/Constraints.lean`.
- `core_mul` / `core_mulw` in `SP1Operations/Operation/MulOperation/Constraints.lean`
  (both carry per-decl `set_option maxHeartbeats 100_000_000`).
- The largest `correct_*` in `SP1Chips/DivRem/Constraints.lean` (271s file).

If the profile shows the `repeat rw` or `simp_all` is dominant, Proposal A
helps. If `grind (ematch := 2048) (splits := 128)` (MulOperation:205) or
`bv_decide` is the hotspot, neither helps and the win is elsewhere.

### Proposal C — Hoist mod-collapse before the 64-way `rcases`

Pattern 5 in this doc, scoped down to a tractable experiment.
`SP1Chips/ShiftLeft/Constraints.lean:614-631` does
`rcases b_cb0 <;> ... <;> rcases b_cb5 <;> simp_all <;> ...`
producing 64 goals. The `repeat rw [Nat.mod_eq_of_lt (by omega)]` inside the
trailing `all_goals` runs **per-case**, so 4 omega calls × 64 cases.

If a uniform identity like
`(↑x + ↑y * c) % 2130706433 = ↑x + ↑y * c` (for some symbolic case-bit
expression `c`) can be proven *before* the rcases — taking the byte/half
bounds as arguments — then `simp only [...] in rcases ...` could amortize
the work across all 64 branches. The challenge is that `c` itself is
case-dependent (`(cb0 + 1) * (cb1 * 3 + 1) * ...`), so the identity has to
quantify over all 64 cases or use a tactic-level abstraction.

### Proposal D — DivRem audit (attempted, abandoned)

`SP1Chips/DivRem/Constraints.lean` is 271s with `iterate N rw [Nat.mod_eq_of_lt …]`
at lines ≈1543, 2358, 3146, 3985 (counts 8/4/4/4).

**Tried Proposal A on site 1543 in two flavors:**

1. **`clear *- u16_ctq0..7 b_cry0..7 ...; omega`** — built (248s, 8% win) but
   linter warnings: the `clear` does nothing (the parent already did
   `clear *- is_U64_b is_U64_c is_U64_q is_U64_r` at line 1485, removing
   `u16_ctq*` long before site 1543 — they're shadowed/consumed). Names
   *appear* available because they're lemma parameters, but they're gone
   by site 1543's local context.

2. **`first | (clear *- is_U64_* is_U16_msb_* nof_eq_ctqpr*; omega) | omega`
   wrapped in `set_option linter.unusedTactic false in iterate 8 …`** —
   built (256s, 5% win) but emits *both* `unusedTactic` and
   `unreachableTactic` warnings; only the former was suppressed. Two more
   set_option layers would be needed.

The fundamental issue: by site 1543, the proof has already done multiple
context-clearing passes, so the `clear *-` hits an already-minimal set
and provides little additional perf benefit. The `first | ... | omega`
fallback's trailing `omega` is provably unreachable in the cases tested,
which the linter correctly flags.

**Conclusion**: site 1543 is not a clean fit for Proposal A. The clear
chain at lines 1485, 1496, 1500 is the *real* perf optimization in this
proof; nothing more to win at site 1543. Sites 2358, 3146, 3985 deserve
a proper check (they're in different lemmas with different `clear` patterns)
but the DivRem 271s budget likely needs a different approach (Proposal B
or restructuring the upstream `clear` chain).

**Reverted in this session — DivRem stays at 271s.**

### Proposal E — `bv_omega` / `decide` / `simp` substitutes

In some sites, `(by omega)` is invoked on a goal that `bv_omega` (the
BitVec-aware variant) or `decide` (when LHS/RHS are closed forms) can close
faster. Worth a `lean_multi_attempt` shootout per representative site.

## Round 2 outcomes (2026-04-25, second session)

A second pass after Proposal A landed. Full `lake build` end-to-end with all
changes (clean-cache rebuild of the post-`SailM`-edit cascade): **~582s** with
zero errors / zero warnings. Key per-file deltas (machine-relative; this
machine runs ~10-15% slower than the doc's earlier baselines):

| File | Pre-session (this machine) | Post-session | Δ |
|---|---|---|---|
| `SP1Chips/ShiftRight/Constraints.lean` | 329s | 290s | **−12%** |
| `SP1Foundations/SailM.lean` | ~32s | 22.6s | **−30%** |
| `SP1Chips/DivRem/Constraints.lean` | ~271s | 268s | within noise |
| `SP1Operations/Operation/MulOperation/Constraints.lean` | ~95s | 107s | within noise |

### Landed

**Proposal F — `srlw_common` `clear *-` with reduced keep list (Pattern 1).**
Doc-section "srlw_common gotcha" workaround #1 turns out to work. Site at
`SP1Chips/ShiftRight/Constraints.lean:1191` now uses
`(by clear * - b0_16 b1_16 lt_ll0 lt_ll1 lt_hl0 lt_hl1; omega)`. The shorter
keep list survives the upstream `simp_all`-driven elimination of
`lt_hl2/lt_hl3/lt_ll2/lt_ll3` (the original blocker), so no `first | … | omega`
fallback is needed. Wall-clock: `lake env lean SP1Chips/ShiftRight/Constraints.lean`
**329s → 290s (~12%)**. The doc previously marked this as "reverted"; it
isn't, with the right keep list.

**`joins`/`divs` lift in `DivRem/Constraints.lean` and `MulOperation/Constraints.lean`.**
Plan-agent insight: the `have joins`/`have divs` over `Fin N` with
`fin_cases <;> norm_num <;> omega` was inlined at four DivRem sites and two
MulOp sites. Lifted to file-private lemmas (`joins_fin4`/`joins_fin8` for
DivRem with base 65536; `joins_byte_fin4`/`joins_byte_fin16` for MulOp with
base 256) so each is elaborated once. Net wall-clock: marginal (within ~5%
noise). Kept for code clarity.

**Proposal A applied to `SailM.lean` `combine_MUL_*` iterate-2 sites.**
Lines 774 and 799 (now 774 and 800 after this round): the `iterate 2 rw
[Nat.mod_eq_of_lt (b := 2^64) (by omega)]` after `apply Word.lt_cases_of_isU64`
benefits from `clear * - isU64_pl isU64_ph` even though the bounds remain
conjunction-shaped — context shrinks from ~15 hypotheses to 2. Wall-clock:
**~32s → 22.6s (~30%)**. The doc previously had this as "no win" via Pattern
2 only; the iterate sites were a separate, untested target.

### Tried, did not help

**`clear * -` on DivRem mod-collapse iterate sites.** Tested at site 2378
with keep list `is_U64_b is_U64_r is_U64_q is_U64_ctql is_U64_ctqh`
(conjunctions, not flat inequalities like ShiftRight). DivRem rebuild went
**268s → 311s (43s regression)**, reverted. Hypothesis: omega is *slower*
when handed a small set of conjunctions vs. a larger set of already-flat
inequalities, because each conjunction has to be destructured. Sites 3163
and 3998 left at original `(by omega)` for the same reason. The doc's
pessimism about Proposal A in DivRem holds — at least without first running
`apply Word.lt_cases_of_isU64 at is_U64_*` to flatten the bound shape, which
is a larger refactor.

**`Bitwise/Constraints.lean:212`.** Live context already minimal (8 byte
bounds via upstream `clear *- hr0..hr7`); helper-lemma or refine variants
save ~100ms in a 10s file. Skipped — disproportionate to risk.

### Calibrated for next session

- **Try flattening DivRem bounds before iterate sites.** Per-site experiment:
  insert `apply Word.lt_cases_of_isU64 at is_U64_b is_U64_r is_U64_q
  is_U64_ctql is_U64_ctqh` *before* the iterate, then apply the (now-flat)
  keep list. The 43s regression at 2378 likely flips to a win if omega gets
  raw inequalities. Validate carefully — destructuring renames hypotheses
  and may break downstream tactics.
- **Profile srlw_common, sra_common, sraw_common.** With srlw_common's site
  1191 closed, the remaining ShiftRight floor is dominated by the 64-way
  rcases cascades (Pattern 5). `lean_profile_proof` would tell us if `simp_all`
  per case is the cost or something else.
- **Targeted `simp only [...] at h` for known leaky `simp_all` calls.** The
  `simp at *` lines 1573 / 2386 / 3170 / 4001 in DivRem (after the lifted
  `joins`/`divs` rewrites) are candidates: replace with `simp only [Fin.val_add,
  Fin.val_mul] at *` once we know what the original was normalizing.

## Reference precedent: `BitwiseU16Operation` mod-collapse helper

The pattern fix is in `SP1Operations/Operation/BitwiseU16Operation.lean`:

```lean
private lemma mod_KB_collapse
    {r0 r1 r2 r3 r4 r5 r6 r7 : ℕ}
    (hr0 : r0 < 256) (hr1 : r1 < 256) (hr2 : r2 < 256) (hr3 : r3 < 256)
    (hr4 : r4 < 256) (hr5 : r5 < 256) (hr6 : r6 < 256) (hr7 : r7 < 256) :
    (r0 + r1 * 256) % 2130706433 +
          (r2 + r3 * 256) % 2130706433 * 65536 +
        (r4 + r5 * 256) % 2130706433 * 4294967296 +
      (r6 + r7 * 256) % 2130706433 * 281474976710656 =
    r0 + r1 * 256 + (r2 + r3 * 256) * 65536 +
      (r4 + r5 * 256) * 4294967296 +
        (r6 + r7 * 256) * 281474976710656 := by
  rw [Nat.mod_eq_of_lt (a := r0 + r1 * 256) (by omega)]
  rw [Nat.mod_eq_of_lt (a := r2 + r3 * 256) (by omega)]
  rw [Nat.mod_eq_of_lt (a := r4 + r5 * 256) (by omega)]
  rw [Nat.mod_eq_of_lt (a := r6 + r7 * 256) (by omega)]
```

Three call-sites of `repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]` were replaced with one `rw [mod_KB_collapse hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7]` each.

**Wall-clock impact for that file alone**: 33s → 6.7s elaboration, ~5×. The win comes from running `omega` four times against an isolated 8-hypothesis context once (at lemma elaboration time) instead of three sites × four iterations × full ~40-hypothesis context.

The same shape is reusable across the codebase wherever a fixed-shape sum-of-bytes is being mod-stripped.

## Pattern 1 (highest leverage): `repeat rw [Nat.mod_eq_of_lt (b := <KB>) (by omega)]`

**Status (2026-04-25): NOT cleanly applicable to ShiftLeft/ShiftRight.**
LSP probes at `SP1Chips/ShiftLeft/Constraints.lean:626` show the post-`simp_all`
LHS shape varies across all 64 case-split branches: different multipliers
(2, 256, 1024, …), different summand counts (sometimes only 2 of the 4 limbs
remain after `simp_all` collapses zero terms), and the surrounding RHS is a
final `mod 2^64` reduction rather than a clean `mod KB` identity. A single
`mod_KB_collapse_hword4` helper does NOT fit. Two avenues for a future
session:
1. **Per-case `clear *-`** in the `(by omega)` side condition to localize
   omega's working set. Multi-attempt confirmed both forms succeed; would
   need a real wall-clock measurement before committing.
2. **Restructure the proof** so the rewrite happens *before* the 64-way
   `rcases` rather than inside `all_goals`. Larger refactor, higher risk.

Bitwise/Constraints.lean (lines 210-212) was also probed: the goal already
runs `clear *- hr0..hr7` at line 209, leaving omega with only 8 byte-bound
hypotheses. Total file build is 10.9s — small absolute leverage.

Original analysis below for reference.

24 occurrences across 6 files. All have the form: a fixed sum of `Fin KB` byte-bounded terms shaped like `(rᵢ + rⱼ * 256) % 2130706433`, justified by `< 256` byte bounds already in scope.

Multiple sites sit inside `all_goals { ... }` after a 6-way `rcases b_cb0 <;> ... <;> rcases b_cb5` cascade — meaning the `repeat` runs once per case in a 64-way split, and `omega` runs 4 × 64 = 256 times against the full hypothesis context. Hoisting the equation to a lemma proven once before the rcases would give the biggest wins here.

| File | Lines | Heartbeat budget | Notes |
|---|---|---|---|
| `SP1Chips/ShiftLeft/Constraints.lean` | 389, 403, 626, 629, 733, 736, 838, 865, 967, 994 | 100M (file-level) | Several inside 64-way `rcases` cascades at 614-615, 721-722, 835, 964. Highest leverage in the codebase. |
| `SP1Chips/ShiftRight/Constraints.lean` | 528, 542, 567, 1032, 1189, 1338-1339, 1526-1527 | 100M (file-level) | Same 64-way cascade at 1022-1024. Lines 1338-1339 chain two `repeat rw` of the same lemma at different `(a := _ * _)` patterns — could merge. |
| `SP1Operations/Operation/MulOperation/Constraints.lean` | 190, 254 (+ `iterate 3` at 241) | 100M (decl-level on lines 86, 207) | Line 254 has `(by clear eq_p00 eq_p01 eq_p02 eq_p03; grind)` — manual context-clear because grind/omega can't keep up otherwise. Strong "context too big" signal. |
| `SP1Chips/Bitwise/Constraints.lean` | 210, 212 | (none) | Inside `all_goals { }` after a 3-way rcases on `xor / and / or`. Two adjacent `repeat rw` (`Fin.lt_def, Fin.val_add, Fin.val_mul` then `Nat.mod_eq_of_lt`) — both could fold into one helper. |
| `SP1Foundations/BitVec.lean` | 88, 90 | (none) | Lower-level helper file, smaller scope. |
| `SP1Operations/Operation/BitwiseU16Operation.lean` | — | 10M | **Already fixed.** Listed for cross-reference. |

### Helper-lemma reuse question to investigate

The `mod_KB_collapse` shape (sum of four `(rᵢ + rⱼ * 256) % KB` terms with byte bounds) may not be quite the right shape for ShiftLeft/ShiftRight, where the addends typically involve products like `((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ...)` that depend on the case-split bits. Worth eye-balling each `all_goals` body to see whether the post-`simp_all` LHS is structurally fixed, or whether each case actually wants a different shape (in which case the helper has to be parametric in the multipliers).

If the shape *is* fixed across multiple files, the helper belongs in `SP1Foundations/Word.lean` or `SP1Foundations/BitVec.lean` for shared use. If it's per-file, keep it `private` at the top of each chip's namespace like `BitwiseU16Operation` does.

## Pattern 2 (correctness + perf): `repeat rw [if_neg (by … simp_all)]`

**Status (2026-04-25): partially landed.** 7 of the 8 sites were rewritten to
use private helpers `toNat_ne_zero_of_ne_zero` / `toInt_ne_zero_of_ne_zero`
defined at the top of `SailM.lean`. Site at line 1139 (now ~1145) is a
different `(by simp; omega)` proof, not an `r2 ≠ 0` discharge — left as-is.

Wall-clock: 32.4s → 31.6s (~3% faster). Main win is correctness (7 fewer
`simp_all` calls in the leaky-`simp_all` repo per CLAUDE.md commit `419ee1d`).

Original analysis below for reference.

`SP1Foundations/SailM.lean` — 8 sites: 1049, 1114, 1128, 1133, 1176, 1191, 1215, 1240.

```lean
repeat rw [ if_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
```

Worst variant of the pattern: `simp_all` runs in the side-condition proof of every `repeat` iteration. Two problems compound:

1. **Perf**: `simp_all` scans the full local context per iteration.
2. **Correctness**: CLAUDE.md flags `simp_all` as leaky in this repo (commit `419ee1d` "temp patch for leaky simp_all"). Each side-condition discharge is a fresh opportunity for the leak to bite.

The side conditions all assert "r2 ≠ 0" in different forms (`r2.toNat ≠ 0`, `r2.toInt = 0` negation). Two small dedicated lemmas would suffice:

```lean
private lemma toNat_ne_zero_of_ne_zero {r : BitVec n} (h : r ≠ 0) : r.toNat ≠ 0
private lemma toInt_ne_zero_of_ne_zero  {r : BitVec n} (h : r ≠ 0) : r.toInt ≠ 0
```

Both follow from `BitVec.toNat_inj` / `BitVec.toInt_inj` plus the existing `r2z : r2 ≠ 0`. Replace each `repeat rw [if_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all)]` with `rw [if_neg (toNat_ne_zero_of_ne_zero r2z)]` etc. Bonus: removes 8 `simp_all` calls from the file.

## Pattern 3: `iterate 3 rw [Nat.mod_eq_of_lt …]`

`SP1Operations/Operation/MulOperation/Constraints.lean:241`. Same as `repeat`, fixed count. Folds into the Pattern-1 helper.

## Pattern 4: nested `repeat apply` chain with tactic side terms

`SP1Operations/Operation/MulOperation/Constraints.lean:199`:

```lean
· repeat apply mod_add_split _ (by apply mod_mul_split (by rfl) (by simp))
```

Each iteration re-elaborates the inner `apply mod_mul_split (by rfl) (by simp)`. Probably dwarfed by the `grind (ematch := 2048) (splits := 128)` two lines later, but worth bundling into a `mod_split_chain` helper if/when this lemma is touched.

## Pattern 5 (structural, harder): 64-way `rcases` + per-case `simp_all`

`SP1Chips/Shift{Left,Right}/Constraints.lean` — the `rcases b_cb0 <;> rcases b_cb1 <;> ... <;> rcases b_cb5 <;> simp_all` cascades produce 64 large goals and run `simp_all` (leaky) on each. The cases differ in bit-pattern arithmetic that may be amenable to a single algebraic lemma instead of 64 separate `simp_all` closures.

This is a more ambitious refactor than Patterns 1-3 and probably wants its own session.

## Heartbeat heat-map (proxy for "where is the time going")

Declarations or files with bumped budgets, sorted by budget:

```
SP1Operations/Operation/MulOperation/Constraints.lean   86, 207   100M (per-decl)
SP1Chips/ShiftRight/Constraints.lean                    12        100M (file)
SP1Chips/ShiftLeft/Constraints.lean                     10        100M (file)
SP1Chips/DivRem/Constraints.lean                        13        100M (file)
SP1Foundations/SailM.lean                               12         10M (file)
SP1Operations/Operation/BitwiseU16Operation.lean        8          10M (file) [just fixed]
SP1Operations/Compare/LtOperationSigned.lean            121         10M (per-decl)
SP1Chips/JalrChip.lean                                  32          10M (per-decl)
SP1Chips/BranchChip.lean                                45,153,...   2-8M (six branches)
```

DivRem doesn't show up explicitly in the Pattern-1 catalog above but is in the 100M tier — worth a `grep -n "Nat.mod_eq_of_lt\|simp_all\|repeat rw" SP1Chips/DivRem/Constraints.lean` pass before planning.

## Suggested rollout order

If maximizing wall-clock impact per unit work:

1. **`SP1Chips/ShiftLeft/Constraints.lean`** (Pattern 1, 10 sites, 64-way cascades) — likely the single biggest perf delta.
2. **`SP1Chips/ShiftRight/Constraints.lean`** (Pattern 1, 8 sites, same shape).
3. **`SP1Operations/Operation/MulOperation/Constraints.lean`** (Pattern 1 + 3 + 4, plus the `(by clear …; grind)` smell).
4. **`SP1Foundations/SailM.lean` `if_neg` cluster** (Pattern 2, 8 sites; correctness win on top of perf).
5. **`SP1Chips/Bitwise/Constraints.lean`** (Pattern 1, 2 sites; small but rounds out the U16 surface and probably reuses the same helper as `BitwiseU16Operation`).
6. **DivRem audit** — file budget says 100M, but it didn't surface explicit `repeat rw` sites in the initial grep. Profile first, then plan.

Items 1-3 may share a single helper lemma if the post-`simp_all` LHS shape is structurally identical. That's the first thing to verify in a planning session — read the goal state at each `repeat rw` site (via `mcp__lean-lsp__lean_goal`) and compare LHS shapes.

## Verification recipe

For each file touched:

```sh
touch <file>.lean
/usr/bin/time -f "elapsed: %e s" lake build <Module>          # before
# apply changes
/usr/bin/time -f "elapsed: %e s" lake build <Module>          # after
grep -cE '^(error|warning):' <build-log>                      # must be 0
```

Use `mcp__lean-lsp__lean_goal` at the line *after* each `rw [helper ...]` to confirm the post-rewrite goal matches the previous post-`repeat` goal — the rest of each proof must continue unchanged.

End with a top-level `lake build` to catch downstream breakage from any helper that escaped `private`.
