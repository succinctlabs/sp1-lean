# Elaboration-budget findings — the measured record of the 2026-07 ceiling campaign

What this file is: the durable evidence behind the `/cleanup-all` marathon's **853 → 317** heartbeat-ceiling
ratchet. Every removal in that campaign was **measured**, not inferred; this file records the protocol, the
predictor that made it cheap, the cause classes and their fixes, and — most importantly for a future
maintainer — **which surviving ceilings are real, and what their measured floors are**.

The house rules that governed the campaign are in [`cleanup-profile.md`](cleanup-profile.md) §8; the general
theory is Clean's own `doc/performance-problems.md` (the whnf-into-expensive-values doctrine). This file is
the *data*. Where the two disagree, the profile is the rule and this file is the reason.

---

## 1. Headline

| | before | after | delta |
|---|---:|---:|---:|
| All ceiling sites (`scripts/check_heartbeats.sh` baseline) | 853 | **317** | −536 (−63%) |
| — of which auto-generated `Extracted/` (out of scope) | 215 | 215 | 0 |
| **Hand-written ceilings** | **638** | **102** | **−536 (−84%)** |

The second row is the number that matters and it is easy to miss: **two thirds of the surviving 317 sites are
in `SP1Clean/Extracted/`**, which is auto-generated and whose only lever is `update_extracted.py`. On the
hand-written surface the campaign removed 84% of all ceilings.

Per pillar, hand-written:

| pillar | before | after |
|---|---:|---:|
| `Faithful/` | 305 | 38 |
| `Proofs/` | 232 | 53 |
| `Native/` | 54 | 8 |
| `Soundness/` | 43 | 1 |
| `Model/` | 3 | 2 |
| `Math/` | 1 | 0 |

Per wave (from `scripts/heartbeats_baseline.txt` history; `git log --grep '^Wave:'` reconstructs all 108
commits with machine-parseable trailers):

| wave | ceilings | note |
|---|---|---|
| W1 | 853 → 799 | shallow layers; the two shift-core duplication fixes |
| W2 | 799 → 738 | the `Proofs/Operations` and `Faithful/ChipOracle` copied-default families |
| W3 | 738 → 654 | `Proofs/Sail/Advance.lean` alone was −35 |
| W4 | 654 → 644 | the first 0-for-N batches; mostly right-sizing, not removal |
| W5 | 644 → 485 | the `Faithful/` anchor sweep — the campaign's largest yield |
| W6 | 485 → 370 | the heavy `Faithful/` families incl. the 44-site `DivRemChip/Exact.lean` |
| W7 | 370 → 327 | the `Typed*` grounding family and `Proofs/Chips/*/Contracts.lean` |
| W8 | 327 → 317 | the `Soundness/Grounding` band |
| W9 | 317 → 317 | `SP1CleanTest` — its 16 ceilings are all in auto-generated `*TraceVectors.lean` |

**Declared-budget ratchet is a separate number from removal count, and both must be reported.** W4/b4 removed
*zero* of its 19 ceilings while cutting their aggregate declared budget 174M → 31.5M (5.5×). A batch that
removes nothing has not necessarily failed.

---

## 2. Why the removals are safe — the protocol as actually practised

Per file, three passes, usually one round-trip after the control:

1. **Control at rung 1.** Set every ceiling in the file to a distinct tiny rung and elaborate. *Every* site
   must produce a real deterministic timeout. Without this, a "pass" at a low rung may be a cached LSP result
   rather than a genuine re-elaboration, and you report a floor that was never tested. This also catches the
   placement bug below.
2. **One measuring pass at distinct labels ≤ 40000** — `40000, 39999, 39998, …`, all at *one* magnitude. The
   rung is only a *label* here: the timeout message embeds the rung it hit, so distinct labels separate
   ownership even when every error is reported at the same shared `variable` line. Spreading labels across
   decades conflates "which site failed" with "what its floor is" and answers a question you did not ask.
   `Advance.lean` settled **34 sites in a single pass** this way; `Faithful/ChipOracle.lean` settled 11 sites
   in 6 passes (0.55 passes/site) against ~3.5 passes/site for a serial search. The best rate recorded was
   0.086 passes/site (W5/b2, 58 sites in 5 elaborations).
3. **Decide.**
   - **REMOVE** if the site clears ≤ 40000. Against Lean's plain 200000 default that is **≥ 5× headroom**,
     so there is nothing left to check.
   - **KEEP-AND-LOWER** otherwise, at roughly **4× the measured bracket top**. Not at the lowest passing
     rung: a floor measured through the `lean-lsp` server is measured *without* the pillar libs'
     `moreLeanArgs`, so a 1× margin is measured under weaker options than the build will use.
   - **Never raise.** (Profile §2.9. Removal is unaffected by the LSP caveat — ≥5× either way.)

Two file-level caveats:

- **A file-scoped ceiling must be measured separately from the scoped `… in` ones.** It covers every
  declaration in the file, so it cannot take a distinct label alongside them without making every
  unceilinged declaration fail at one indistinguishable rung. Do the scoped sites first, then remove them
  and give the file-scoped one the whole file at a single rung. `Advance.lean`'s file-scoped 4M turned out to
  be owned by exactly one tactic call.
- **Placement:** a scoped directive must precede the docstring, not sit between it and the declaration. Put
  after a `/-- … -/` it is a parse error — and the real damage is that a ladder pass then *silently skips
  that site's rung* with no timeout appearing, reporting a clean result for a site it never tested.

---

## 3. The predictor

**What binds is not *touching* an unfolded generated list — it is letting that list reach a
`congr` / `isDefEq` / unification step.**

This is Clean's whnf-into-expensive-values doctrine, measured. Sites that rewrite a generated Rust
`asserts` / `interactions` / `.operations` list with targeted `simp only` over `rfl`-projection lemmas,
never unifying against it, clear ≤ 40000 with the list right there in the goal.

Evidence, in the order it was established:

- **Exact at n = 56** (W6/b1: `Faithful/{Branch,ShiftRight,ShiftLeft}Chip.lean`). Every one of the 51
  removals is a folded-template anchor; every one of the 5 survivors demonstrably holds an unfolded native
  `main` operation tower, a raw generated `asserts` list, or an unfolded `ShiftRightCore.main` in a goal.
- **Prospective at n = 12** (W7/b2, `Proofs/Chips/*/Contracts.lean`). All 12 sites were classified correctly
  *before* measuring. The sole survivor closes seven `.shallowConstraints` goals with one
  `all_goals simp only [MulChip.main, …, circuit_norm]` — the only site letting an unfolded `main` operations
  list reach a unification step.
- **The refinement, at n = 44** (W6/b3, `Faithful/DivRemChip/Exact.lean`). *All 44* declarations mention an
  unfolded `.operations`/`.asserts`/`.interactions` list, so read literally the predictor called ~44 binding
  against an actual 5. Contact is necessary, not sufficient; screen on the **unification step**.

### It discriminates between proofs that look identical

- `LtChip` and `BitwiseChip` run the **visually identical** `controlExpressions_subset_constraints` as
  `MulChip`'s binding site and clear 40000 — because each branch narrows with `right; …; left` *first* and
  only then applies a targeted `simpa … using equalityConstraint_mem`. **Tactic-text similarity is not
  evidence of similar cost; the narrowing order is.**
- `divRem{Header,Comparison,Arithmetic,Result}Blocks_roundtrip` (`Faithful/DivRemChip.lean`) share identical
  tactic text. `divRemHeaderBlocks_roundtrip` cleared 40000 and was removed; the other three bind at `whnf`
  and were kept at 400000/800000/400000. The reason is arithmetic, not style: **the header chunk's offsets
  all land in the first `Vector` append arm, so its `rw` ladder terminates early.**
- Two **adjacent** lemmas over the same 19-cell structure split >25×: `BitwiseChip`'s
  `toElements_bitwiseChipOperationOfLocals` floors in (800000, 1000000]; the `getElem_toElements_…` lemma
  immediately below it clears 39989. The cost is *producing* the `toElements` normal form, not consuming it.

### Weaker predictors, in descending order

- **Declared magnitude predicts nothing, in either direction.** Across ~110 measured sites it never
  correlated with the true floor: 16M families flooring ≤40k, 8M at ≤20k, 1M at ≤1500 — and
  `ltChip_interactions_faithful`, declared at exactly the 200000 default, *fails at 100000*. Do not triage by
  declared value.
- **Role beats family, but its brackets do not transfer between chip families.** Across the six `Faithful/`
  ALU anchors, `*_memory_*`/`*_byte_*`/`*_constraints_faithful` all floor ≤40000, `*cols_state_*`/
  `*cols_program_*` in (40k, 60k], and `*_interactions_faithful` in (60k, 100k] — but on `Faithful/BranchChip`
  *every* state/program/memory/byte/interactions anchor cleared 40000. **Ask the fold question first; use role
  only to break ties within one family.**
- **Counter-intuitively, State/Program anchors cost more than Byte anchors.** Byte has 12 emits and clears
  40000; Program has 1 and does not. The cost is channel-distinctness filtering, not emit count.
- **Layer beats chip, decisively.** Three batches over the *same nine* Load/Store chips: at
  `Proofs/Chips/*/Formal.lean`, **0 of 19** removable (floors (150k, 400k]); at `Proofs/Chips/*/Bridge.lean`,
  **21 of 21**; at the `Faithful/` anchor layer, **52 of 52**. Same chips, three orders of magnitude apart.
- **Count the witnessed sub-gadgets `main` composes** — chip-side only. `Proofs/Chips/*/Formal.lean` is
  *not* a uniform family: the ALU chips went 8 of 11 removed while the jump/U-type chips went 0 for 4, because
  `JalrChip` composes two witnessed `AddOperation` gadgets plus `ITypeReader` plus `RegisterWrite`. This
  discriminator does **not** transfer to the `Faithful/` anchor for the same chip: `Faithful/JalrChip`'s six
  anchors all floor ≤40000, a >50× gap.
- **The sibling screen is a reliable *ranker*, not a keep/remove oracle**, and it predicts both answers.
  `MulOperation/RawSpec.full_product` vs the unceilinged `low_half` does 16 columns rather than 8 → predicted
  *real*, confirmed; `high_half_eq` vs `product_reassembly`, which does strictly more work → predicted
  *vestigial*, confirmed. It ordered all eleven `ChipOracle` sites by floor with zero measurements — but the
  group it flagged "plausibly genuine" was still ~40× over-provisioned.
- **Read the phase name in the timeout, but read it at the *binding* rung.** `whnf` = an elaboration-bound
  tower, foldable · `isDefEq` = an abstraction/unification blowup · `«abstract nested proofs»` =
  post-elaboration, neither foldable nor term-intrinsic · `«LCNF compiler»` = genuinely codegen-bound.
  **The phase moves with the rung** (measured at n=56 and again at n=44): the control-rung distribution
  (`elaborator` 21 · `isDefEq` 14 · `«synthesize pending MVars»` 14 · `whnf` 7) bore almost no resemblance to
  the binding-rung distribution (`whnf` 5/5 on DivRem `Exact`). Treat it as a cost *class*, not a fingerprint.

---

## 4. Cause classes, with worked fixes and measured before/after

**1. Search duplication in a `first | … | …` ladder — the campaign's largest single win.**
`ShiftRightChip/Dispatch.lean`: **1591 → 861 lines (−730)**, all 12 ceilings removed. Each lemma did `rcases`
into 16 goals `<;> first | exact close 0 65536 … | … | 15 …`. `first` restarts the ladder for every goal and
the matching alternative sits at `bitreverse4(goal index)`, so ~8 alternatives per goal were elaborated all
the way through their `rw […]; push_cast; ring1` side conditions and discarded — ≈128 wasted `ring1` per
lemma, ≈1500 across the file. That was the entire ceiling. Fix: `rcases … with rfl | rfl` (substituting makes
the side conditions uniform), hoist the fixed arguments into one `have key`, replace `first` with **ordered
bullets**.
- *First check whether the ladder is just `assumption`.* If every alternative is a bare context reference, the
  whole thing collapses to one token — cheaper than ordered bullets, which cost ~+14 lines per site. Measured
  on `MulOperation/Formal.lean`.
- *Sorting the ladder does not help.* `ShiftRightChip/Core.lean`'s `cb_aux` ladder was already in goal order
  and still paid the full 120 wasted alternatives. Do not try the cheap fix.

**1b. Permutative-`simp` term ordering over a dependent cast.** A permutative `@[simp]` lemma
(`Std.ExtDHashMap.insert_insert_comm`) makes `simp` pick a direction with `Lean.Meta.acLt`, whose cost scales
with the compared arguments. When one is a `▸` cast whose proof is a 31-arm `match`, that comparison dominates
— presenting as an opaque `timeout at «Lean.Meta.acLt»` with **no hint of which simp lemma is responsible**.
Fix inside the body: `unfold`, `generalize` the cast away, re-run. This was `Model/SailWrap.lean`'s entire
file-scoped 10M ceiling and, in the same shape, `Advance.lean`'s 4M (owner: `get_reg?_writeBack`) — which
cleared **all 35** of that file's sites.

**1d. `simp_all` under `circuit_proof_start`.** One `simp_all` closing a small goal against the *entire*
post-`circuit_proof_start` context can own a file's budget. `DivRemOperation/Compare.soundness` spent 4M on a
four-case numeral goal; narrowing to `rcases … <;> rw [hrcmGate, hz, hv] <;> simp` moved the floor from
(40000, 100000] to below 40000, i.e. keep → remove.
- *High-yield instance:* in the load `Bridge.lean` files, `advance_of_load_width{1,2,4}`'s `hpin` obligation
  was discharged inline by `simp_all` against the whole post-`obtain` `advance` context — while being a pure
  `loadOpcode` fact about loose `isU` that never needed the context. Extracting it as a `private lemma` moved
  all three sites **FAIL@400000 → PASS@≤40000**, over 100×. `Model/Semantics/Decode.lean` already owned the
  exact `storeOpcode_pin_one` analogue; only `loadOpcode` lacked one.
- *Known false negative for the sibling screen:* the byte-identical `simp_all` block in that file's
  `completeness` cleared the same rung, because that proof destructures less context. When the suspect tactic
  is context-sensitive, measure rather than screen.

**1e. A `set` over a large term is an `isDefEq` abstraction across the whole goal.**
`BitwiseChip.completeness` failed at 1M *at the `set` line*; deleting it took the same proof FAIL@1M →
PASS@1M — and the `with hR` binding was dead anyway. A bare `set` for readability on a large term is a perf
hazard.

**1c. LCNF-compiler-bound, not elaboration-bound.** `Native/Operations/MulOperation/Defs.lean`'s `def main`
elaborates fine at 40000; the failure is `timeout at «LCNF compiler»` over sixteen schoolbook product
expressions. **None of the fold recipes apply** — they all target elaboration. `noncomputable def` is
*rejected*, not deferred: `SP1CleanTest/TraceGenTests` derives traces from `main`'s witness closures, so
dropping the code plausibly breaks `lake test`. Such a site is lowered, not removed, and keeps more headroom
than usual (~6.7×) because code-generation cost is more load-sensitive.

**2. A duplicated `.val`-bridge fact — a raised ceiling as a proxy for missing shared substrate.**
`ShiftLeftChip/Core.lean` carried 16 ceilings; its SLLW half was re-deriving `mul_v_val` / `hi_lo_val` /
`mul_v_add_val` by hand while the SLL half *in the same file* already called them, and two residual `nlinarith`
calls re-proved `< 65536` limb bounds that `Math/ShiftBounds.lo_hi_lt` already proves once over loose
variables. Fixing the duplication dropped 26 `nlinarith` to 3 and made **all 16 ceilings removable**.

**3. Eval-map factoring, then partial application.** `Proofs/Operations/DivRemOperation/Core.lean` repeated
the same two-line `rw [← h, Vector.getElem_map]` bridge **176 times**; folding to one-liners took 352 → 176
lines, and replacing each per-index family with one **quantified `simp only` rule** took 176 → **25**. Total
−466 (−40% of the file); elaboration 19.0s → 15.8s; 2 of its 4 ceilings removed.
- *Landmine:* the quantified rule only fires when the helper's bound **is** the vector's own length.
  `StoreWordChip`'s `eoap : ∀ i (hi : i < 2), …` over a length-4 `Word` makes the `getElem` side condition a
  derived `omega` term rather than `hi` itself, so simp cannot key the pattern. It **fails silently** and
  surfaces four lines later as `Application type mismatch`.

---

## 5. The sites that were KEPT — measured floors

**This is the table to read before touching any surviving ceiling.** Everything here was laddered; the floor
is the highest rung that *failed*, so the bracket is (fail, pass]. Sizing convention: ~4–5× the bracket top.

Most `Proofs/`, `Native/` and `Model/` keeps carry their one-line ladder **in the source, directly above the
directive** — that is the primary record and it is tracked. `Faithful/**` is conservative-only, so its keeps
carry no in-source note: **for the `Faithful/` rows this file is the only record.**

### `Faithful/` (38 survivors) — the anchor layer

| site | declared before | floor bracket | kept at |
|---|---:|---|---:|
| `DivRemChip/Exact.lean:1128` `divRemRustAssertionsDecompose` | 64M | **(8M, 16M]** | 64M (unchanged, ~4×) |
| `DivRemChip/Exact.lean` `divRemWholeAssertionsExact` | 32M | (100k, 200k] | 800000 |
| `DivRemChip/Exact.lean` `divRemCoreForallDecompose` / `divRemLowerBackward` / `divRemUpperBackward` | 8M each | (40k, 100k] | 400000 each |
| `BranchChip.lean:1061` `branchTailMeaningFaithful` | 4M | (200k, 400k] | 1600000 |
| `BranchChip.lean:536/747` `branchNativeAssertionsDecompose` / `branchColumns_asserts_decompose` | 2M each | (100k, 200k] | 800000 each |
| `ShiftRightChip.lean:848` / `ShiftLeftChip.lean:722` `shift{Right,Left}CoreAssertions` | 4M each | (40k, 100k] | 400000 each |
| `DivRemChip.lean` three `divRem*Blocks_roundtrip` siblings | 2M each | > 40000, `whnf` | 400k/800k/400k |
| `DivRemChip.lean:1122` `divRemChip_lookups_empty` | 8M | > 40000 | 800000 |
| `AluX0.lean:211` `aluX0Chip_constraints_faithful` | 4M | (250k, 500k] | 2000000 |
| `AluX0.lean:331` + 5 ALU `*Chip_interactions_faithful` | 1M–4M | (60k, 100k] | 400000 |
| 8 ALU `*cols_state_*` / `*cols_program_*` (Add/Addw/Sub/Subw) | 1M–4M | (40k, 60k] | 250000 |
| `BitwiseChip.lean:126` `toElements_bitwiseChipOperationOfLocals` | 4M | (800k, 1M] | 2000000 |
| `BitwiseChip.lean:408/815` | 2M / 8M | (150k, 200k] / (100k, 200k] | 400000 each |
| `LtOperationUnsigned.lean:30` `ltUnsigned_constraints_faithful` | 2M | (50k, 60k] | 400000 |
| `MulChip.lean:1716` `mulChip_constraints_faithful` | — | > 40000 | 600000 |
| `MulChip.lean:3203` `mulChip_interactions_faithful` | — | > 40000 | 1000000 |
| ⚠ `LtChip.lean:1477` `ltChip_interactions_faithful` | 200000 | **(100k, 200k]** | 200000 (no headroom) |
| ⚠ `MulChip.lean:1092` `mulOperation_assertions_forward` | 100000 | **(40k, 60k]** | 100000 (~1.7×) |
| ⚠ `MulChip.lean:1518` `mulOperation_assertions_backward` | 100000 | **(40k, 80k]** | 100000 (~1.25×) |

### `Proofs/` (53 survivors) — highlights

| site | declared before | floor bracket | kept at |
|---|---:|---|---:|
| ⚠ `StoreByteChip/Formal.lean:252` `circuit` | 2M | **(1M, 2M]** | 2000000 (<2×) |
| `JalrChip/Formal.lean:63,193` `soundness`/`completeness` | 8M each | **(2M, 4M]** | 8000000 (~2×, unchanged) |
| nine Load/Store `Formal.lean` `soundness` | 4M–16M | (300k, 400k] | 2000000 |
| nine Load/Store `Formal.lean` `completeness` | 2M–16M | (150k, 300k] | 1500000 |
| `UTypeChip/Formal.lean:66,139` | 2M each | (40k, 100k] | 500000 each |
| `MulChip/Formal.lean:77,182` | 4M / 128M | (60k, 80k] | 400000 each |
| `MulChip/Formal.lean:378` `circuit` | 8M | (150k, 200k] | 800000 |
| `MulChip/Contracts.lean:35` | 4M | (40k, 100k] | 400000 |
| `LtChip/Formal.lean:157,208` | 800k / 32M | (60k, 100k] / (45k, 60k] | 500000 / 300000 |
| `BitwiseChip/Formal.lean:217` | 32M | (700k, 1M] | 5000000 |
| `DivRemChip/Soundness.lean:292,596,678` | 8M/4M/8M | (50k,100k]/(20k,50k]/(50k,100k] | 500k/400k/500k |
| `DivRemChip/Evidence.lean:110` `compareAssumptionsOfCore` | 16M | (60k, 100k] | 400000 |
| `DivRemChip/Evidence/Signed{32,64}.lean` | 16M each | (400k, 1M] | 4000000 each |
| `DivRemChip/Evidence/Unsigned{32,64}.lean` | 16M each | (100k, 400k] / (40k, 400k] | 2000000 each |
| `ShiftRightChip/Core.lean:1591` `srlw_within_byte_shift` | file-scoped | (250k, 320k] | 1600000 |
| `Shift{Left,Right}Chip/Soundness/*.lean` (6 files) | 4M–16M | (100k,200k] / (200k,400k] | 800000 / 1600000 |
| `Proofs/Operations/MulOperation/Formal.lean:100,607` | 40M each | (100k, 150k] / (100k, 200k] | 1000000 each |
| `Proofs/Operations/DivRemOperation/Core.lean:301,471` | 16M each | (80k,100k] / (60k,80k] | 500000 / 400000 |
| `DivRemChip/Completeness/OwnComplete.lean:126` | 16M | (100k, 200k] | 800000 |

### `Native/` (8), `Model/` (2), `Soundness/` (1)

| site | declared before | floor bracket | kept at |
|---|---:|---|---:|
| `MulOperation/RawSpec.lean:114` `full_product` | 16M | **(1M, 1.2M]** — the highest floor measured anywhere | 6000000 |
| `MulOperation/RawSpec.lean:904` `mulSemantics_of_raw` | 1.6M | (60k, 100k] | 500000 |
| `MulOperation/Defs.lean:20` `main` (**`«LCNF compiler»`-bound**) | 8M | (40k, 60k] | 400000 |
| `LtOperationUnsigned/RawSpec.lean:34` `at_most_one` | 1M | (400k, 500k] | 1000000 (unchanged — correctly sized) |
| `DivRemOperation/OwnAsserts.lean:20` `ownAsserts` | 8M | (40k, 50k] | 500000 |
| `SubOperation/RawSpec.lean:38,91` | 16M each | (60k, 80k] / (40k, 60k] | 400000 each |
| `AddrAddOperation/RawSpec.lean:134` | 16M | (45k, 60k] | 400000 |
| `Model/SailWrap.lean:316` | file-scoped 10M | (50k, 100k] | 400000 |
| `Model/SailDecode.lean:49` | file-scoped 8M | (40k, 50k] | 400000 |
| `Soundness/RowSoundness.lean:61` `supportedChip_usesSupportedBusChannels` | — | (100k, 200k] | 800000 |

### ⚠ The five under-provisioned sites

Headroom < 2× against the declared value. **These are the declarations most likely to break on the next
toolchain or mathlib pin**, and none of them can be fixed by the campaign's rules (removal needs ≤40000;
raising is prohibited).

| site | declared | floor | headroom |
|---|---:|---|---|
| `Faithful/MulChip.lean:1518` `mulOperation_assertions_backward` | **100000** (below the default) | (40k, 80k] | ~1.25× |
| `Faithful/MulChip.lean:1092` `mulOperation_assertions_forward` | **100000** (below the default) | (40k, 60k] | ~1.7× |
| `Faithful/LtChip.lean:1477` `ltChip_interactions_faithful` | 200000 (= the default) | (100k, 200k] | none |
| `Proofs/Chips/StoreByteChip/Formal.lean:252` `circuit` | 2M | (1M, 2M] | <2× |
| `Proofs/Chips/JalrChip/Formal.lean:63,193` | 8M | (2M, 4M] | ~2× |

The two `MulChip` sites are a distinct shape worth understanding: **a ceiling declared *below* the 200000
default is a deliberate tightening, not a budget.** It buys the proof nothing and functions as a signal. Same
for `ltChip_interactions_faithful` at exactly the default. If a future pin breaks one of these, the correct
response is a *fold* (cause class 1d/1e), or an audited, deliberate raise — not a reflex bump.

`divRemRustAssertionsDecompose` (declared 64M, fails at 8M) is a sixth site at exactly 4×, i.e. correctly
sized all along. It is also the repo's single most expensive declaration — worth roughly half of
`Faithful/DivRemChip/Exact.lean`'s ~260s — so folding it would move the whole build's critical path. See
[`cleanup-deferred.md`](cleanup-deferred.md) for why it was not taken.

---

## 6. Measurement traps

These cost the campaign real time. Each has been observed more than once.

**Masking — the single most expensive measurement error, and the mask itself MOVES.** If a producer (`def`)
times out, every dependent cascades with `(kernel) unknown constant '_private.…'` instead of its own timeout,
so the dependents' true floors are invisible and they read as "binding" when they may be hundreds of times
over. Two properties make it hard to spot:
- the cascade lands on **unceilinged** consumers too, where it reads as independent breakage;
- **which producer is named changes between rungs.** The same masked line reported
  `unknown constant …divRemComparisonBlocks_roundtrip` at the 40000 rung and
  `…divRemArithmeticBlocks_roundtrip` at 100k, because the producers' pass/fail set had changed.

It struck in every large batch: 6 of 43 removals hidden in one, twice in another, and across W6 alone a naive
single-pass ladder would have under-removed by **five** — including a 16M and a 32M ceiling sitting ~400× and
~800× over. **A `(kernel) unknown constant` is never a result; it is a re-measure instruction.** Pin the
suspected producer high, re-run, and confirm the dependency by grepping for citations rather than inferring
it from the error. Masking is also **rung-dependent**: `MulOperation/RawSpec.full_product` masks at 1M (whnf
at the signature) and does *not* mask at 200k/400k (fails inside its tactic block, gets `sorry`'d, dependents
stay visible). Check for masking at the rung you actually intend to use.

**The phase name moves with the rung** (§3). Read it at the binding rung — the lowest that fails — not at
rung 1, and never treat a rung-1 phase as the site's identity.

**`lake env lean <file>` does not rebuild edited dependencies.** It only sets the environment. After one
batch edited `TypedMemoryBalance.lean`, its source was 4 hours newer than its `.olean`, and a `lake env lean`
run on the *dependent* `MemoryFrontier.lean` resolved happily against the stale one and reported green. The
instrument is *stronger than the LSP on flags and weaker on freshness*. Work deepest-first, `lake build
<Dep.Module>` after editing a dependency, and treat the gate's full `lake build SP1Clean` as the only joint
confirmation. (`lake env lean` also exits 0 on a Lean stack overflow — it is sound only as a *falsifier*.)

**A ceiling has declaration granularity only.** The heartbeat counter is cumulative from the declaration's
start, so wrapping one tactic line in a scoped directive does **not** isolate it — the wrapped line still
fails with the *enclosing declaration's* rung. "Pin the one expensive tactic high and ladder the rest" is not
a usable strategy. To attribute cost within a declaration, substitute `sorry` for the other branches — and
restore it before any other tool call, since a `sorry` on disk can trip the harness's own guards.

**Attribution ≠ magnitude.** A `timeout at whnf` is reported at **column 1 of a signature**, which is not
necessarily the declaration you think failed: `ShiftRightChip/Core.lean`'s binding site was recorded once as
`sra_close_su16_3_case` and is actually `srlw_within_byte_shift` — pinning that single lemma leaves ~42 of the
file's 43 declarations clean at the plain default. And a failure *position* tells you which declaration owns
the budget and **nothing reliable about how large it is**:
`Faithful/LtOperationUnsigned.ltUnsigned_constraints_faithful` failed at an in-body `itauto` and floors at
~60000, the highest floor in `Faithful/`, against a heuristic that predicted hundreds. Also: an **in-body**
failure position is not stable across runs — three identical invocations at rung 60000 named three different
owners while the *signature* positions stayed fixed.

**Re-ladder after a heavy golf, and after a cause fix.** `OwnComplete.lean` went 817 → 495 lines (−39%) and
its bracket was **identical before and after** (FAIL 40000 · FAIL 100000 · PASS 200000, both times) — the 322
removed lines were all bullet tactics while the real cost sat in a 121-hole `refine` over an unfolded
`ownAsserts`. "The floor did not move" is a finding, not a null result. Conversely the *owner* moves after a
cause fix: `SailWrap.lean`'s ceiling was owned by two lemmas before its `acLt` fix and a completely different
third lemma after.

**`#count_heartbeats` lies** — measure from the build log.

**Prefix scratchpad helper scripts with your batch id.** A shared scratchpad let one worker's `rung.py` be
silently overwritten by a sibling's same-named script using a different sentinel convention, so its delete
pass wrote a `maxHeartbeats 0` directive — a *valid but wrong* Lean option — instead of removing the lines.
No build failed and no error was raised; only the worker's own post-pass grep caught it.

---

## 7. Negative results — what did NOT work

- **A uniform per-file ceiling count across a family is usually a copied default, not a measurement.**
  Confirmed four times: the `RawSpec` family (all 16M, floors ≤40k), `Proofs/Operations/*/Formal.lean` (32 of
  32 removed), `Faithful/ChipOracle.lean` (11 of 11, floors 500–30000 against a uniform declared 1M), and
  `Proofs/Chips/*/Contracts.lean` (11 of 12). Treat "every file in this family has exactly one" as a *prior
  for removal* — then measure anyway, since the twelfth was real.
- **Per-rule golf yield does not transfer between files in the same layer.** One batch was briefed that a
  tactic-body → term conversion was its biggest lever, on the strength of −131 lines from it on a 1087-line
  sibling. It scanned all 351 declarations of the target and found **zero** hits; every proof there leads with
  `rw`/`simp only`/`obtain`, so the shape does not occur. Its −677 came from macros (−352) and line joins
  (−293), the rules ranked below it. Hand a batch the whole ordered recipe, not a prediction.
- **Role brackets do not transfer between chip families** (§3) — the ALU `Faithful/` brackets are an ALU fact.
- **`simp` → `simp only` on the §5 KEEP-set**: zero speedup, tested twice. Do not sweep those files.
- **Sorting a `first` ladder into goal order**: no effect; `first` restarts from the top regardless.
- **`noncomputable def` for an LCNF-bound site**: rejected, breaks `lake test` (§4, cause 1c).
- **Omitting `ElaboratedCircuit` Prop-fields is *per-file*, not family-wide.** Letting Clean's default tactic
  fire is usually right, but the default **whnf's the entire chip `main`** while a hand-written
  `simp only [circuit_norm, main, …]` never does. Measured across 19 `Native/Chips` files: chips whose `main`
  composes `AddressOperation` **+ `U16MSBOperation`** regressed **+63% to +132%**, or timed out at `whnf`
  outright (`LoadHalf`/`LoadWord`/`LoadByte`/`Lt`/`Mul`); `AddressOperation` alone was −3%. The driver is the
  sign-extension block, not "is it a load chip". Run the omission pass **before** the ceiling pass — a
  defaulted `output_eq` can manufacture a fresh ceiling.
- **Dropping `by exact` on a `def`'s Prop-valued field can be a downstream catastrophe.** Correct by proof
  irrelevance, −1 line, clean in its own file — and it took `Faithful/DivRemChip/Exact.lean` from **260s to
  >1230s and still climbing**, pinned in `isDefEqDelta`/`whnfImp`/`unfoldDefinition`. A tactic block is
  auto-abstracted into an opaque auxiliary proof constant; the term-mode form is inlined and delta-unfolds
  straight into `DivRemChip.circuit`. On a field any heavy module unfolds, `by exact` is **deliberate
  opacity**: A/B-time the *downstream* consumers.
  > And note *why it hung instead of erroring*: the blown-up work landed inside the one survivor still
  > carrying a 64M budget, enough to absorb roughly an hour of extra `whnf`. **A high surviving ceiling
  > silently converts a downstream regression from a loud error into a slow build.** That is the argument for
  > this ratchet beyond tidiness — every ceiling lowered makes the next regression louder.

---

## 8. Where the rest of the evidence lives

- **In the source.** Every kept `Proofs/`/`Native/`/`Model/` ceiling carries a one-line ladder immediately
  above it ("the former 16M ceiling was ~160× over; measured floor bracket (60000, 100000]"). Keep them to
  one line; multi-line transcripts belong here, not in a `.lean` file.
- **In git.** `git log --grep '^Wave:'` reconstructs the whole campaign — 108 commits carrying
  `Wave:`/`Group:`/`Batch:`/`Tier:`/`Gate:`/`Divergences:` trailers, with the per-batch ladders in the bodies.
- **Owner decisions and un-taken work:** [`cleanup-deferred.md`](cleanup-deferred.md).
- **The rules:** [`cleanup-profile.md`](cleanup-profile.md) §8.

> **When recording a new ladder anywhere in this repo, never write the literal option name.**
> `scripts/check_heartbeats.sh` counts sites with a raw `grep -rc` over `SP1Clean/` and `SP1CleanTest/` — it
> does not parse Lean, so a comment mentioning the option scores as a live ceiling and silently corrupts the
> ratchet. Phrase it as "the former 8M ceiling was ~170× over". Two workers hit this; one caught it, one did
> not.
