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

| | start | after the 2026-07 campaign | final |
|---|---:|---:|---:|
| All `maxHeartbeats` sites | 853 | 317 | **3** |
| **Hand-written `maxHeartbeats`** | **638** | **102** | **0** |
| Hand-written `maxRecDepth` | 44 | 44 | **3** |
| Generated `maxRecDepth` | 66 | 66 | **6** |

**Hand-written Lean in this repo now carries zero elaboration-budget overrides**, matching upstream Clean,
which has none in 44,603 lines. All twelve surviving sites are on *generated* definitions or measured
structural cases, and every one is named in `scripts/option_escapes_allowlist.txt` with its floor bracket
and mechanism — enforced by `scripts/check_option_escapes.sh`, which fails on anything unlisted rather than
merely counting. The 2026-07 campaign removed 84% of hand-written ceilings by *measuring* each one; the P4
follow-up (`git log --grep '^Wave: heartbeat-P4'`) removed the rest by *diagnosing and fixing the causes* —
a different and much more productive exercise. Sections 10, 11 and 12 are that follow-up's findings.

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

> 🔴 **BOTH §5 AND §5A ARE NOW HISTORICAL.** They document the 101-site state as of 2026-08-01. The
> follow-up campaign (`git log --grep '^Wave: heartbeat-P4'`) took that to **5**. Read §5/§5A for the
> *method* and for the archaeology of a site's earlier brackets; read the table immediately below for
> what is actually in the tree. Every site removed since is documented in its removing commit, and the
> per-site mechanism write-ups live in §10 and §11.

### 5-current. The surviving ceilings

**There are no hand-written ones left.** All twelve survivors are on generated definitions or are
measured structural cases, and the authoritative list — with a floor bracket and a mechanism for each —
is `scripts/option_escapes_allowlist.txt`, enforced by `scripts/check_option_escapes.sh`. Read that file
rather than a table here, so the guard and the documentation cannot drift apart.

Summary of the twelve: three `maxHeartbeats` (a generated chip-oracle definition that fails in
**codegen** not elaboration; `Global`'s Poseidon closure; the largest conformance battery) and nine
`maxRecDepth` (four on `Global`'s `assertsPart*`, three structural hand-written cases, two conformance
batteries).

**The one confirmed-irreducible verdict.** `Global`'s ceiling is the only claim of irreducibility in this
tree that survived measurement: `assertsPart2` contains a *single* list entry whose transitive
`let`-closure is **1239 bindings**, and the Rust emitter's chunker bottoms out there — chunking at one
entry per part still leaves 1239. Four other "irreducible" verdicts this campaign inherited turned out to
be untested; this one was not.

> ⚠ **§5 is the campaign-era record and it has drifted from the tree.** For a per-site,
> reconciled, line-accurate answer use **[§5A](#5a-the-authoritative-floor-table--all-101-hand-written-sites)**,
> which supersedes this section wherever they disagree; §5A's "reconciliation" subsection lists every
> divergence found. Known stale here: the `divRemRustAssertionsDecompose` row (that ceiling was
> **removed**), the two `shift*CoreAssertions` rows (re-measured and lowered to 240000), the "nine
> Load/Store `soundness`" row (only five of the nine match it), the two
> `Proofs/Operations/MulOperation/Formal.lean` brackets (swapped), and ~11 rows citing pre-drift line
> numbers. Keep §5 for its *narrative* — which families were laddered together, and why.

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

## 5A. The authoritative floor table — all 101 hand-written sites

Built 2026-08-01 by reconciling three sources per site: §5 above, the one-line ladder comments in the
source, and the `Wave:`-trailered commit bodies (`git log --grep '^Wave:'`). **Where they disagree this
table is the answer and §5 is not.** Read the [reconciliation](#reconciliation--every-divergence-found)
subsection before trusting any §5 row.

Scope: the 101 elaboration-budget ceilings on **hand-written** code — everything under `SP1Clean/` and
`SP1CleanTest/` *except* the auto-generated `SP1Clean/Extracted/**` (215 sites, uniform 8M) and
`SP1CleanTest/**/Vectors/**` + `*TraceVectors.lean` (16 sites, uniform 4M). Paths below drop the
`SP1Clean/` prefix. Line numbers are as of commit `cbfc8d43`.

> **Status — Phase 1 tranche A (2026-08-01): 44 of these 101 sites are deleted, 57 remain.**
> Tranche A removed every site whose floor bracket tops out at or below Lean's plain 200000 default
> (the 60-site bucket below) *minus* the three excluded shapes in
> [Deletion hazards](#deletion-hazards-inside-the--200000-bucket): the 13 zero-margin sites at exactly
> 200000, the two sub-default 100000 stamps in `Faithful/MulChip.lean`, and the file-scoped
> `Model/SailDecode.lean` stamp. The full `lake build SP1Clean` gate passed with **zero sites
> restored** — every recorded floor in the deleted set held under the real pillar `moreLeanArgs`
> build, which is the strongest confirmation this table's `≤ 200000` bracket tops have. Baseline
> ratcheted 316 → 272. The 57 survivors are the 35 with floor top > 200000, the 6 UNKNOWN, and the 16
> exclusions. **The rows below are retained as the measurement record, but their line numbers are
> pre-deletion** and no longer resolve in the 27 files that lost a site; re-anchor by declaration
> name. Ladder comments for the deleted sites were removed with them.

> **Status — Phase 1 tranche B (2026-08-01): a further 20 deleted, 37 hand-written sites remain.**
> Tranche B resolved the 22 sites tranche A held back, all re-measured under the real pillar
> `moreLeanArgs` (not the LSP). Results, and the rows above they correct:
> - **All 13 zero-margin sites pass at the plain default** and were deleted. The
>   [hazard-1](#deletion-hazards-inside-the--200000-bucket) caution was sound to act on but the
>   bracket tops all held; there is now no recorded case of a `≤ 200000` bracket top failing.
> - **The 6 UNKNOWN rows are measured.** Five floor at or below the default and were deleted:
>   `divRemComparisonBlocks_roundtrip` **(40000, 60000]**, `divRemResultBlocks_roundtrip`
>   **(60000, 100000]**, `divRemArithmeticBlocks_roundtrip` **(100000, 200000]**,
>   `divRemChip_lookups_empty` **(100000, 200000]**, `mulChip_constraints_faithful` **≤ 200000**.
>   Their declared 400000–800000 values were 4–13× over, confirming the "single largest block of
>   unmeasured slack" note in [Plausibility check](#plausibility-check--declared-value-vs-recorded-floor).
>   The sixth, `mulChip_interactions_faithful`, is the **only** site in either tranche that genuinely
>   exceeds the default: **(220000, 250000]**, ratcheted 1000000 → 300000. §5A's backwards-guess of
>   250000 for it was right; the guesses for the other five were all too high.
> - **The two 100000 stamps** in `Faithful/MulChip.lean` were deleted (owner call, per hazard 2).
> - **The file-scoped `Model/SailDecode.lean` stamp was converted to a scoped one**, not deleted.
>   ⚠ Hazard 3 says it "covers all 57 declarations in the file" — **the file has 3**, and only
>   `decode_ADD_example` is budget-bound (the other two are one-line `simp only`s). Its floor
>   (40000, 50000] re-confirmed; kept at 400000 for the reason its in-source note gives.
> - §9's `Nat.pred`/`Nat.casesOn` finding **reproduces on a second member of the family**:
>   `divRemArithmeticBlocks_roundtrip` gives `Nat.casesOn ↦ 138302`, `Nat.rec ↦ 69158`,
>   `Nat.pred ↦ 68368`, `Eq.rec ↦ 22` — `Vector.append`/`Eq.rec` are absent, as §9 found.
>   No fix was taken: with all four floors under the default the sites are simply gone.
> - The mechanism for the one keep is §9.6(a)'s, scaled: `Channel.Guarantees ↦ 2268` /
>   `Channel.name ↦ 433` with `nonempty_prop ↦ 273` / `isEmpty_Prop ↦ 136` and a
>   `sub_self ↦ 330 ❌️` / `forall_const ↦ 273 ❌️` failed-match tail, over Mul's 45-column row eval
>   (`Eq.rec ↦ 6096`, `List.rec ↦ 5102`, `ProvableStruct.componentsToElements ↦ 2395`).
>
> Baseline ratcheted 272 → 252. The 37 survivors are the 35 rows with floor top > 200000, plus
> `mulChip_interactions_faithful` and the rescoped `SailDecode` site.

Column conventions:

- **floor bracket** — `(lo, hi]` = highest rung that *failed*, lowest that *passed*. `≤ n` = a pass at
  `n` with no recorded failing rung below it. `> n` = a fail at `n` with **no recorded passing rung**,
  i.e. the top is unmeasured; those rows count as UNKNOWN for planning.
- **source** — `§5` · `in-source` (the ladder comment above that declaration) · `git <sha>` ·
  `derived` (computed from a ratio or a former value).
- **confidence** — `measured` (a real ladder was run and recorded) · `derived` · `none`.

### `Faithful/` (37 sites)

`Faithful/**` is conservative-only, so most of these carry **no in-source note** — §5 (and the wave
commits) are the only record. The three exceptions are marked.

| file:line | declaration | declared | floor bracket | source | conf |
|---|---|---:|---|---|---|
| `Faithful/AddChip.lean:160` | `addcols_state_interactions_faithful_syntactic` | 250000 | (40000, 60000] | §5 | measured |
| `Faithful/AddChip.lean:207` | `addcols_program_interactions_faithful_syntactic` | 250000 | (40000, 60000] | §5 | measured |
| `Faithful/AddChip.lean:729` | `addChip_interactions_faithful` | 400000 | (60000, 100000] | §5 | measured |
| `Faithful/AddiChip.lean:677` | `addiChip_interactions_faithful` | 400000 | (60000, 100000] | §5 | measured |
| `Faithful/AddwChip.lean:224` | `addwcols_program_interactions_faithful_syntactic` | 250000 | (40000, 60000] | §5 | measured |
| `Faithful/AddwChip.lean:274` | `addwcols_state_interactions_faithful_syntactic` | 250000 | (40000, 60000] | §5 | measured |
| `Faithful/AddwChip.lean:957` | `addwChip_interactions_faithful` | 400000 | (60000, 100000] | §5 | measured |
| `Faithful/AluX0.lean:208` | `aluX0Chip_constraints_faithful` | 2000000 | (250000, 500000] | §5 (cites `:211`) | measured |
| `Faithful/AluX0.lean:328` | `aluX0Chip_interactions_faithful` | 400000 | (60000, 100000] | §5 (cites `:331`) | measured |
| `Faithful/BitwiseChip.lean:126` | `toElements_bitwiseChipOperationOfLocals` | 2000000 | (800000, 1000000] | §5 | measured |
| `Faithful/BitwiseChip.lean:408` | `bitwise_chip_constraints_decompose` | 400000 | (150000, 200000] | §5 | measured |
| `Faithful/BitwiseChip.lean:815` | `bitwiseChip_interactions_faithful` | 400000 | (100000, 200000] | §5 | measured |
| `Faithful/BranchChip.lean:536` | `branchNativeAssertionsDecompose` | 800000 | (100000, 200000] | §5 | measured |
| `Faithful/BranchChip.lean:747` | `branchColumns_asserts_decompose` | 800000 | (100000, 200000] | §5 | measured |
| `Faithful/BranchChip.lean:1061` | `branchTailMeaningFaithful` | 1600000 | (200000, 400000] | §5 | measured |
| `Faithful/DivRemChip.lean:480` | `divRemComparisonBlocks_roundtrip` | 400000 | **> 40000, top UNKNOWN** | §5 + git `f6d3c773` | measured (lower only) |
| `Faithful/DivRemChip.lean:529` | `divRemArithmeticBlocks_roundtrip` | 800000 | **> 40000, top UNKNOWN** | §5 + git `f6d3c773` | measured (lower only) |
| `Faithful/DivRemChip.lean:592` | `divRemResultBlocks_roundtrip` | 400000 | **> 40000, top UNKNOWN** | §5 + git `f6d3c773` | measured (lower only) |
| `Faithful/DivRemChip.lean:1122` | `divRemChip_lookups_empty` | 800000 | **> 40000, top UNKNOWN** | §5 + git `f6d3c773` | measured (lower only) |
| `Faithful/DivRemChip/Exact.lean:1755` | `divRemCoreForallDecompose` | 400000 | (40000, 100000] | §5 | measured |
| `Faithful/DivRemChip/Exact.lean:1790` | `divRemLowerBackward` | 400000 | (40000, 100000] | §5 | measured |
| `Faithful/DivRemChip/Exact.lean:1862` | `divRemUpperBackward` | 400000 | (40000, 100000] | §5 | measured |
| `Faithful/DivRemChip/Exact.lean:2197` | `divRemWholeAssertionsExact` | 800000 | (100000, 200000] | §5 | measured |
| `Faithful/LtChip.lean:1477` | `ltChip_interactions_faithful` | **200000** | (100000, 200000] | §5 | measured |
| `Faithful/LtOperationUnsigned.lean:30` | `ltUnsigned_constraints_faithful` | 400000 | (50000, 60000] | in-source **+** §5 (agree) | measured |
| `Faithful/MulChip.lean:1091` | `mulOperation_assertions_forward` | **100000** | (40000, 60000] | §5 + git `5c71054d` | measured |
| `Faithful/MulChip.lean:1517` | `mulOperation_assertions_backward` | **100000** | (40000, 80000] | §5 + git `5c71054d` | measured |
| `Faithful/MulChip.lean:1715` | `mulChip_constraints_faithful` | 600000 | **> 40000, top UNKNOWN** | §5 + git `5c71054d` | measured (lower only) |
| `Faithful/MulChip.lean:3186` | `mulChip_interactions_faithful` | 1000000 | **> 40000, top UNKNOWN** | §5 + git `5c71054d` | measured (lower only) |
| `Faithful/ShiftLeftChip.lean:723` | `shiftLeftCoreAssertions` | 240000 | (40000, 60000] | in-source (git `46231bc8`) — **§5 stale** | measured |
| `Faithful/ShiftRightChip.lean:849` | `shiftRightCoreAssertions` | 240000 | (40000, 60000] | in-source (git `46231bc8`) — **§5 stale** | measured |
| `Faithful/SubChip.lean:159` | `subcols_state_interactions_faithful_syntactic` | 250000 | (40000, 60000] | §5 | measured |
| `Faithful/SubChip.lean:206` | `subcols_program_interactions_faithful_syntactic` | 250000 | (40000, 60000] | §5 | measured |
| `Faithful/SubChip.lean:726` | `subChip_interactions_faithful` | 400000 | (60000, 100000] | §5 | measured |
| `Faithful/SubwChip.lean:215` | `subwcols_state_interactions_faithful_syntactic` | 250000 | (40000, 60000] | §5 | measured |
| `Faithful/SubwChip.lean:278` | `subwcols_program_interactions_faithful_syntactic` | 250000 | (40000, 60000] | §5 | measured |
| `Faithful/SubwChip.lean:829` | `subwChip_interactions_faithful` | 400000 | (60000, 100000] | §5 | measured |

### `Native/` (8), `Model/` (2), `Soundness/` (1)

| file:line | declaration | declared | floor bracket | source | conf |
|---|---|---:|---|---|---|
| `Native/Operations/AddrAddOperation/RawSpec.lean:132` | `carries_of_addrAddSemantics` | 400000 | (45000, 60000] | in-source + §5 (cites `:134`) | measured |
| `Native/Operations/DivRemOperation/OwnAsserts.lean:20` | `ownAsserts` | 500000 | (40000, 100000] — **§5 says (40000, 50000]** | in-source (2026-07-27, later) | measured |
| `Native/Operations/LtOperationUnsigned/RawSpec.lean:34` | `at_most_one` | 1000000 | **(400000, 500000]** | in-source (file docstring, names the decl) + §5 | measured |
| `Native/Operations/MulOperation/Defs.lean:20` | `main` (`«LCNF compiler»`-bound) | 400000 | (40000, 60000] | in-source + §5 | measured |
| `Native/Operations/MulOperation/RawSpec.lean:114` | `full_product` | 6000000 | **(1000000, 1200000]** — highest in the tree | in-source + §5 | measured |
| `Native/Operations/MulOperation/RawSpec.lean:894` | `mulSemantics_of_raw` | 500000 | (60000, 100000] | in-source + §5 (cites `:904`) | measured |
| `Native/Operations/SubOperation/RawSpec.lean:38` | `subSemantics_of_carries` | 400000 | (60000, 80000] | in-source + §5 | measured |
| `Native/Operations/SubOperation/RawSpec.lean:90` | `carries_of_subSemantics` | 400000 | (40000, 60000] | in-source + §5 (cites `:91`) | measured |
| `Model/SailDecode.lean:49` ⚑ **file-scoped** | whole file (owner: the branch-skip walk) | 400000 | (40000, 50000] | in-source + §5 | measured |
| `Model/SailWrap.lean:316` | `rX_bits_eq_get_reg?` | 400000 | (50000, 100000] | in-source + §5 | measured |
| `Soundness/RowSoundness.lean:61` | `supportedChip_usesSupportedBusChannels` | 800000 | (100000, 200000] | §5 + git `6a6d1017` | measured |

### `Proofs/` (53 sites)

| file:line | declaration | declared | floor bracket | source | conf |
|---|---|---:|---|---|---|
| `Proofs/Chips/BitwiseChip/Formal.lean:213` | `completeness` | 5000000 | (700000, 1000000] | in-source + §5 (cites `:217`) | measured |
| `Proofs/Chips/BranchChip/Core.lean:19` | `soundness` | 400000 | (40000, 100000] | **git `502b925b` only** — absent from §5 and from the source | measured |
| `Proofs/Chips/DivRemChip/Completeness/OwnComplete.lean:126` | `ownAsserts_complete` | 800000 | (100000, 200000] | §5 + git `bb3488d0` | measured |
| `Proofs/Chips/DivRemChip/Defs.lean:1137` | `derivedElaborated` | 250000 | (39999, 50000] | **in-source only** — absent from §5 | measured |
| `Proofs/Chips/DivRemChip/Evidence.lean:110` | `compareAssumptionsOfCore` | 400000 | (60000, 100000] | in-source + §5 | measured |
| `Proofs/Chips/DivRemChip/Evidence/Signed32.lean:39` | `signed32Evidence` | 4000000 | (400000, 1000000] | in-source + §5 + git `2dd6af26` | measured |
| `Proofs/Chips/DivRemChip/Evidence/Signed64.lean:39` | `signed64Evidence` | 4000000 | (400000, 1000000] | in-source + §5 + git `2dd6af26` | measured |
| `Proofs/Chips/DivRemChip/Evidence/Unsigned32.lean:38` | `unsigned32Evidence` | 2000000 | (100000, 400000] | in-source + §5 + git `2dd6af26` | measured |
| `Proofs/Chips/DivRemChip/Evidence/Unsigned64.lean:50` | `unsigned64Evidence` | 2000000 | (40000, 400000] | in-source + §5 + git `2dd6af26` | measured |
| `Proofs/Chips/DivRemChip/Soundness.lean:292` | `euclid_identity_signed` | 500000 | (50000, 100000] | in-source + §5 | measured |
| `Proofs/Chips/DivRemChip/Soundness.lean:596` | `euclid_identity_word_unsigned` | 400000 | (20000, 50000] | in-source + §5 | measured |
| `Proofs/Chips/DivRemChip/Soundness.lean:678` | `euclid_identity_word_signed` | 500000 | (50000, 100000] | in-source + §5 | measured |
| `Proofs/Chips/JalrChip/Formal.lean:63` | `soundness` | 8000000 | **(2000000, 4000000]** | in-source + §5 | measured |
| `Proofs/Chips/JalrChip/Formal.lean:192` | `completeness` | 8000000 | **(2000000, 4000000]** | in-source + §5 (cites `:193`) | measured |
| `Proofs/Chips/LoadByteChip/Formal.lean:34` | `soundness` | 2000000 | ≤ 400000 (§5: (300000, 400000]) | in-source (file-level, names both) + §5 | measured |
| `Proofs/Chips/LoadByteChip/Formal.lean:170` | `completeness` | 1500000 | ≤ 300000 (§5: (150000, 300000]) | in-source (`:33`) + §5 | measured |
| `Proofs/Chips/LoadDoubleChip/Formal.lean:26` | `soundness` | 1500000 | (150000, 300000] — **§5's uniform row is wrong here** | in-source (`:25`) | measured |
| `Proofs/Chips/LoadDoubleChip/Formal.lean:90` | `completeness` | 1500000 | (150000, 300000] | in-source (`:25`) | measured |
| `Proofs/Chips/LoadHalfChip/Formal.lean:50` | `soundness` | 2000000 | ≤ 400000 (§5: (300000, 400000]) | in-source (`:49`) + §5 | measured |
| `Proofs/Chips/LoadHalfChip/Formal.lean:150` | `completeness` | 1500000 | ≤ 300000 (§5: (150000, 300000]) | in-source (`:49`) + §5 | measured |
| `Proofs/Chips/LoadWordChip/Formal.lean:37` | `soundness` | 2000000 | ≤ 400000 (§5: (300000, 400000]) | in-source (`:36`) + §5 | measured |
| `Proofs/Chips/LoadWordChip/Formal.lean:144` | `completeness` | 1500000 | ≤ 300000 (§5: (150000, 300000]) | in-source (`:36`) + §5 | measured |
| `Proofs/Chips/LoadX0Chip/Formal.lean:24` | `soundness` | 2000000 | ≤ 400000 (§5: (300000, 400000]) | in-source (`:23`) + §5 | measured |
| `Proofs/Chips/LoadX0Chip/Formal.lean:100` | `completeness` | 1500000 | ≤ 300000 (§5: (150000, 300000]) | in-source (`:23`) + §5 | measured |
| `Proofs/Chips/LtChip/Formal.lean:157` | `soundness` | 500000 | (60000, 100000] | in-source + §5 | measured |
| `Proofs/Chips/LtChip/Formal.lean:207` | `completeness` | 300000 | (45000, 60000] | in-source + §5 (cites `:208`) | measured |
| `Proofs/Chips/MulChip/Contracts.lean:35` | `controlExpressions_subset_shallowConstraints` | 400000 | (40000, 100000] | in-source + §5 | measured |
| `Proofs/Chips/MulChip/Formal.lean:77` | `soundness` | 400000 | (60000, 80000] | in-source + §5 + git `a1580968` | measured |
| `Proofs/Chips/MulChip/Formal.lean:182` | `completeness` | 400000 | (60000, 80000] | in-source + §5 + git `a1580968` | measured |
| `Proofs/Chips/MulChip/Formal.lean:378` | `circuit` | 800000 | (150000, 200000] | in-source + §5 + git `a1580968` | measured |
| `Proofs/Chips/ShiftLeftChip/Soundness/Sll.lean:35` | `soundness` | 1600000 | (200000, 400000] | in-source + §5 + git `f722f6c1` | measured |
| `Proofs/Chips/ShiftLeftChip/Soundness/Sllw.lean:38` | `soundness` | 800000 | (100000, 200000] | in-source + §5 + git `f722f6c1` | measured |
| `Proofs/Chips/ShiftRightChip/Core.lean:1591` | `srlw_within_byte_shift` | 1600000 | (250000, 320000] | in-source + §5 | measured |
| `Proofs/Chips/ShiftRightChip/Defs.lean:1735` | `resultA_isU64` | 400000 | (39996, 100000] | **git `502b925b` only** — absent from §5 and from the source | measured |
| `Proofs/Chips/ShiftRightChip/Soundness/Sra.lean:29` | `soundness` | 1600000 | (200000, 400000] | §5 + git `f722f6c1` | measured |
| `Proofs/Chips/ShiftRightChip/Soundness/Sraw.lean:29` | `soundness` | 1600000 | (200000, 400000] | §5 + git `f722f6c1` | measured |
| `Proofs/Chips/ShiftRightChip/Soundness/Srl.lean:29` | `soundness` | 800000 | (100000, 200000] | §5 + git `f722f6c1` | measured |
| `Proofs/Chips/ShiftRightChip/Soundness/Srlw.lean:29` | `soundness` | 800000 | (100000, 200000] | §5 + git `f722f6c1` | measured |
| `Proofs/Chips/StoreByteChip/Formal.lean:25` | `soundness` | 2000000 | ≤ 400000 (§5: (300000, 400000]) | in-source (`:23`) + §5 | measured |
| `Proofs/Chips/StoreByteChip/Formal.lean:130` | `completeness` | 1500000 | ≤ 300000 (§5: (150000, 300000]) | in-source (`:23`) + §5 | measured |
| `Proofs/Chips/StoreByteChip/Formal.lean:252` | `circuit` | 2000000 | **(1000000, 2000000]** | in-source (`:24`) + §5 | measured |
| `Proofs/Chips/StoreDoubleChip/Formal.lean:23` | `soundness` | 1500000 | (150000, 300000] — **§5's uniform row is wrong here** | in-source (`:22`) | measured |
| `Proofs/Chips/StoreDoubleChip/Formal.lean:73` | `completeness` | 1500000 | (150000, 300000] | in-source (`:22`) | measured |
| `Proofs/Chips/StoreHalfChip/Formal.lean:24` | `soundness` | 1500000 | (150000, 300000] — **§5's uniform row is wrong here** | in-source (`:23`) | measured |
| `Proofs/Chips/StoreHalfChip/Formal.lean:105` | `completeness` | 1500000 | (150000, 300000] | in-source (`:23`) | measured |
| `Proofs/Chips/StoreWordChip/Formal.lean:24` | `soundness` | 1500000 | (150000, 300000] — **§5's uniform row is wrong here** | in-source (`:23`) | measured |
| `Proofs/Chips/StoreWordChip/Formal.lean:93` | `completeness` | 1500000 | (150000, 300000] | in-source (`:23`) | measured |
| `Proofs/Chips/UTypeChip/Formal.lean:66` | `soundness` | 500000 | (40000, 100000] | in-source + §5 | measured |
| `Proofs/Chips/UTypeChip/Formal.lean:139` | `completeness` | 500000 | (40000, 100000] | in-source + §5 | measured |
| `Proofs/Operations/DivRemOperation/Core.lean:299` | `soundness` | 500000 | (80000, 100000] | §5 (cites `:301`); git `e3b924ec` fixes only "> 40000" | measured |
| `Proofs/Operations/DivRemOperation/Core.lean:469` | `completeness` | 400000 | (60000, 80000] | §5 (cites `:471`); git `e3b924ec` fixes only "> 40000" | measured |
| `Proofs/Operations/MulOperation/Formal.lean:98` | `soundness` | 1000000 | (100000, 200000] — **§5 has this pair swapped** | in-source | measured |
| `Proofs/Operations/MulOperation/Formal.lean:602` | `completeness` | 1000000 | (100000, 150000] — **§5 has this pair swapped** | in-source | measured |

### The three counts Phase 1 needs

| bucket | count | meaning |
|---|---:|---|
| **floor top ≤ 200000** | **60** | candidate *pure deletions* — Lean's plain default is 200000 |
| **floor top > 200000** | **35** | genuine; keep, and take them to Phase 3 cause work |
| **UNKNOWN** | **6** | a fail rung but no recorded pass — must be measured before any decision |

Per pillar: `Faithful/` 28 / 3 / 6 · `Proofs/` 23 / 30 / 0 · `Native/` 6 / 2 / 0 · `Model/` 2 / 0 / 0 ·
`Soundness/` 1 / 0 / 0.

**The 6 UNKNOWN sites** — all recorded as "> 40000, binds at `whnf`" with no passing rung ever laddered:

- `Faithful/DivRemChip.lean:480` `divRemComparisonBlocks_roundtrip` (400000)
- `Faithful/DivRemChip.lean:529` `divRemArithmeticBlocks_roundtrip` (800000)
- `Faithful/DivRemChip.lean:592` `divRemResultBlocks_roundtrip` (400000)
- `Faithful/DivRemChip.lean:1122` `divRemChip_lookups_empty` (800000)
- `Faithful/MulChip.lean:1715` `mulChip_constraints_faithful` (600000)
- `Faithful/MulChip.lean:3186` `mulChip_interactions_faithful` (1000000)

Applying §5's own "size at ~4× the bracket top" convention *backwards* to their declared values would
guess tops of 100000 / 200000 / 100000 / 200000 / 150000 / 250000. **That is a guess, not a floor** —
those five files' declared values were also chosen partly from a sibling-screen ranking, and W6/b4
records masking inside `Faithful/MulChip.lean` hiding a site at ≥25× over. Ladder them.

### Deletion hazards inside the "≤ 200000" bucket

Three shapes need care even though they qualify:

1. **13 zero-margin sites** whose bracket top is *exactly* 200000, so deleting them leaves a 1× margin —
   and §2's LSP caveat says those floors were measured **without** the pillar libs' `moreLeanArgs`:
   `Faithful/BitwiseChip.lean:408,815` · `Faithful/BranchChip.lean:536,747` ·
   `Faithful/DivRemChip/Exact.lean:2197` · `Faithful/LtChip.lean:1477` · `Soundness/RowSoundness.lean:61` ·
   `Proofs/Chips/DivRemChip/Completeness/OwnComplete.lean:126` · `Proofs/Chips/MulChip/Formal.lean:378` ·
   `Proofs/Chips/ShiftLeftChip/Soundness/Sllw.lean:38` ·
   `Proofs/Chips/ShiftRightChip/Soundness/Srl.lean:29`, `Srlw.lean:29` ·
   `Proofs/Operations/MulOperation/Formal.lean:98`. Re-ladder each under a real `lake build` before
   deleting; do not trust the recorded pass rung at 1×.
2. **Three stamps at or below the plain default**, where deleting *raises* the budget rather than
   lowering it: `Faithful/MulChip.lean:1091` and `:1517` (both **100000**) and
   `Faithful/LtChip.lean:1477` (**200000**, a literal no-op stamp). §5 is right that these are a
   deliberate tightening signal, not a budget — deleting them is safe but discards the signal, so it is
   an owner call, not a mechanical one.
3. **One file-scoped stamp**: `Model/SailDecode.lean:49` has no `in`, so it covers all 57 declarations
   in the file, and the recorded (40000, 50000] belongs to the whole-file walk. Its in-source note
   argues for keeping a site here on purpose (the failure mode is a mid-cascade error, and cost scales
   with the Sail decoder's branch count). Do not delete it on the arithmetic alone.

Also mechanical, not a hazard: six sites carry a `maxRecDepth` directive on an adjacent line
(`Faithful/BranchChip.lean:746,1060` · `Faithful/DivRemChip.lean:481,530,593` ·
`Faithful/DivRemChip/Exact.lean:2198`). Delete only the budget line.

### Reconciliation — every divergence found

Nine classes, worst first. Everything here is a place a future maintainer would have trusted §5 and
been wrong.

1. **A removed ceiling still listed as a KEEP.** §5's first `Faithful/` row —
   `DivRemChip/Exact.lean:1128` `divRemRustAssertionsDecompose`, "64M (unchanged, ~4×)" — was
   **removed** in `46231bc8`; one `simp only [List.append_cancel_left_eq]` took the file 278s → 10s and
   the true floor to (10000, 20000]. §5's §3/§5/§7 prose still cites it as "the repo's single most
   expensive declaration". `Faithful/DivRemChip/Exact.lean` now has four sites, not five.
2. **Two re-measured rows never updated.** §5 lists `shift{Right,Left}CoreAssertions` at declared 4M,
   floor (40000, 100000], kept 400000. The same commit `46231bc8` squeezed their `simp`s to `simp only`,
   narrowed both floors to **(40000, 60000]** and lowered both to **240000**. The in-source comments are
   correct; §5 is a generation behind.
3. **A uniform row that is wrong for four of its nine members.** §5 asserts "nine Load/Store
   `Formal.lean` `soundness` | (300k, 400k] | 2000000". Only five match (LoadByte, LoadHalf, LoadWord,
   LoadX0, StoreByte). `LoadDouble`, `StoreDouble`, `StoreHalf`, `StoreWord` are declared **1500000**
   and their in-source note reads "both proofs in (150000, 300000]" — a different floor *and* a
   different kept value. This is exactly the "a uniform value across a family is a copied default"
   trap §7 warns about, reproduced inside the record of the fix.
4. **A swapped pair.** §5's `Proofs/Operations/MulOperation/Formal.lean:100,607` row gives
   "(100k, 150k] / (100k, 200k]". The in-source ladders say the opposite: `soundness` (line 98) "fails
   at 100k, passes at the plain default" = (100000, 200000]; `completeness` (line 602) "fails at 100k,
   passes at 150k" = (100000, 150000]. Both tops are ≤ 200000 so no Phase-1 decision changes, but the
   attribution is inverted. In-source wins — it sits on the declaration.
5. **A conflicting bracket.** `Native/Operations/DivRemOperation/OwnAsserts.lean:20` `ownAsserts`:
   §5 says (40000, 50000]; the in-source ladder, dated 2026-07-27 and therefore later, records
   `40000 FAILS / 100000 ok` = **(40000, 100000]** and is self-consistent with its own stated "500000
   keeps ~5x margin". §5's 50000 is most likely transcribed from the adjacent `Model/SailDecode.lean`
   row, which genuinely is (40000, 50000]. Taking the wider bracket costs nothing here (both tops are
   ≤ 200000).
6. **A wrong "declared before" value.** §5 puts
   `DivRemChip/Completeness/OwnComplete.lean:126` at 16M before; `bb3488d0` records **64,000,000 →
   800,000**. The floor (100000, 200000] is right.
7. **Three sites §5 does not cover at all.** `Proofs/Chips/BranchChip/Core.lean:19` `soundness`
   (40000, 100000] and `Proofs/Chips/ShiftRightChip/Defs.lean:1735` `resultA_isU64` (39996, 100000],
   both recorded **only** in commit `502b925b`'s body; and `Proofs/Chips/DivRemChip/Defs.lean:1137`
   `derivedElaborated` (39999, 50000], recorded **only** in-source. A grep of §5 for these would
   return nothing and a reader would call them UNKNOWN.
8. **Stale line numbers, 11 rows.** §5 cites `AluX0:211,331` (now 208, 328) · `MulChip:1716, 3203,
   1092, 1518` (now 1715, 3186, 1091, 1517) · `MulOperation/RawSpec:904` (894) ·
   `SubOperation/RawSpec:91` (90) · `AddrAddOperation/RawSpec:134` (132) ·
   `BitwiseChip/Formal:217` (213) · `LtChip/Formal:208` (207) · `JalrChip/Formal:193` (192) ·
   `DivRemOperation/Core:301,471` (299, 469) · `MulOperation/Formal:100,607` (98, 602) ·
   `ShiftLeftChip:722` / `ShiftRightChip:848` (723, 849). Declarations all resolve; only the anchors
   drifted.
9. **Headline counts off by one.** §1 and §5's headings say 102 hand-written sites and 38 `Faithful/`
   survivors. The tree has **101** and **37** (divergence 1). `scripts/heartbeats_baseline.txt` is the
   live number; this file is not.

Nothing in the reverse direction was found: every §5 row that is not listed above matches the tree, and
no site exists that §5 claims does not.

### Plausibility check — declared value vs recorded floor

Nothing is left at a ≤ 40000 floor (that was the campaign's removal threshold), so the "4M stamp with a
claimed tiny floor that nobody removed" shape does not occur. The over-provisioned tail is mild and
almost all of it is documented as deliberate:

- `Proofs/Chips/DivRemChip/Soundness.lean:596` — 400000 vs a (20000, 50000] top: **8×**, the widest
  ratio in the tree, and the only one with no stated reason. Prime Phase-3 candidate.
- `Model/SailDecode.lean:49` (8×), `Native/Operations/LtOperationUnsigned/RawSpec.lean:34` (in fact
  ~2×, correctly sized), `Native/Operations/MulOperation/Defs.lean:20` (6.7×, justified: LCNF cost is
  load-sensitive), `Faithful/LtOperationUnsigned.lean:30` (6.7×, justified in-source) — all carry an
  explicit argument for the extra headroom.
- The four UNKNOWN `Faithful/DivRemChip` roundtrips and two `Faithful/MulChip` anchors sit at
  400000–1000000 against a floor known only to exceed 40000; if their true tops are near 40000 they are
  10–25× over. This is the single largest block of unmeasured slack left.

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

---

## 9. Diagnosing a site: the instrument (`diagnostics true`)

Everything above answers *how much* a declaration costs. This section is about *why*. Clean's
`doc/performance-problems.md` § "Measuring honestly" prescribes an instrument this project had never used
— `set_option diagnostics true` — and the ceiling campaign ran entirely on ladder bisection instead.
**Validated 2026-08-01 on Lean 4.31 against four sites whose cause was already known, then applied to two
that were not.** Verdict: it works, it is cheap, and it discriminates three of our four cause classes.
It does **not** subsume the ladder — the two answer different questions, see §9.5.

### 9.1 The commands

The runner. `lake env lean` does **not** apply the package's per-lib lean args, so pass them yourself or
you are measuring a different configuration than `lake build` does (§6, and
[`lake_env_lean_not_a_gate`]):

```sh
cd <repo root>
lake env lean --tstack=400000 \
  -DsynthInstance.maxHeartbeats=1000000 \
  -Dlinter.style.lambdaSyntax=true -Dlinter.style.dollarSyntax=true \
  -Dlinter.style.refine=true      -Dlinter.style.cases=true \
  -Dlinter.style.induction=true   -Dlinter.style.admit=true \
  -Dlinter.oldObtain=true         -Dlinter.style.cdot=true \
  SP1Clean/<Path>/<File>.lean
```

The instrument itself is a scoped option on the declaration you are diagnosing:

```lean
set_option diagnostics true in     -- add this line, nothing else
-- …the file's existing scoped budget directive, left exactly as it is…
theorem soundness : … := by …
```

Order relative to the existing directive does not matter — tested in both positions, and interleaved with
`maxRecDepth` / `linter.unusedSimpArgs` stamps. The option is scoped to the single next declaration, so a
1000-line file reports only the site you marked.

Two knobs worth knowing:

- `set_option diagnostics.threshold <n> in` — **the default is 20**, so any counter below 21 is invisible.
  A lemma that fires 4 times and a lemma that never fires look identical in this report. When the question
  is *"did X fire at all?"* the report cannot answer it; drop the threshold to 1, or use the trace (§9.7).
- `set_option trace.Meta.Tactic.simp.rewrite true in` — the full rewrite log (§9.7). Two orders of
  magnitude more output; use it only after `diagnostics` has named a suspect.

`#count_heartbeats` remains useless for this (§6) and nothing below changes that.

### 9.2 What the output looks like here

One marked declaration emits, in order: a `[simp] Diagnostics` block **per `simp` call** in the proof, then
a `[<kind>] <declName>` term census, then a final `[diag] Diagnostics` block covering the whole declaration
(elaboration counters, then `[kernel]` counters from the type-check re-run). Trimmed real output from
`Proofs/Chips/LoadByteChip/Formal.lean` `soundness`:

```
[theorem] SP1Clean.LoadByteChip.soundness
  [size] 169280
  [occs] And ↦ 5570
  [occs] Eq ↦ 4873
  …
[diag] Diagnostics
  [reduction] unfolded declarations (max: 450604, num: 98):
    [reduction] Nat.rec ↦ 450604
    [reduction] List.rec ↦ 327222
    [reduction] Vector.mapRange ↦ 323040
    [reduction] List.concat ↦ 238275
    [reduction] Array.push ↦ 164019
    [reduction] Vector.push ↦ 150752
    [reduction] Eq.rec ↦ 59095
    [reduction] ProvableStruct.componentsFromElements ↦ 20640
    [reduction] ProvableStruct.componentsToElements ↦ 17885
    [reduction] varFromOffset ↦ 5155
  [reduction] unfolded reducible declarations (max: 452349, num: 100):
    [reduction] Nat.casesOn ↦ 452349
    [reduction] Vector.toArray ↦ 373167
    [reduction] Array.toList ↦ 372110
    [reduction] List.toArray ↦ 191792
  [def_eq] heuristic for solving `f a =?= f b` (max: 371, num: 22): …
  [kernel] unfolded declarations (max: …): …
```

Four fields carry the signal:

| field | reads as |
|---|---|
| `[reduction] unfolded declarations` | **whnf**. Clean's runaway signature (`Eq.rec`/`List.rec`/`Nat.rec`/`dite`/`Vector.append` in the tens of thousands) lives here, and the *named* SP1/Clean entries below the generic recursors say *which* value is being torn open. |
| `[reduction] unfolded reducible declarations` | same, for `@[reducible]` defs and `casesOn`. `Vector.toArray`/`Array.toList`/`List.toArray` in the hundreds of thousands = a `Vector ↔ Array ↔ List` round-trip. |
| `[simp] used / tried theorems` | per-`simp` census with success counts. `X ↦ n ❌️` = tried `n` times, never fired — the failed-match cost a `simp only` would delete. |
| `[<kind>] <name> [size]/[occs]` | the produced **term**. `Mathlib.Tactic.Ring.Common.*` dominating `occs` means the cost is `ring` building a big term, not whnf. |

### 9.3 It works on a **failing** declaration, and the profile is scale-invariant

This was the operationally critical unknown — our targets are the ones that time out. Answer: the
`[diag]` block is emitted **before** the error and is unaffected by it. Confirmed on a synthetic
`whnf` timeout, a synthetic `maxRecDepth` overflow, and on a real site.

Better than that: the *ranking* does not depend on the budget. `LoadByteChip.soundness`, run to completion
vs. force-failed at a 40000 budget (add a second, lower scoped directive **below** the existing one — inner
wins, so nothing on disk has to change):

| counter | passes at 2M | fails at 40000 | ratio |
|---|---:|---:|---:|
| `Nat.rec` | 450604 | 42967 | 10.5× |
| `List.rec` | 327222 | 30829 | 10.6× |
| `Vector.mapRange` | 323040 | 29970 | 10.8× |
| `List.concat` | 238275 | 22131 | 10.8× |
| `Array.push` | 164019 | 15263 | 10.7× |
| `Eq.rec` | 59095 | 6015 | 9.8× |

Same top ten, same order, one uniform scale factor. **So diagnose at a LOW budget, not a raised one.**
The loop is: add `diagnostics true` + a low scoped budget → read the ranking → fix → drop both and
re-ladder. No need to raise anything, and the failing run is the faster of the two (11.9 s vs 20.9 s here).

Caveat: force-failing a producer re-triggers the masking cascade of §6 — the dependents in the file report
`(kernel) unknown constant`. That is expected and does not affect the `[diag]` block.

**Scale-invariance holds for ONE declaration across budgets — not for two variants at a shared cutoff.**
The table above compares the *same* declaration at 2M and at 40000. It does **not** license comparing a
before-fix and an after-fix variant at a budget neither one reaches: at a cutoff both variants fail at, each
one's counters are truncated at wherever its own elaboration happened to be when the budget ran out, and the
ratio between them measures nothing. If you want to know whether a fix worked, ladder it — the bracket is
the answer. Use the counters to find the *mechanism*, not to score the fix.

### 9.4 What it discriminates — and what it does not

Four controls, causes known in advance:

| site | known cause | what the counters said | verdict |
|---|---|---|---|
| `Native/Operations/MulOperation/RawSpec.lean` `full_product` (floor (1M, 1.2M]) | term-intrinsic: 16-column `omega` telescope over `2^128` literals + a 256-monomial `ring` | `occs` = `Mathlib.Tactic.Ring.Common.*` (4211 + 1006 + 918 + …) on a `[size] 61385` term; reductions are `OfNat.ofNat ↦ 786960`, `HPow.hPow`/`Pow.pow ↦ 786952`, `Monoid.npow ↦ 393476`; `Lean.Omega.Coeffs.isZero ↦ 3924` | ✅ **confirmed and sharpened** — the `2^128` coefficients are literally being evaluated through `Monoid.npow`/`Nat.rec`; `ring` and `omega` are both visible and separable |
| `Native/Operations/MulOperation/Defs.lean` `main` (codegen-bound) | `«LCNF compiler»`; elaborates fine at 40000, only code generation times out | max reduction counter `LT.lt ↦ 21950`; **no counter attributable to the compiler at all**. The only evidence is the error string: ``timeout at `«LCNF compiler»` `` | ❌ **does not discriminate — and actively misleads.** 21950 is "tens of thousands", i.e. a false positive against Clean's whnf heuristic, on a declaration whose elaboration is not the problem |
| `Proofs/Chips/MulChip/Formal.lean` `soundness` (floor (60k, 80k]) | `circuit_proof_start` tower | `List.rec ↦ 15820`, `Eq.rec ↦ 14872`, `Nat.rec ↦ 13459`, then the named culprits `ProvableStruct.componentsToElements ↦ 4790`, `toElements ↦ 4196`, `Vector.mapRange ↦ 2520`; kernel `List.rec ↦ 46179` | ✅ correct class, and names the row-eval path |
| `Faithful/DivRemChip.lean` `divRemComparisonBlocks_roundtrip` (`Vector`-append/`congr` tower) | expected `Vector.append`/`Eq.rec` in the tens of thousands | **not** those: `Nat.rec ↦ 95308`, `Nat.pred ↦ 93912`, `Nat.casesOn ↦ 190633`, plus the `DivRemChip.Columns.*` projections ~430 each and `Lean.Omega.*` all through the kernel counters | ✅ right class (runaway whnf), **wrong culprit guessed** — the cost is literal index arithmetic (`Nat.pred` chains from the `(by decide)`/`(by omega)` offset side conditions), not `Vector.append` |

Read the last row twice. The instrument was right and the standing hypothesis was wrong; that is the whole
argument for running it before writing a fix.

So, per cause class (the §4 taxonomy):

- **whnf-into-expensive-values** — discriminated, and usually names the value. Best case for the tool.
- **`simp` set thrash** — discriminated precisely, with per-lemma success counts (§9.6).
- **term-intrinsic arithmetic (`ring`/`omega`/`bv_decide`)** — discriminated: the tactic's own lemma
  namespace dominates `occs`, and the reduction counters point at numeral evaluation rather than at a
  project datatype.
- **codegen (`«LCNF compiler»`)** — **not** discriminated. The counters are silent on it and can read as a
  whnf blowup. The discriminator for this class is the *phase name in the error*, which the ladder already
  gives you for free. Never diagnose a `def` on counters alone.

### 9.5 Versus ladder bisection

They answer different questions and neither replaces the other.

| | ladder bisection | `diagnostics true` |
|---|---|---|
| answers | *how much* — the floor bracket, hence how much a directive is over | *why* — which reduction/lemma/tactic is spending it |
| output | pass/fail per rung, plus the phase name and owning declaration | ranked counters |
| runs needed | 3–5 re-elaborations (bisecting rungs) | **1** |
| cost | 1 file elaboration per rung | 1 file elaboration + 2–30 % (measured below) |
| tells you the declaration is over-provisioned | yes | no |
| tells you what to change | no | usually |
| works on codegen-bound sites | yes (phase name) | no |

Measured overhead of adding the option, per whole-file elaboration:

| file | site | baseline | with `diagnostics` |
|---|---|---:|---:|
| `Native/Operations/MulOperation/RawSpec.lean` | `full_product` | 39.2 s | 41.7 s (+6 %) |
| `Native/Operations/MulOperation/Defs.lean` | `main` | 4.7 s | 4.8 s (+2 %) |
| `Faithful/DivRemChip.lean` | `divRemComparisonBlocks_roundtrip` | 8.7 s | 9.6 s (+10 %) |
| `Faithful/AddChip.lean` | `addcols_state_…_syntactic` | 5.4 s | 6.3 s (+17 %) |
| `Proofs/Chips/LoadByteChip/Formal.lean` | `soundness` | 16.8 s | 20.9 s (+24 %) |
| `Proofs/Chips/MulChip/Formal.lean` | `soundness` | 11.4 s | 14.8 s (+30 %) |

**A diagnostic run costs about one ladder rung.** The practical order is therefore: ladder first to get the
bracket (you need it anyway to size or delete the directive); if the floor is genuinely high, spend one
more run on `diagnostics` before writing any fix.

### 9.6 The two undiagnosed sites

**(a) `Faithful/AddChip.lean` `addcols_state_interactions_faithful_syntactic`** — representative of the
17-site `Faithful/` cluster that closes with a bare non-`only` `simp` over an unfolded native operations
list plus an unfolded extracted oracle list. Named mechanism, and it is not the lists:

```
[simp] used theorems (max: 1216, num: 29):
  nonempty_prop ↦ 1216 · isEmpty_Prop ↦ 608 · Decidable.not_not ↦ 456 · List.map_cons ↦ 342 …
[simp] tried theorems (max: 1216, num: 61):
  forall_const ↦ 1216 ❌️ · forall_eq ↦ 1216 ❌️ · implies_true ↦ 1216 ❌️
  eq_iff_eq_cancel_left ↦ 608 ❌️ · forall_apply_eq_imp_iff ↦ 608 ❌️ · imp_self ↦ 608 ❌️
  Finset.diag_mem_sym2_mem_iff ↦ 608 ❌️ · Module.isTorsionBySet_singleton_iff ↦ 608 ❌️
  SetLike.forall_smul_mem_iff ↦ 608 ❌️ · Subgroup.forall_mem_sup ↦ 608 ❌️
  Submodule.forall_mem_sup ↦ 608 ❌️ · Subsingleton.forall₂_iff ↦ 608 ❌️ …
[diag] unfolded reducible declarations:
  Channel.Guarantees ↦ 10108 · Ne ↦ 1976 · Channel.name ↦ 1710 · Module.IsTorsionBySet ↦ 608
```

`Channel.toRaw_ext_iff` fires 38 times, and the rewrite trace shows what each firing does: it tears the
`RawChannel` record open into a conjunction whose third and fourth components are `HEq`s of the
**`Guarantees`/`Requirements` predicate lambdas** —

```
byteChannel.toRaw = stateChannel.toRaw
  ==>  byteChannel.name = stateChannel.name ∧ size ByteRow = size StateMsg ∧
       ((fun mult message data => mult = -1 → byteChannel.Guarantees (fromElements message) data) ≍
         fun mult message data => mult = -1 → stateChannel.Guarantees (fromElements message) data) ∧ …
```

simp then descends into those lambdas. Per firing that costs exactly 32 `nonempty_prop` + 16
`isEmpty_Prop` + 12 `Decidable.not_not` rewrites of `Nonempty (mult = -1)` / `IsEmpty (mult = -1)`, and
each of the 16 residual `∀`-shaped props draws mathlib's entire `∀ x ∈ S` discrimination bucket — ~20
lemmas, every one of which fails. **38 firings → ≈2,300 rewrites and ≈12,000 failed matches, none of
which touch the interaction lists the theorem is actually about.**

Confirmed on a sibling: `Faithful/SubwChip.lean` `subwcols_state_interactions_faithful_syntactic` gives
36 firings, `nonempty_prop ↦ 1152` (= 36×32), `isEmpty_Prop ↦ 576` (= 36×16),
`Channel.Guarantees ↦ 9576`. The ratios are identical, so **one mechanism does explain the cluster.**

The lever is to stop `Channel.toRaw_ext_iff` from ever firing. `Model/Channels.lean` already carries all
twelve `@[circuit_norm]` name-based `<x>Channel_eq_<y>Channel_false` lemmas, whose whole purpose is to
decide these comparisons on the `name` field — and the full rewrite trace of this declaration contains
**zero** occurrences of any of them. They lose the match to `Channel.toRaw_ext_iff` every time. Making
them win (priority) is a single-point change in one file that should reach all 17 sites.

⚠ **This hypothesis reaches zero of the sites that carry a directive.** It was promoted twice as the
campaign's last big structural lever, on a conflation: the mechanism above was diagnosed on `AddChip`'s
`*_state_interactions_faithful_syntactic`, and then attributed to the four stamped `Faithful/` sites, which
are different declarations. Those four have no channel-comparison counters at all — no `Channel.Guarantees`,
no `nonempty_prop`, no `toRaw_ext_iff`. The 17-site `*_syntactic` cluster is real and the diagnosis of it
stands, but **no member of that cluster carries a directive**, so the payoff would be compile time, not the
ratchet. Worth doing on its own merits; do not expect it to remove a ceiling.

Tested and rejected here: `simp [-Channel.toRaw_ext_iff, …]` is a **no-op**, byte-identical counters. Lean
warns why — `` `Channel.toRaw_ext_iff` does not have the `[simp]` attribute ``. It arrives via
`circuit_norm`, and `simp [-X]` only removes from the default set. **`-X` cannot delete a lemma supplied
by a custom simp set.**

**(b) `Proofs/Chips/LoadByteChip/Formal.lean` `soundness`** — representative of the 18 Load/Store towers.
Textbook runaway whnf, the largest counters measured anywhere in this tree (the block quoted in §9.2):
`Nat.rec ↦ 450604`, `List.rec ↦ 327222`, `Vector.mapRange ↦ 323040`, `List.concat ↦ 238275`,
`Array.push ↦ 164019`, `Vector.push ↦ 150752`, `Eq.rec ↦ 59095`; reducibles
`Vector.toArray ↦ 373167` / `Array.toList ↦ 372110` / `List.toArray ↦ 191792`.

The chain is legible end to end: `varFromOffset ↦ 5155` → `ProvableStruct.componentsFromElements ↦ 20640`
/ `componentsToElements ↦ 17885` → `Vector.mapRange` → `Vector.push`/`Array.push` → `List.concat` →
`Nat.rec`, with `Vector ↔ Array ↔ List` conversion at every step. The row's `varFromOffset` structure is
being built cell-by-cell instead of being kept folded — exactly the value Clean's
`doc/performance-problems.md` says to make opaque, and the counters name it. `Extracted.AddrAddOperation.casesOn ↦ 5091`
and `Extracted.AddressOperation.addr_operation ↦ 795` corroborate §7's independent finding that
`AddressOperation`-composing chips are the whnf-heavy ones. For contrast, `MulChip.soundness` — same
tactic shape, floor (60k, 80k] — runs the same chain **30× smaller**.

### 9.7 The rewrite trace: when it adds anything

`set_option trace.Meta.Tactic.simp.rewrite true in` on the AddChip site produced **47,201 lines / 2.4 MB**
and doubled the file's elaboration time (5.4 s → 11.9 s). Ranking the rules by frequency reproduces the
`[simp] used theorems` census *exactly* and adds nothing:

```sh
grep -o "^\[Meta.Tactic.simp.rewrite\] [A-Za-z_.'₀-₉]*" out.txt \
  | sed 's/^.*rewrite\] //' | sort | uniq -c | sort -rn | head
```

So `diagnostics` supersedes it for "which lemmas". The trace earns its cost for exactly two questions
`diagnostics` cannot answer:

1. **"what did this rewrite actually do?"** — the `==>` pairs. Both `Nonempty (mult = -1)` and the
   `toRaw_ext_iff` record expansion quoted in §9.6 came from here; the counters alone would not have
   identified the channel-record tear-open.
2. **"did lemma X ever fire?"** — the trace is complete and unthresholded, while the `diagnostics` report
   silently drops everything under 20 (§9.1). The "zero occurrences of any `_false` lemma" finding is a
   trace result and could not have been read off the counters.

Run it only after `diagnostics` has named a suspect, and always through a filter.

### 9.8 Gotchas

- **A high `[reduction]` counter is not proof of a whnf problem.** The codegen control sat at 21950 with
  nothing wrong with its elaboration. Cross-check against the error's phase name before believing it.
- **Counters are cumulative over the declaration**, exactly like the heartbeat counter (§6): they do not
  attribute cost to one tactic line. The `[simp]` blocks *are* per-call and appear in source order, which
  is the one place you get intra-declaration attribution for free.
- **`diagnostics` on a `def` tells you about its elaboration, not its compilation.**
- **The error's phase name is a hint, not a diagnosis — and it misleads whenever the tactic is a search
  procedure.** `LtOperationUnsigned.at_most_one` reported `timeout at whnf` and was not a whnf runaway at
  all: max counter 12592, and the cost was five `tauto` calls closing satisfiable flag patterns. Read the
  phase name to *rank* hypotheses, then confirm against the counters. Where the phase name has held up it
  has been genuinely informative — `whnf` sites respond to fix pattern 7, `isDefEq` and `elaborator` sites
  do not — but a `tauto`/`grind`/`omega` closer voids the signal.
- **`#count_heartbeats` needs `set_option Elab.async false`.** Under 4.31's async elaboration it silently
  undercounts by roughly 4×. With the option set it is genuinely useful and gives *exact* totals where a
  ladder gives only a bracket (measured on `MulOperation.full_product`: 593455 → 214983 across a fix, and
  `low_half` 50601 → 26990). The older blanket note that it "lies because it runs with an unlimited budget"
  is true of the budget but was over-generalised into "unusable".
- **A declaration's total work can exceed the budget it passes at.** Lean elaborates the signature and the
  tactic body as separate tasks with separate budgets. `full_product` totals 214983 against a 200000 default
  it clears, because the body alone is the (120k, 150k] half. So a `#count_heartbeats` total above the
  declared ceiling is not evidence of a miscount — check which half you are looking at before concluding
  anything.
- Everything in §6 still applies — a stale `.olean` under `lake env lean`, and masking at rungs where a
  producer fails, both survive unchanged.

---

## 10. The anatomy of `circuit_proof_start`, and when to stop using it

The single most-cited cause in this tree is "the opener", and for a long time that was a black box. It
isn't. `circuit_proof_start` is a fixed, **untunable** 13-step pipeline
(`Clean/Utils/Tactics/CircuitProofStart.lean:117-163` in the upstream checkout). Knowing its shape tells you
which sites it can be blamed for and what to do about them.

**The core.** `circuit_proof_start_core` (`:167`) does exactly one thing: match the goal's head against the
eight supported `Soundness`/`Completeness` forms, `unfold` that constant, and `intro` the fixed binder list
(`i₀ env input_var input h_input h_assumptions h_holds`, or the completeness variant with `h_env`). No
`simp`, no `dsimp`, no unfolding of `main`.

**The full tactic** then adds ~15 further whole-context passes, of which two are the named hot spots:

- step 4, `dsimp +instances only [main] at *` — unfolds the entire circuit into every hypothesis **and** the
  goal. There are six `… at *` traversals in total.
- step 8's `simp +instances only [circuit_norm, h_input] at h_env` — the one-shot cast that Clean's own
  `doc/performance-problems.md:146-149` singles out as "the largest single cast".

**Every step is wrapped in `try … catch _ => pure ()`** — but ⚠ **this does NOT swallow budget errors, and
an earlier revision of this section said it did.** Measured 2026-08-02 with a two-line probe: both a
heartbeat timeout and a `maxRecDepth` overflow raised *inside* a `try` propagate out and fail the
declaration. Lean treats them as unrecoverable, so `try`/`first` cannot insulate a tactic from a ceiling.

Two consequences, both the opposite of what was written here before:

- A `circuit_proof_start` that runs out of budget **hard-fails at the step that exhausts it**, and reports
  that step's phase. It does not silently no-op the rest of the pipeline. The error location is meaningful.
- When laddering, a `try`-wrapped tactic is **not** protected. A `first | cheap | expensive` fallback will
  not rescue a proof from a depth ceiling — the depth error escapes the alternation. This bit us for real:
  `Faithful/DivRemChip.lean`'s `all_goals try exact vector_getElem_congr_idx …` still hard-failed at the
  `try` line, which is why that fix had to reorder the branches rather than add a fallback.

The prior claim was inferred from reading `try … catch _ => pure ()` in Clean's source, never tested — the
exact failure mode §12's meta-rule warns about, committed in this very document.

**The migration.** Clean's prescription for a heavy composition is to stop using the full tactic:
`circuit_proof_start_core`, then reproduce by hand only the steps the body actually needs —
`dsimp only [main, circuit_norm] at h_env` (definitional, castless), project components with `.1`/`.2`,
`clear h_env`, and `simp only [circuit_norm, h_input, <child circuits>]` on each small component separately.

We use the plain form **130×** and the binder-only `_core` form **11×**. The `_core` sites are not
incidental: they are `ShiftLeftChip`, `ShiftRightChip`, `DivRemChip` and `BranchChip` — and none of those
declarations carries a ceiling. `ShiftRightChip/Formal.lean:93-95` records the outcome in one line: *"The
former 4M ceiling was ~100× over: the four per-conjunct proofs carry the cost in their own modules, so this
assembly clears ≤40000 against the plain default."*

The two levers compose and are separable:

1. **Declaration splitting** resets the heartbeat counter (it is per-declaration) and gives each piece its
   own kernel check. This is what the per-variant `Soundness/<Op>.lean` files buy.
2. **`_core` + hand-sequenced casts** avoids the `at *` traversals entirely, so the *assembly* theorem stays
   cheap enough to delegate with bare `exact`s.

Local variants live in `SP1Clean/Proofs/CircuitProofStart.lean`, which already re-orders the pipeline for
the Shift chips (`circuit_proof_start_early_struct` moves `provable_struct_simp` **before** `main`
expansion). That file is the right home for further variants — prefer a named, documented variant over a
bespoke tactic block copied between chips.

### The `elaborated`-field correlate

Clean's `AGENTS.md:139` states it plainly: passing `elaborated` as an explicit field is *"very important"*
for performance, "otherwise `soundness` has to elaborate with metavariables since `elaborate` is not filled
in at that time". Chips that write `instance elaborated … := by elaborate_circuit` leave the metadata to be
recomputed; chips that pin `output` / `localLength` / `channelsWithGuarantees` / `channelsLawful` make it
literal.

At the point this was measured, **exactly two chips in the tree let the default tactic fire — and they were
exactly the two sites where ablation attributed 100% of the cost to circuit elaboration.**

❌ **Tested on JalrChip and refuted.** Pinning `output` / `localLength` / `channelsWithGuarantees` and
forwarding `subcircuitsConsistent` / `channelsLawful` from a private `derivedElaborated` changed the measured
totals from 2,967,014 / 2,988,116 to 2,966,790 / 2,987,857 — a **0.008% delta, i.e. noise** — for a change to
what the instance definitionally *is*. It was reverted. Keep following the upstream rule when writing a new
chip, because it costs nothing there; but **it is not a remediation lever for an existing ceiling**, and the
n=2 correlation above was coincidence. This is the third structural hypothesis this campaign promoted on
correlation and then lost to measurement (see also the `channelsWithGuarantees_eq` rfl-lemma theory and the
`*_eq_*Channel_false` priority theory). The pattern is consistent enough to be a rule: **a correlate found by
reading code predicts nothing until a ladder confirms it.**

### What the Jalr cost actually was

Per-step `#count_heartbeats` (under `Elab.async false`) put **98%** of `soundness`'s 2.97M budget units in a
single step — `provable_struct_simp`, at 2,900,887,852 raw heartbeats. Both of the hot spots named in
upstream's own doc were irrelevant here: `dsimp only [main] at *` cost ≈199 budget units, and the one-shot
`simp … at h_env` was a **no-op** (soundness has no `h_env`).

`provable_struct_simp` is expensive *only because of where it sits in the pipeline*: it runs its `simp … at *`
fixpoint **after** `dsimp only [main] at *` has expanded the five-subcircuit tower into `h_holds` and the
goal. Run against the still-folded context, the same fixpoint costs ≈2.2k budget units — a **1000× drop** —
and destructures identically, because destructuring is driven by `h_input`/`h_assumptions`, not `h_holds`.

That is exactly the reordering `SP1Clean/Proofs/CircuitProofStart.lean`'s `circuit_proof_start_early_struct`
already performs, and it is very likely why the Shift chips have never needed a ceiling on these proofs.
The one thing the hoist gives up: `provable_struct_simp`'s struct-eval set is deliberately **not** a
`circuit_norm` subset (its `getElem` lemmas loop against `circuit_norm`'s element-map spelling), so it no
longer reaches the unfolded `h_holds`. Restore it with a **scoped** `simp only [<structEvalSimpLemmas>] at
h_holds ⊢` — adding those lemmas to a `circuit_norm` call instead loops, as Clean's own comment warns.

Measured result on JalrChip: `soundness` 2,967,014 → 65,581 (45×), `completeness` 2,988,116 → 24,475 (122×),
file 110.3s → 6.1s, both 8M ceilings deleted, proof bodies byte-identical.

**Read the pipeline before blaming a step.** The cost was not in any step's own work; it was in the *order*
of two steps, which no counter and no phase name reports.

---

## 11. The cost can be in a `have`'s **type**, not its proof — ablate both halves separately

`BitwiseChip.completeness` carried a 5M ceiling that its own comment blamed on a `have key : ∀ k : Fin 8, …`
witness-pin block. Replacing the block with `sorry` collapsed the floor from (700000, 1000000] to
(20000, 40000], confirming the attribution at ~96% of the budget. But a **second, finer ablation** — sorry
the proof body while keeping the written-out type — did not move the floor at all.

**The entire cost was elaborating the statement.** Writing

```lean
have key : ∀ k : Fin 8, env.get (i₀ + 3 + 4 + 4 + (k : ℕ)) =
  (BitwiseU16Operation.populate b c opcode).bitwise_operation.result[(k : ℕ)] := …
```

forces the elaborator to `whnf` through `populate`'s `let`-bundle, `decompBytes`, and the eight-fold `byteOp`
result vector — once per concrete `k`. The tell that it is the *projection* and not the term: a sibling
`have` in the same proof carries `toElements (populate …)` in its type and is cheap. It is
`.field[getElem]` on the populate result that triggers the unfold.

The fix is Clean's fix pattern 1 in its strict form: a `private theorem` over an **opaque** column struct
`s`, so the projection is inert, applied at the use site with **no written-out type** so instantiation only
pattern-matches. Eight concrete-index defeq checks collapse to one at an opaque index. Result: 900904 →
40145 heartbeats (22×), file 14.2s → 6.3s, directive deleted.

**Generalisable procedure.** When ablating a `have` block, ablate in two steps — first the whole block, then
the proof body alone with the type retained. If the second ablation does not move the bracket, no amount of
work on the proof will help, and the fix has to change how the statement is *spelled*. This distinction is
invisible to the phase name and to the counters, both of which just say "whnf".

---

## 12. The one rule that carried every fix: extract over **opaque** arguments

Five sites were remediated in the P4 follow-up by five superficially different edits. They are the same
edit. In each case a value that should have stayed abstract was reaching a step that had to unfold it, and
the fix was to put an opaque variable between the two — never to make the expensive step cheaper.

| site | where the cost actually was | the fix |
|---|---|---|
| `Faithful/AluX0` | the **context**, not the goal — the goal was already value-level after the `rw` block; `hReaderList` still mentioned `(…main …).operations offset`, and `tauto` reverts and normalises everything | `clear` the three spent circuit-valued hypotheses. Floor moved 25× |
| `Faithful/BitwiseChip` | the **spelling of a definition** — a struct *literal* forced `toElements` through `componentsToElements` | build it with `fromElements` instead, so `toElements_fromElements` fires in one step |
| `BitwiseChip.completeness` | a `have`'s **type**, not its proof — `(populate …).field[k]` in a statement forces whnf through a `let`-bundle, once per concrete `k` | restate over an opaque struct so the projection is inert; apply with no written-out type. 22× |
| `JalrChip` | the **order** of two pipeline steps — `provable_struct_simp` ran after `main` had been unfolded into `h_holds` | hoist it above the unfold, so the fixpoint sees the folded context. 1000× on that step |
| `DivRemChip/Evidence/Signed*` | 24 `rw [gate] at e; linear_combination e` pairs, each renormalising a ~115-hypothesis context | one 3-line opaque-argument lemma applied as a **term**. Beat both planned hoists combined |

**The corollary that keeps being learned the expensive way:** extracting a block *within* the same proof
buys nothing. The DivRem family had a recorded negative result — "extracting the componentwise `Vector.ext`
sweep into its own lemma moved nothing" — which was used for months as evidence that the site was
irreducible. It was extracted into a `have` inside the branch, so it kept the whole branch context. The same
extraction to a lemma over opaque arguments is what paid.

So when an extraction "doesn't help", check *what the extracted thing can still see* before concluding the
cost is intrinsic.

### And the meta-rule: a correlate found by reading code predicts nothing

Four structural hypotheses were promoted during this campaign on the strength of code-reading, and all four
were corrected or refuted by measurement:

1. **Missing `channelsWithGuarantees_eq` rfl-lemmas force tower-unfolding.** Refuted — those proofs carry no
   ceilings at all, and `MulChip` has the rfl-lemma *and* the ceiling.
2. **`*_eq_*Channel_false` losing the match to `Channel.toRaw_ext_iff`.** Real mechanism, correctly
   diagnosed — but it reaches **zero** of the sites that carry a ceiling. Promoted twice before that was
   checked.
3. **The `elaborated`-field correlate** (n=2, and upstream's own documented rule). Tested on Jalr:
   **0.008% delta**, noise.
4. **The 122 byte-identical duplicated lines in the DivRem signed pair** (verified by `diff`, so the
   duplication was certainly real). Removing them got to 224836 against a 200000 target — not a fix. The
   lever that closed it was a three-line lemma nobody had noticed.

Note that #2 and #4 were *correct diagnoses of real phenomena* that simply were not the cost. That is the
trap: a mechanism can be genuine, verifiable, and irrelevant. **Ladder before you believe it, including —
especially — when you found it yourself.**
