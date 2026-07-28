# Cleanup profile — the house rules for `/cleanup` and `/cleanup-all` in this repo

**Read this before the `mathlib-quality` plugin's own references. Where they conflict, this file
wins.** The plugin (`commands/cleanup.md`, `references/golfing-rules.md`,
`references/cleanup-gates.md`) is written for **mathlib**. This repo is a Clean-native formal
verification of SP1's RISC-V chips with different — and in several places *opposite* — invariants.
Applying the stock workflow unmodified breaks the build and corrupts the audit surface.

Companion reading, in order: Clean's `doc/performance-problems.md` and `doc/proving-guide.md`
(upstream authority), then `docs/agents/proof-patterns.md` (this repo's landmines and the
"Golf & cleanup discipline" section), then `AGENTS.md`.

---

## 1. Why the stock rules are overridden

| Stock rule | What it does here |
|---|---|
| Phase 3.5 / rule 3.7 — delete every `set_option maxHeartbeats`, "no exceptions" | **638** exist in `SP1Clean/`, ratcheted by `scripts/check_heartbeats.sh`. Deleting them fails the build and the guard. |
| Rule 1.15 — unsqueeze terminal `simp only` → bare `simp` | Exact inverse of this repo's `maxHeartbeats` fold recipe; there is a tested KEEP-set (§5). |
| Item 12 (hard gate) — split `∧` statements into `foo_left`/`foo_right` | As stock, it *deletes* a theorem and mints new names. `scripts/gen_axiom_probe.py` resolves its probe targets by **regex over source text**. Adopted here only in additive form (§4). |
| Item 11 — make single-file declarations `private` | `gen_axiom_probe.py` **skips `private` decls** → silently shrinks the axiom census. |
| Item 19 (hard gate) — rewrite `≥`→`≤` in statements and hypotheses | Changes statement text. `Faithful/*` are *syntactic* faithfulness anchors. |
| Item 5 (hard gate) — forced renames, "existing convention preserved is NOT acceptable" | Breaks `scripts/nolints.json` (FQN-keyed), the `gen_axiom_probe.py` regexes, and `scripts/check_report_citations.sh` (15 hard-coded file+declaration pairs). |
| Phase 5a — delete "wrapper" lemmas mathlib provides | Targets this repo's deliberate one-line namespace bridges — "shared substrate … not migration debt" (AGENTS.md). |
| Item 10 — strip docstrings from private/aux declarations | Destroys the institutional memory the landmine notes carry. |
| A.1 copyright header, `lake exe cache get`, `lake exe runLinter` | Not this project's conventions or commands (§7). |

---

## 2. Hard prohibitions

A violation is a defect: revert and re-dispatch.

1. **Never change an existing declaration's statement.** No `≥`→`≤` rewrite (kills item 19); no
   restating a conjunction; no inline hypothesis generalisation (kills step 2.6e — generalisation
   candidates are *reported* to `DEFERRED.md`, never applied). Adding a *new* split lemma is
   permitted, see §4.
2. **Never change a declaration's name or visibility.** Renames are queued only (§6); `private` is
   never added or removed.
3. **Never delete a declaration.** This kills Phase 5a items 1–3 (mathlib replacement, junk-def
   inlining, single-use `∃`-lemma inlining). *Adding* declarations is permitted — see §4a.
4. **Never touch** `SP1Clean/Extracted/**`, `SP1CleanTest/**/Vectors/**`, `*TraceVectors.lean`,
   `scripts/axiom_probe.lean`, or `SP1Clean.lean` (the root import index). No file moves.
4b. **Never change a `def` / `abbrev` *data* body.** Statements are already frozen by §2.1, but a
   `def`'s body is part of its meaning: importers see it through definitional unfolding, so editing
   one changes downstream elaboration in a way a sibling worker's cached olean cannot see. A theorem
   or lemma *proof* body is invisible to importers and is the campaign's actual working surface.

   > **Exception — Prop-valued fields are fair game.** A `Prop`-valued field of a `def`/`instance`
   > (`channelsLawful`, `localLength_eq`, `subcircuitsConsistent`, `output_eq`, and every
   > `ElaboratedCircuit` obligation) is a *proof*, and Lean's proof irrelevance is definitional: any
   > two proofs of the same `Prop` are already defeq, so no importer can observe which one you wrote.
   > These are exactly as invisible as a theorem body, and they are golfable. Only **data** fields and
   > the declaration's type are frozen. This matters: `Native/Readers/` alone carries ~90 lines of
   > near-verbatim `channelsLawful` / `requirementsChannelsLawful` boilerplate, and
   > `proof-patterns.md` says such obligations should almost never have a hand-written proof at all —
   > the goal is to let Clean's default tactic close them.
   This rule is what makes it safe to edit files at different topological depths in one gate group —
   with statements frozen, attributes suspended (§10), and `def` bodies untouched, there is no
   channel by which one worker's edit can invalidate another's LSP verdict.

   > **But separate the two schedules.** Correctness permits a mixed-depth *gate group*; workability
   > does not permit a mixed-depth *editing round*. While any worker holds a shallow file dirty on
   > disk, every file importing it answers only `Imports are out of date and must be rebuilt`, and
   > that lockout does **not** self-clear (`lean_goal` does not help; the olean's recorded source hash
   > genuinely differs — diagnose by comparing `<Mod>.trace` against `<Mod>.trace.nobuild`). A whole
   > W1 batch lost in-place verification this way. So: **one editing round = one depth level** (a true
   > antichain, no import edges by construction), but **one gate = many rounds**. Rounds are free;
   > gate builds are ~10 minutes.
5. **Never introduce** `native_decide` into `SP1Clean/`, or `skipKernelTC` anywhere.
6. **Never unsqueeze `simp only` → `simp`.** The permitted direction is `simp` → `simp only`, and
   only outside the KEEP-set (§5).
7. **Never add mathlib copyright/authors headers.** **Never delete `/-! ## … -/` subsection
   dividers** — this repo uses them structurally inside large files.
8. **`Faithful/**` and `Native/Operations/*/RawSpec.lean` are conservative-only.** Permitted: drop
   `by exact`, drop a dead `let`, `from by` → `by`. Never restructure proof terms or statement
   forms — they are *syntactic* faithfulness anchors.
9. **Never raise a `maxHeartbeats` ceiling.** The performance track (§8) only lowers or removes.
10. **Never create a top-level `SP1Clean/*.lean` module.** The eight style linters live on the
    *pillar* libs in `lakefile.toml`; the umbrella `SP1Clean` lib carries no `moreLeanArgs`, so a
    module outside a pillar subdirectory would silently escape linting.

---

## 3. Comment discipline (stock item 9, as adopted)

**Strip** narrative play-by-play: `-- now we rewrite`, `-- apply the lemma`, `-- case 2`,
`-- unfold the definition`.

**Keep**, always:

- anything documenting a **landmine or invariant** — the `2^64` and `id (ZMod p)` notes on
  Shift/DivRem/Mul, the `omit [Fact (2 ^ 17 < p)]` rationale, kernel deep-recursion warnings;
- anything explaining **why** a proof is shaped the way it is — a roadmap over a dense body, or a
  note that a `have` is load-bearing for a downstream `omega`;
- module docstrings, and docstrings on any declaration regardless of visibility.

Precedent: a blanket comment-strip on `Proofs/Chips/ShiftLeftChip/Soundness/Sll.lean` was
**reverted** for destroying exactly this. The rule is **strip narration, keep rationale** — on a
dense proof, when in doubt, keep it.

---

## 4. Additive conjunction splits (stock item 12, as adopted)

Where a declaration's conclusion is a conjunction, **add** `foo_left` / `foo_right` (or
better-named projections) proved from the original, and **leave `foo` byte-identical**. Call sites
may migrate to the projections; none are required to. Nothing is deleted, no statement changes,
and the original name stays resolvable for `check_report_citations.sh` and the probe globs.

## 4a. Extracted helpers are permitted

Adding a **new** declaration is allowed in exactly two shapes. Nothing existing may change either way.

1. **Additive conjunction split** (§4 above).
2. **A helper extracted from existing proof bodies** — a shared preamble repeated across sibling
   lemmas, or the kernel-safe dedup lemma of §9. This is not a loophole: it is the repo's own
   documented dominant structural win, and `proof-patterns.md` explicitly prescribes extracting a
   repeated `have` block "as a lemma **over loose variables**" applied symbolically.

Rules for a new helper:

- **Prefer `private`** when it is used only within its own file. (Prohibition §2.2 forbids changing
  the visibility of an *existing* declaration; a new one may be born `private`.) This keeps
  `gen_axiom_probe.py` churn at zero, since it skips `private` declarations. A **public** helper is
  also fine when it matches the sibling files' existing convention — the safety properties that
  actually matter are (a) it does not match a probe glob, and (b) its namespace does not collide with
  a same-named declaration elsewhere. `ShiftRightMath.inner_val`/`inner_hi_val` are public precisely
  because the pre-existing `ShiftLeftCore` pair is; different namespaces, no collision, no glob.
- **Do not name it to match a probe glob.** Avoid `*faithful*`, `soundness`, `completeness`,
  `circuit`, `kind`, `correct_*`, `*reaches_sail*`, and the specific names listed in
  `scripts/gen_axiom_probe.py`. An `_aux`-style name is fine.
- In `FormalModel/Contracts/DivRem.lean` and `Proofs/Chips/DivRemChip/Cases.lean` **every** named
  theorem is a probe target, so a non-`private` addition there changes the probe count. Permitted,
  but say so in your report so the count is regenerated and explained.
- The helper's conclusion must match the original `have`'s type **character-for-character** where it
  is a `rw` target (§9) — but see the scope refinement there; the constraint is narrower than it
  first appears.

> **Probe-count consequence.** `gen_axiom_probe.py` matches *every* named theorem in
> `FormalModel/Contracts/DivRem.lean` and `Proofs/Chips/DivRemChip/Cases.lean`. New lemmas in those
> two files enlarge the probe set. That is acceptable — `run_audit.sh` checks internal consistency
> (parsed entries == `#print axioms` lines), not a fixed count — but the probe must be regenerated
> and `docs/snapshots/axiom-ledger.md` updated at the end of the campaign, with the delta explained.

---

## 5. The `simp` → `simp only` KEEP-set

Tested during the 2026-06 campaign, zero speedup — **do not sweep these**:

```
SP1Clean/Proofs/Operations/DivRemOperation/Core.lean
SP1Clean/Native/Operations/DivRemOperation/OwnAsserts.lean
SP1Clean/Native/Operations/MulOperation/RawSpec.lean
SP1Clean/Proofs/Chips/MulChip/Formal.lean
SP1Clean/Proofs/Operations/MulOperation/Formal.lean
SP1Clean/Proofs/Chips/ShiftLeftChip/Core.lean      (the nlinarith farm)
SP1Clean/Proofs/Chips/ShiftRightChip/Core.lean     (the nlinarith farm)
SP1Clean/Proofs/Chips/ShiftLeftChip/Soundness/{Sll,Sllw}.lean
SP1Clean/Proofs/Chips/ShiftRightChip/Soundness/{Sra,Sraw,Srl,Srlw}.lean
SP1Clean/Math/Word.lean                             (toBitVec64)
SP1Clean/Proofs/Sail/Advance.lean
```

`Faithful/**` is anchor-safe but **not mechanically safe** — per-theorem only, and the payoff is
low. `Extracted/**` is out of scope; its only lever is `update_extracted.py`.

---

## 6. Load-bearing constructs that look dead

Verify with `lean_goal`, or a build, before removing:

- `have hp : 2 ^ 17 < p := Fact.out` and `have : 131072 < p` — feed a downstream `omega` that needs
  the magnitude. A grep shows one occurrence (its own line), yet `omega` consumes it implicitly.
- `haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩` — supplies an instance to
  later `ZMod.val`/`omega` steps. There is deliberately **no** global `NeZero p` instance: a
  `Fact (2 ^ 17 < p)`-derived one would make the pervasive `omit [Fact (2 ^ 17 < p)] in` clauses
  illegal (`Model/ByteTable.lean:84`). Do not add one — it is an owner decision, not a drive-by.

> **The derivation source decides — do not treat all `Fact`/`NeZero` locals as load-bearing.** This
> rule was originally written too broadly and was telling workers to keep dead code. Three measured
> cases:
>
> | local | derived from | verdict |
> |---|---|---|
> | `NeZero p` | `Fact (2 ^ 17 < p)` | **keep** — no global exists, on purpose (above) |
> | `NeZero p` | `Fact p.Prime` (`⟨(Fact.out (p := p.Prime)).ne_zero⟩`) | **dead, remove** — synthesizable |
> | `Fact (1 < p)` | `Fact p.Prime` | **dead, remove** — synthesizable |
>
> Anything synthesizable from `Fact p.Prime` is already in scope and the local shadows nothing. Only
> the magnitude-derived (`2 ^ 17`) form is load-bearing. Likewise `Math/Word.lean` declares
> `instFact_2_17_of_2_24` and `instFact_2_24_of_2_25`, so an in-proof `have` re-deriving
> `Fact (2 ^ 17 < p)` under a stronger hypothesis is also dead — four such copies were deleted
> outright during the `sixteen_lt` hoist. **Verify by deletion + re-elaboration, never by grep.**

- A `change` that only restates an `abbrev` is free to delete when the closer is a term rather than a
  tactic that needed the syntactic form. `MicroTime.chainState_succ_front` went from 8 lines to 2
  this way (three pure-defeq `change`s dropped, body now `exact congrArg (·.bind Machine.stepOnce) ih`).
- `set_option linter.unusedSectionVars false in` before the `circuit_norm` `rfl`-lemmas.

---

## 7. Commands

| Plugin says | Use here |
|---|---|
| `lake exe cache get` | *(nothing — do not run it)* |
| `lake build` | `lake build SP1Clean`. **Pass = exit 0 AND zero `error:` AND zero `warning:` AND zero `info:` notes.** |
| `lake exe runLinter` | `lake lint` (driver `scripts/sp1Lint.lean`; needs a completed build first) |
| — | `lake test` — the `SP1CleanTest` conformance anchors, the only `native_decide` |
| — | `scripts/run_audit.sh` — zero proof deferrals + the axiom census |
| — | `scripts/check_no_native_decide.sh`, `scripts/check_no_skipkerneltc.sh`, `scripts/check_heartbeats.sh` |

Two traps:

- **`lake env lean <file>` is not a gate.** It exits 0 even on a Lean stack overflow, and it skips
  the package's lean args, so it passes where `lake build` fails. It is sound only as a
  *falsifier*: a reported error is real, but a clean run certifies nothing.
- **The `ring` `info:` leak.** On some goals `ring` runs its `ring1` pass, fails, emits
  `Try this: ring_nf`, then closes via the `ring_nf` fallback — the proof passes but the build is
  no longer clean. Close those with `simp` (the `is_real` binary gate and `interval_cases` carry
  goals), `ring_nf`, or the explicit lemma.

---

## 8. Performance track — investigate, don't ratchet

638 hand-written `maxHeartbeats` lines on a ladder already in use (200k → 128M), distributed
`Faithful` 305, `Proofs` 232, `Native` 54, `Soundness` 43, `Model` 3, `Math` 1.

**The lead worth chasing:** `Faithful/` holds 48% of the ceilings but only ~115s of elaboration
across 50 files, and a median downstream closure of 2. Many of those 8M ceilings are vestigial —
cheap and safe to lower.

Per site:

1. **Diagnose before touching the number.** Clean's `doc/performance-problems.md` is the authority:
   the whnf-into-expensive-values doctrine (make dangerous values opaque; cross spellings by
   syntactic rewriting, not unification), the nine fix patterns, the kernel-size-cliff completeness
   recipe (`circuit_proof_start_core`), and "keep hypothesis types folded". Then
   `proof-patterns.md` § "maxHeartbeats: the fold recipe + no-bump discipline". **`#count_heartbeats`
   lies** — measure from the build log.
> **Never write the literal string `set_option maxHeartbeats` inside a comment or docstring.**
> `scripts/check_heartbeats.sh` counts sites with a raw `grep -rc "set_option maxHeartbeats"` — it
> does not parse Lean, so a comment mentioning the option scores as a live ceiling and silently
> corrupts the ratchet. When recording a measured ladder (which you should), phrase it without the
> literal: "the former 8M ceiling was ~170× over". Two workers hit this; one caught it, one did not.
> A pre-existing instance at `Proofs/Sail/Advance.lean:2325` means the 853 baseline has always
> counted at least one phantom.

### Cause classes, most valuable first

**1. Search duplication in a `first | … | …` ladder.** The largest single win of the campaign:
`ShiftRightChip/Dispatch.lean` went **1591 → 861 lines (−730)** and shed all 12 of its ceilings.
Each lemma did `rcases` into 16 goals `<;> first | exact close 0 65536 … | exact close 1 32768 … |`
… `| 15 …`. `first` restarts the ladder for every goal, and the matching alternative sits at
`bitreverse4(goal index)`, so ~8 alternatives per goal were elaborated *all the way through their
`rw […]; push_cast; ring1` side conditions* and then discarded — ≈128 wasted `ring1` per lemma,
≈1500 across the file. That was the entire ceiling. The fix is inside the proof bodies: `rcases …
with rfl | rfl` (substituting makes the side-condition blocks uniform across all 16 cases), hoist the
fixed arguments into one local `have key := fun …` instead of repeating them 16×, and replace the
`first` ladder with **ordered bullets**, one per goal. Whenever you see `<;> first |` over many goals,
suspect this before anything else.

> **Sorting the ladder does not help — only bullets do.** `ShiftRightChip/Core.lean`'s `cb_aux`
> ladder was *already* in goal order (0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15 — which independently
> confirms the bit-reversal permutation) and still paid the full 120 wasted alternatives, because
> `first` restarts from the top for every goal regardless of ordering. Do not try the cheap fix.
>
> **A `have key := fun … =>` binding has no expected type**, so named arguments like `(cb4 := cb4)`
> become mandatory where `exact` did not need them. Giving `key` an explicit `∀` type avoids the trap
> entirely, and is the better habit.

**Reading a timeout's location.** A `(deterministic) timeout at whnf` is reported at **column 1 of a
signature**, which is not necessarily the declaration you think failed. `ShiftRightChip/Core.lean`'s
binding site was recorded once as `sra_close_su16_3_case` and is actually `srlw_within_byte_shift`;
pinning that single lemma leaves ~42 of the file's 43 declarations clean at the plain default. Always
confirm which declaration owns the reported line before concluding a whole file needs a budget — and
prefer a **scoped `set_option … in` on the one lemma** over a file-scoped ceiling.

Two refinements, both measured:

- **At very low rungs the error is reported at the shared `variable` line**, which is useless for
  attribution. Separate ownership by laddering the sites at *different* rungs until each failure
  lands inside a declaration body.
- **Re-ladder after fixing a cause — the owner moves.** `SailWrap.lean`'s ceiling was owned by two
  lemmas before its `acLt` fix and by a completely different third lemma afterwards. A floor measured
  before the fix tells you nothing about the file after it.

**1b. Permutative-`simp` term ordering over a dependent cast.** A **permutative** `@[simp]` lemma
(`a ∘ b = b ∘ a` shaped — here `Std.ExtDHashMap.insert_insert_comm` in `Math/Misc.lean`) makes `simp`
decide the rewrite direction with `Lean.Meta.acLt`, whose cost scales with the size of the compared
arguments. When one argument is a `▸` cast whose proof is a wide `match` (`reg_idx_must_64 idx ▸ val`,
a 31-arm match), that comparison dominates everything. It presents as an opaque
`(deterministic) timeout at «Lean.Meta.acLt»` **with no hint of which simp lemma is responsible** —
the tactic looks innocent. Diagnostic: find a sibling lemma doing the same rewrite *without* the
cast; if it passes at the default, the cast is the cost. Fix inside the proof body: `unfold`, then
`generalize` the cast away, then run the original tactic. This was `Model/SailWrap.lean`'s entire
ceiling, and the lemma is tagged globally, so the hazard reaches every `simp` over that head symbol.

**2. A duplicated `.val`-bridge fact — a raised ceiling as proxy, not term-intrinsic cost.** Look for the repeated `have` before you touch the
number. `ShiftLeftChip/Core.lean` carried 16 ceilings; its SLLW half was re-deriving `mul_v_val` /
`hi_lo_val` / `mul_v_add_val` by hand while the SLL half *in the same file* already called them, and
two residual `nlinarith` calls were re-proving `< 65536` limb bounds that
`Math/ShiftBounds.lo_hi_lt` already proves once over loose variables. Fixing the
duplication dropped 26 `nlinarith` to 3 and made **all 16 ceilings removable**. That is the
difference between raising a budget and driving the proof to closure.

**Lead with the sibling-comparison screen — it is nearly free and it has been predictive.** Before
laddering anything, find a declaration in the same file (or its mirror file) that does *the same kind
of work* and carries **no** ceiling. If one exists, the ceiling is almost certainly vestigial, and the
ladder is then only confirming what the comparison already told you. Worked cases: `SailWrap`'s
`Sail.writeReg_writeReg_comm` — same tactic, same hashmap comm step, no dependent cast — passes at the
default and pinpointed the `acLt` cause; `Faithful/CPUState.lean`'s third interaction anchor does
strictly *more* work than the two ceilinged ones (same `hbk`, same binding hypotheses, plus a 4-entry
`List.Perm` instead of a filtered `=`) and has never carried a ceiling — which correctly predicted
both floors at ≤2500 against a declared 1M.

**Declared magnitudes are uninformative.** Across ~100 measured sites the declared value has never
correlated with the true floor: 16M families flooring at ≤40k, 8M at ≤20k, 1M at ≤1500, and the
highest-floor file in a batch carrying the same number as the lowest. Treat the number as evidence of
nothing but a copy-paste.

**Batch several sites per file per pass.** Separating ownership requires laddering sites at *distinct*
rungs, so two sites cost ~7 LSP round-trips if done serially. Plan the rung schedule for all of a
file's sites up front.

2. **Classify the cause**, and record any cause not already documented — new ones are expected.
   Known classes: unfolded expensive value (the `circuit_output_eq` fold), unfolded hypothesis type,
   over-broad simp set, missing normalization lemma, metavariable normalization at a decoded row,
   a `rfl`-check cliff.
3. **Fix the cause, then lower the ceiling.** Try removal first, then the next lower rung. Keep the
   lowest rung that compiles **with no elaboration-time regression**.

**Two methodology rules, both learned the hard way in this campaign — a ladder search that skips
either one produces wrong answers:**

- **Always run a control at `maxHeartbeats 1`** and confirm it produces real timeout errors. Without
  it, a "pass" at a low rung may be a cached LSP result rather than a genuine re-elaboration, and you
  will report a floor that was never tested.
- **Watch for *masking* sites.** If a producer (`def`) times out, every dependent theorem cascades
  with `Unknown identifier …` / `Function expected at …` instead of its own timeout — so the
  dependents' true floors are invisible and they read as "binding" when they may be hundreds of times
  over. Pin the producer high, ladder the dependents separately, then ladder the producer.
  `DivRemOperation/OwnAsserts.lean` is the worked case: `def ownAsserts` masked twelve
  `*_mem_ownAsserts` theorems that all turned out to have floors ≤20k against a declared 8M.
  A naive ladder **under-removes** here; it does not produce unsound results, just timid ones.
4. **Budget.** Full ladder search only where the module elaborates <10s in isolation (79% of modules
   are <3s). On the heavies, change a ceiling only when the golf pass already altered that proof,
   and always in a solo batch.

**`simp only` root-cause pass** (replacing the dropped rule 1.15): where a `simp only` carries a
long explicit lemma list or sits next to a raised ceiling, classify it — over-broad simp set / a
lemma that should be `@[simp]` or `@[circuit_norm]` / a missing normalization lemma / a fold that
should be a `rfl`-helper — and fix the cause when it is cheap and local. This repo's own precedent
is that the right lever is usually a missing `@[circuit_norm]` `rfl`-lemma (`channelsWith*_eq`,
`localLength_eq`, `circuit_output_eq`), not a bigger ceiling. Non-local findings go to
`DEFERRED.md`.

Findings are logged to `docs/agents/perf-findings.md`.

---

## 9. Permitted golf

Plugin rules **1.1–1.14, 1.16–1.18, 1.20; 2.3, 2.5, 2.6, 2.9, 2.11, 2.12, 2.15; 3.1, 3.4, 3.6**,
subject to §2.

**Opt-in only, never applied by default:** `grind` (2.1/2.2) — a whnf-into-expensive-values risk on
circuit goals; `lia` (2.7/3.3) — do not mass-rewrite `omega` on a 4.31 toolchain without a spot
check; `push_neg` → `push Not` (1.19) — not adopted.

**The single most common finding in this campaign: the lemma already exists, it just is not cited.**
This repo has good shared substrate — `Math/ShiftBounds.lean` (`lo_hi_lt`, `hi_lo_lt`,
`factor_le`), `Math/Word.lean`'s `val_N_zmod_p` / `val_N_ne_zero` families, `Math/Gate.lean`'s
`bool_val_le`, `Math/EvalVec.lean`'s `vec4_eval` — and proofs all over the tree re-derive those exact
facts by hand instead. Measured instances: a 20-line `key` in `ShiftLeftChip/Populate.lean` that was
literally `ShiftBounds.hi_lo_lt`; `two_ne_zero_one` (13 lines) and `h64ne` (6 lines) hand-rolling
`val_2_zmod_p` / `val_64_zmod_p`; `hval2` being literally `val_2_zmod_p`; four hand-rolled copies of
mathlib's own `Nat.cast_ofNat` sitting next to a sibling file that used the real one.

**So before golfing a `have`, search for it.** `lean_local_search` on the statement shape, and grep
the `Math/` and `ShiftBounds` families. This is cheaper than any tactic golf and it is where the
lines actually are. Adding the import may be free — check whether the blanket `Mathlib.Tactic` it
drags in is *already* in the module's closure and its consumers'.

> **Cashing a lever does not have to mean rewriting with it.** Measured on `AddOperation.soundness`:
> `rw [Nat.cast_ofNat]` (forward, against a goal) is safe, but `rw [← Nat.cast_ofNat]` rewrites the
> `6` opcode column, and pinning it as `rw [← Nat.cast_ofNat (n := 16)]` does **not** rescue it — it
> targets the right column but yields `↑(OfNat.ofNat 16)`, a *different spelling* from `↑16`, which is
> a live char-for-char hazard against the downstream `byteRowSpec_range` match.
>
> The safe way to retire a hand-rolled copy in the `←` direction is to **keep the local `have` and
> prove it by the real lemma** — `have c16 … := Nat.cast_ofNat` instead of `:= by norm_cast`. The
> duplication is gone, every downstream `rw [← c16]` keeps its exact spelling, and nothing moves. Use
> the forward idiom only where the *goal* carries the cast; substituting it at 4–6 hypothesis call
> sites per file costs more lines than the `have` it deletes.

This repo's own high-yield moves:

- **Eval-map factoring** — the dominant structural win. Chip/op `Formal.lean` proofs repeat a
  per-limb `have eX : Expression.eval env input_var_X[i] = input_X[i] := by rw [← hX]; simp
  [Vector.getElem_map]`, one per limb. Collapse them into one quantified helper
  `have eX : ∀ i (hi : i < n), … := by intro i hi; rw [← hX]; simp [Vector.getElem_map]`, then call
  `eX i (by omega)` at each site. ~12–25% per file on Load/Store/op `Formal.lean`. Use the existing
  `SP1Clean.vec4_eval` (`SP1Clean/Math/EvalVec.lean:18`) for the length-4 `#v` → `Vector.map` fold.
  Do **not** hoist a global per-limb `eX` lemma — investigated and rejected (saves ~1 line/helper
  while re-churning ~36 clean files at form-variation risk).
- **Kernel-safe dedup** on the bit-shift / DivRem cores: a byte-identical `have` block repeated
  across sibling lemmas may be factored **iff** it is pure `ZMod.val`/`Nat` arithmetic with no
  `2^64`/`BitVec` reduction. Extract it over loose variables and apply symbolically — kernel-safe
  because a lemma application instantiates an already-checked body. **Hard constraint:** the
  helper's conclusion must match the original `have`'s type **character-for-character**; it is a
  downstream `rw` target.

  *Scope refinement (measured, W1/g2/bH3).* The constraint is about the **ascription position**,
  which decides which numeral gets elaborated at which type. It is **not** about redundant outer
  parens: `((16 : ZMod p) - X).val` and `(16 - X : ZMod p).val` elaborate to the same term, and every
  downstream `rw` fires across that spelling. Treat differing ascription placement as blocking;
  treat cosmetic parenthesisation as fine. The stricter reading costs real golf for no safety.
  Worked example: `inner_val`/`inner_hi_val` in `Proofs/Chips/ShiftLeftChip/Core.lean`. Leave the
  abstract-`BitVec` helpers (`srl_toNat`/`sra_toNat`) alone.
- **Line reflow** to ≤100 chars, except where it would rewrite a frozen statement form (§2.8).

---

## 10. Gates

Per gated group, stopping at the first failure:

1. **Manifest check** — `git status --porcelain`; changed paths ⊆ the group's manifest.
2. **Layer pre-gate** (shallow waves only) — `lake build SP1Native` / `SP1Model` / … as a fail-fast.
3. **`lake build SP1Clean`**, teed to a log; `-j 1` for solo/heavy groups.
4. **Log assertions** — zero `error:`, zero `warning:`, zero `info:`.
> **Do not blanket-kill `lean --server` / `lake serve` before a gate build.** It looks like harmless
> hygiene and it is not: the `lean-lsp` MCP server owns child lean processes, and a `pkill` matching
> them takes the MCP connection down for the whole session. Reconnecting needs a Claude Code restart,
> which strands every editing worker (they verify through the LSP and must not run builds). This
> happened once in this campaign and cost a session restart.
>
> The kill was never what established truth anyway — the **olean-deletion escalation** in gate 5 is.
> If a module you touched does not appear in run 1's job list, delete its
> `.olean`/`.ilean`/`.trace`/`.hash` and rebuild it explicitly. That distinguishes a genuine cached
> pass from an olean written seconds earlier by a dying process, which a 1-second no-op rerun cannot.

5. **Stale-olean smell test** — immediately re-run `lake build SP1Clean`. All three required: exit
   0; completes in **<90s**; and **re-elaborates zero modules** from the group. A rebuild on run 2
   means run 1 never persisted that olean, so run 1 was **not** a pass. On heavy groups also compare
   run 1's wall clock to the recorded baseline — a **>1.5×** regression fails even when green.
6. **Source guards** — `check_no_native_decide.sh`, `check_no_skipkerneltc.sh`,
   `check_heartbeats.sh` (may only ratchet **down**).
7. **Statement-preservation gate** — replacing the plugin's `theorem_statement_protected`, which
   greps only the first line of a signature and misses the continuation lines where hypotheses live.
   The check is on the **set** of normalized signatures, not on the presence of `-` lines:
   - parse every declaration (including `@[...]`-attributed ones) from its keyword to `:=`/`where`,
     comment-stripped and whitespace-normalized, and compare the resulting **multiset** per file,
     before vs after;
   - no signature may be removed or modified;
   - **a pure reorder is permitted.** Moving a declaration emits a `-`/`+` pair for an identical
     normalized signature; that is a position change, not a statement change, and it is often needed
     to let one lemma cite another (`DivRemChip/Math.lean`'s `divu_remu_spec` ⇐ `udiv_umod_bitvec`
     wanted exactly this). A `-`-line rule rejects it spuriously; a multiset rule does not.
     Reordering across a `/-! ## … -/` divider still needs care — the prose describes what follows.
   - a `+` of a brand-new declaration only where the audit declared an additive split (§4) or an
     extracted helper (§4a) — and for a helper, check it is `private` and does not match a probe glob.
8. **Commit**, one per batch.

At wave boundaries additionally: `lake lint`, `lake test`, `scripts/run_audit.sh`.

---

## 11. Renames are queued, never applied

The plugin's Phase 5b **does not run in this repo**. Workers append candidates to
`scratch/cleanup-marathon/renames.jsonl` (not the plugin's `.mathlib-quality/` path) and move on.
The queue is reported at the end for a human decision.

Renaming here is high-blast-radius: `scripts/nolints.json` is keyed by fully-qualified name;
`scripts/gen_axiom_probe.py` resolves probe targets by regex over source text;
`scripts/check_report_citations.sh` hard-codes 15 file+declaration pairs; `docs/verification-report.md`
cites declarations by name; and `update_extracted.py` regenerates files that reference them.

The stock `naming_gate` insists a rename be *applied*, and treats "existing convention preserved"
as unacceptable. In this repo, **queueing is the terminal state** — that is a pass, not a deferral.
