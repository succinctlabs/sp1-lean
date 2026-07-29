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

   > **Omitting an `ElaboratedCircuit` field is a *performance* decision, not just a style one —
   > A/B time it.** `proof-patterns.md` says these obligations should almost never be hand-written, and
   > deleting them so Clean's default (`by intros; rfl`, `Clean/Circuit/Basic.lean:229,236`) fires is
   > usually right. But the default **whnf's the entire chip `main`**, while a hand-written
   > `simp only [circuit_norm, main, <subcircuits>]` never does. Measured across 19 `Native/Chips`
   > files:
   >
   > | `main` composes | effect of omitting |
   > |---|---|
   > | `AddressOperation` **+ `U16MSBOperation`** | **+63% to +132%**, or outright `timeout at whnf` |
   > | `AddressOperation` only | −3% (safe) |
   > | ALU chips whose `output_eq` body was already `simp only [main, circuit_norm]` | ~0% (safe) |
   >
   > The driver is **not** "is it a load chip" — it is whether `main` pulls in the sign-extension block.
   > `LoadDoubleChip` and `StoreDoubleChip` are loads/stores and are fine; `LoadHalf`/`LoadWord`/
   > `LoadByte` are not. And the ALU chips are neutral because their hand-written body unfolded `main`
   > anyway, so there was nothing to save.
   >
   > **The trap:** the defaults *succeed* on most files, so an untimed worker reports a clean −2 lines
   > while silently adding 60–130%. A full `lake build` will not catch it either — +3s on a 2.5s module
   > vanishes inside a ~480s build. These files sit at a ~2.2s import floor, so real deltas are
   > compressed; validate your instrument on a known-regressing file before trusting a null result.
   >
   > **Ordering:** run the omission pass *before* the ceiling pass. A defaulted `output_eq` can
   > manufacture a fresh ceiling — on `LtChip` it would have re-created the exact 1M just removed.
   >
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

> **Never *infer* an axiom change from the tactics you removed — measure it.** A worker replaced some
> `omega` calls in `FormalModel/Contracts/Chips.lean` and reported that two lemmas had dropped
> `Classical.choice`. Measured on both versions in place: `rv64_addw_eq` never carried it, and
> `rv64_mulw_eq` went `[propext]` → `[propext, Quot.sound]` — a strict *addition*, the opposite
> direction from the claim. Nothing left the permitted set, so the change was admissible, but the
> claim was false and had already been relayed upward before the gate caught it.
> **`#print axioms` on the pre-edit version too, or say nothing about axioms.**

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

> **Do not treat `Fact`/`NeZero` locals as load-bearing by inspection — and do not trust the
> derivation source either.** This rule has now been wrong in *both* directions. It first said every
> such local is load-bearing (which preserved dead code); the derivation-source table that replaced
> it said the `2 ^ 17`-derived form is always load-bearing — and all four such copies in
> `Native/Operations/BitwiseU16Operation.lean` turned out to be dead.
>
> **What actually decides it: whether `Fact p.Prime` is already in that declaration's *elaborated
> signature*.** The hazard the rule exists to prevent is not "the proof breaks" — a broken proof is
> loud and safe. It is that deleting the local can make `Fact p.Prime` newly *used*, which **adds a
> binder to the signature**. That is a statement change, and it is quiet.
>
> **A cheaper standing check: `linter.unusedSectionVars`.** Zero `unusedSectionVars` warnings ⟺ every
> section instance is still used ⟺ no binder was dropped. So if a golf stops using an instance, the
> fix is **not** `omit` (which removes the binder and *changes the signature*) — it is
> `set_option linter.unusedSectionVars false in`, which keeps the auto-included binder and leaves the
> signature byte-identical. `LtOperationSigned.zero_ne_one'` is the worked case: its one-line rewrite
> stopped using `Fact (2 ^ 17 < p)`, and the `set_option` is what preserved the statement. Note the
> asymmetry — a **new** declaration takes the ordinary `omit [Fact (2 ^ 17 < p)] in`, because it has
> no prior signature to preserve.
>
> **The recipe — `#check`, delete, re-elaborate, `#check` again.** Compare the printed signatures
> before and after; they must be byte-identical. Deletion-and-re-elaboration alone is necessary but
> **not sufficient**, because a signature can gain a binder while every proof still compiles. Never
> grep.
>
> Measured so far: `NeZero p` and `Fact (1 < p)` from `Fact p.Prime` — dead (many sites);
> `NeZero p` from `Fact (2 ^ 17 < p)` — dead in `BitwiseU16Operation`, load-bearing elsewhere, so
> **check each one**. In-proof `have`s re-deriving `Fact (2 ^ 17 < p)` under a stronger hypothesis are
> dead by construction, since `Math/Word.lean` declares `instFact_2_17_of_2_24` and
> `instFact_2_24_of_2_25` (four were deleted during the `sixteen_lt` hoist). There is deliberately no
> *global* `NeZero p` (§6 above) — that remains true and is a separate question from whether a given
> local is dead.

- **`autoImplicit` is ON here, and it fails *silently* when you hoist a statement.** A lemma whose
  **statement** mentions a name reachable only through a targeted `open` — e.g. `byteChannel`, which
  lives in `SP1Clean.Channels` — does not error. The name is **auto-bound as a fresh implicit
  variable**, and the lemma elaborates as something weaker and different; it surfaces later as a
  confusing mismatch printing `Channels.byteChannel` against `byteChannel`. Any hoist mentioning a
  channel in its statement needs `open SP1Clean.Channels (byteChannel) in` (the shape
  `Faithful/CPUState.lean:67` already uses mid-file). **Validate a new shared statement by *applying*
  it to an existing call site** — a scratch `example` discharging the verbatim hand-written `have` —
  before rolling it out.

- **`unusedSectionVars` is not globally suppressed on the proof pillar**, so a hoisted lemma usually
  needs an explicit `omit [Fact (2 ^ 17 < p)] in`. Note `Fact p.Prime` is often *genuinely* used, via
  `instFiniteFieldFOfFactPrime` in the type. `ChipTactics.bool_iff` is the reference shape.

- **Check for an import cycle before promising a hoist covers every site.** `ChipTactics.lean` imports
  `Faithful/CPUState.lean` (its `faithful_chip` hard-references `cpustate_constraints_faithful`), so
  CPUState cannot cite anything hoisted there — 2 of the 13 `hbk` sites are excluded for this reason
  alone, with byte-identical statements. A partial correct hoist beats a forced general one.

- A `change` that only restates an `abbrev` is free to delete when the closer is a term rather than a
  tactic that needed the syntactic form. `MicroTime.chainState_succ_front` went from 8 lines to 2
  this way (three pure-defeq `change`s dropped, body now `exact congrArg (·.bind Machine.stepOnce) ih`).
  > **But check it is really restating the *same* constant.** `TimedGrounding.stepOnce_of_sailStep`'s
  > `change SP1Clean.Machine.stepOnce s = some s'` looks like the same pattern and is **load-bearing**:
  > `Semantics.stepOnce` is a *distinct constant*, so the `change` is precisely what makes the next
  > line's `unfold` possible. Deleting it gives ``unfold` failed to unfold `Machine.stepOnce``. The
  > rule is about a defeq restatement of one abbrev — not about a `change` that crosses two constants
  > which merely print alike.

- **`have ⟨…⟩ := h` destructures without consuming; `rcases`/`obtain` clears `h`.** Where a proof needs
  a hypothesis both whole *and* destructured, the usual `refine ⟨valid, ?_⟩` + `rcases valid` dance is
  unnecessary — `have ⟨_, …, shardLayout, halts, _⟩ := valid` keeps `valid` in scope. Worth checking
  wherever you see a hypothesis reintroduced right after being cased on.

- **Two declarations can be the same declaration definitionally without looking it.** `TimeExtraction`
  had three payoff theorems with byte-identical bodies because `Readers.RegisterAccessTimestamp.Spec`
  applied to `real` *is* `ActiveTimestampBounds …`, and `RegisterAccessCols.Spec` is *defined as* the
  timestamp `Spec`. Two collapsed to three-line term applications of the first. When sibling theorems
  share a proof body verbatim, check whether their hypotheses are defeq before assuming they are
  genuinely different results.
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
- **The `ring` fallback bites twice, and both bites come from the same fact: `ring` never fails.**
  On a goal it cannot close outright it runs `ring1`, fails, emits `Try this: ring_nf`, and then
  succeeds via the `ring_nf` fallback.
  1. **The `info:` leak.** The proof passes but the build is no longer clean. Close those goals with
     `simp` (the `is_real` binary gate and `interval_cases` carry goals), `ring_nf`, or the explicit
     lemma.
  2. **`ring` cannot lead a `first` ladder.** `first | ring | linear_combination k | …` breaks every
     branch with `unsolved goals`: because `ring` "succeeds" as a mere normalisation on the goal that
     actually needed `linear_combination`, it shadows every alternative behind it. **Use `ring1` as
     the leading alternative.** A *trailing* `ring` is safe only because everything reaching it is
     already `ring1`-closable. Measured on `LtOperationUnsigned.sel_populate`.

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
> **`set_option … in` must precede the docstring, not sit between it and the declaration.** Putting it
> after a `/-- … -/` gives `unexpected token 'set_option'; expected 'lemma'` — and the real damage is
> that a ladder pass then **silently skips that site's rung**, with no timeout appearing, so the pass
> reports a clean result for a site it never actually tested. Check placement before trusting a
> measurement round.
>
> **Keep a recorded ladder to one line.** A removed ceiling should leave evidence of why removal was
> safe — but "the former 4000000 ceiling was ~100× over; measured floor ≤40000" is the whole content.
> Multi-line ladder transcripts belong in the campaign's perf log, not in the source. Several files
> have grown +3 to +5 lines this way, and across ~200 remaining sites that compounds into a net
> positive diff for a campaign whose point is reduction.
>
> **Never write the literal string `set_option maxHeartbeats` inside a comment or docstring.**
> `scripts/check_heartbeats.sh` counts sites with a raw `grep -rc "set_option maxHeartbeats"` — it
> does not parse Lean, so a comment mentioning the option scores as a live ceiling and silently
> corrupts the ratchet. When recording a measured ladder (which you should), phrase it without the
> literal: "the former 8M ceiling was ~170× over". Two workers hit this; one caught it, one did not.
> A pre-existing instance at `Proofs/Sail/Advance.lean:2325` means the 853 baseline has always
> counted at least one phantom.

> **A declared ceiling's magnitude predicts nothing — in either direction.** `StoreByteChip.circuit`
> is declared 2M and *fails at 1,000,000*: under 2× headroom, the campaign's first genuinely
> under-provisioned site. Its two siblings **in the same file** sit ~40× over their floors. So a
> large number is not evidence of slack and a small number is not evidence of tightness; only a
> measured ladder distinguishes them. Do not triage sites by declared value.
>
> **"Kept" and "correctly sized" are different findings, and only a ladder separates them.** W4/b4
> kept all 19 of its ceilings *and* found 18 of them oversized — it removed none while cutting the
> aggregate declared budget 174M → 31.5M (5.5×). A batch that removes nothing has not necessarily
> failed; report the ratchet separately from the removal count, or a real 5.5× win reads as a
> zero-yield batch.
>
> **What predicts removability is the declaration's *role*, not its chip and not its file's family.**
> Three W4/W5 batches over the *same nine Load/Store chips* settled this. At the
> `Proofs/Chips/*/Formal.lean` layer: **0 of 19** removable, floors (150k, 400k]. At the
> `Proofs/Chips/*/Bridge.lean` layer: **21 of 21**. At the `Faithful/` anchor layer: **52 of 52**.
> Same chips, three orders of magnitude apart — because chip `Formal.lean` proofs are
> `circuit_proof_start` whnf towers while the anchors are `rw`/`simp only` syntactic bridges over
> already-elaborated oracle lists. Within one layer the role still discriminates: across the six
> `Faithful/` ALU anchors, `*_memory_*`/`*_byte_*`/`*_constraints_faithful` all floor ≤40000, while
> `*cols_state_*`/`*cols_program_*` floor in (40k, 60k] and `*_interactions_faithful` in (60k, 100k].
> Counter-intuitively **State/Program anchors cost more than Byte anchors** — Byte has 12 emits and
> clears 40000, Program has 1 and does not. The cost is channel-distinctness filtering, not emit
> count. Screen by role; never extrapolate a floor across layers.
>
> **A floor measured through the LSP is not a floor against the gate.** The `lean-lsp` server does
> not apply the pillar libs' `moreLeanArgs`, the same reason `lake env lean` cannot certify a pass
> (§7). So when KEEPING a ceiling, set it at roughly **4× the measured floor bracket**, not at the
> bare lowest passing rung — a 1× margin is measured under weaker options than the build will use.
> Removal is unaffected: a site that clears ≤40000 against a 200000 default has ≥5× headroom either
> way.
>
> **Prefix scratchpad helper scripts with your batch id.** The scratchpad is shared across concurrent
> workers. A W5 worker's `rung.py` was silently overwritten mid-batch by a sibling's same-named
> script using a different sentinel convention, so its delete pass wrote `maxHeartbeats 0` — a
> **valid but wrong** Lean option — instead of removing the lines. It failed no build and raised no
> error; only the worker's own post-pass grep caught it. Use `w5b1_rung.py`, not `rung.py`.

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

> **First check whether the ladder is just `assumption`.** If every alternative is a bare context
> reference (`first | exact h0 | exact h1 | … | exact h15` over `interval_cases`-generated goals), the
> whole thing collapses to plain **`assumption`** — one token, no restart-from-top duplication, and it
> *removes* lines rather than adding them. This is strictly cheaper than the ordered-bullets rewrite
> below, which costs roughly +14 lines per site. Measured on `MulOperation/Formal.lean`, where it also
> retired two 211-codepoint lines and verified at a *lower* rung than the site needed pre-fix. Only
> reach for ordered bullets when the alternatives are genuine tactic blocks with side conditions.
>
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

**1d. `simp_all` under `circuit_proof_start` — and the one place the sibling screen mis-predicts.**
A single `simp_all` closing a small goal against the *entire* post-`circuit_proof_start` context can own
a whole file's budget. `DivRemOperation/Compare.soundness` spent 4M on one `simp_all` closing a
four-case numeral goal; narrowing it to `rcases … <;> rw [hrcmGate, hz, hv] <;> simp` took the floor
from (40000, 100000] — a keep-and-lower — down past 40000, making the site removable.

> **This is the known false negative for the sibling screen.** The *byte-identical* `simp_all` block in
> that file's `completeness` cleared the same rung, because that proof destructures less context. So
> two sites with identical tactic text can have very different floors, and an unceilinged sibling
> running the same tactic is **not** evidence the ceilinged one is vestigial. When the suspect tactic
> is context-sensitive (`simp_all`, `omega` over a large hypothesis set, `aesop`), measure rather than
> screen.
>
> **The high-yield instance: an inline obligation with no chip content.** In the load `Bridge.lean`
> files, `advance_of_load_width{1,2,4}`'s `hpin` obligation was discharged inline as
> `by intro w' u' h; simp only [loadOpcode] at h; cases u' <;> split_ifs … <;> simp_all [...]` — a
> `simp_all` against the whole post-`obtain` `advance` context, twice per file across six places.
> The obligation is a pure `loadOpcode` fact about loose `isU`; it never needed the context at all.
> Extracting it as a `private lemma` (§4a) moved all three sites from **FAIL at 400000 to PASS at
> ≤40000**, over 100×, and turned three "genuinely binding" ceilings into removable ones.
> **`Model/Semantics/Decode.lean` already owned the exact `storeOpcode_pin_one` analogue — only
> `loadOpcode` lacked one.** When an inline `by …` obligation mentions none of the surrounding
> circuit's variables, that asymmetry *is* the cost; look for a proved sibling before measuring.

**1e. A `set` over a large term is an `isDefEq` abstraction across the whole goal.**
`set x := <big populate tower> with h` forces an abstraction pass over everything in scope, and on a
witness-tower goal that alone can own the budget. `BitwiseChip.completeness` failed at 1M **at the
`set` line**; deleting it took the same proof from FAIL@1M to PASS@1M — and the `with hR` binding was
dead, with the downstream `show … = _ from key k` rules reading their RHS off `key` instead. Check
whether a `set`'s binding is actually used before assuming it is load-bearing; a bare `set` for
readability on a large term is a perf hazard.

**1c. LCNF-compiler-bound, not elaboration-bound — check *which phase* times out.** A budget can be
spent on **code generation** rather than on proving. `Native/Operations/MulOperation/Defs.lean`'s
`def main` elaborates fine at 40000; the failure is `(deterministic) timeout at «LCNF compiler»`,
reported at the `def main` line, over sixteen giant schoolbook product expressions. Two consequences:

- **None of the fold recipes apply.** Opaque values, folded hypothesis types, `circuit_output_eq` —
  all of them target elaboration, and there is no tactic here to fold. Do not burn passes on them.
- **`noncomputable def` is *rejected*, not deferred.** It would remove the compiled body, and
  `SP1CleanTest/TraceGenTests` derives whole-chip traces from the chips' own `main` witness closures
  under `native_decide`. Dropping the code would plausibly break `lake test`.

Such a site is **lowered, not removed**, and deliberately keeps more headroom than an elaboration-bound
one (~6.7× rather than the usual ~5×), because code-generation cost is more load-sensitive. Read the
phase name in the timeout before classifying anything.

**2. A duplicated `.val`-bridge fact — a raised ceiling as proxy, not term-intrinsic cost.** Look for the repeated `have` before you touch the
number. `ShiftLeftChip/Core.lean` carried 16 ceilings; its SLLW half was re-deriving `mul_v_val` /
`hi_lo_val` / `mul_v_add_val` by hand while the SLL half *in the same file* already called them, and
two residual `nlinarith` calls were re-proving `< 65536` limb bounds that
`Math/ShiftBounds.lo_hi_lt` already proves once over loose variables. Fixing the
duplication dropped 26 `nlinarith` to 3 and made **all 16 ceilings removable**. That is the
difference between raising a budget and driving the proof to closure.

**Screen on what `main` composes, not on which family the file belongs to.** This is the single most
useful predictor found, and it corrects an assumption that held for most of the campaign. The
`Proofs/Chips/*/Formal.lean` family is **not uniform**: the ALU chips went **8 of 11 removed**, every
removal clearing ≤40000 on the first pass, while the jump/U-type chips in the same family went
**0 for 4**. The discriminator is structural — `JalrChip` composes *two* witnessed `AddOperation`
gadgets plus `ITypeReader` plus `RegisterWrite`, and `UTypeChip`'s `AddOperation` addend is itself
witnessed. `JalrChip`'s two sites floor at **(2M, 4M]** against a declared 8M: about 2×, the
tightest in the tree, and correctly sized all along.

So: count the witnessed sub-gadgets `main` composes before predicting anything. A file in a
"family that removes cleanly" can still be genuinely binding, and a whole wave's expectation should
not be set by its directory.

**Lead with the sibling-comparison screen — it is nearly free, and it predicts *both* answers.**
Before laddering anything, find a declaration in the same file (or its mirror file) that does the same
kind of work and carries **no** ceiling, then ask whether it does *more* or *less* work than the
ceilinged one. `MulOperation/RawSpec.lean` ran two screens that **split**, and both calls were right
before a single rung: `full_product` vs the unceilinged `low_half` does 16 columns rather than 8
(256 monomials vs 64, coefficients to `2^120` vs `2^56`) → predicted **real**, confirmed;
`high_half_eq` vs the unceilinged `product_reassembly`, which does strictly *more* work → predicted
**vestigial**, confirmed. So the screen is not merely a vestigial-detector; an unceilinged sibling
doing *less* work is evidence the ceiling is genuine. Worked cases: `SailWrap`'s
`Sail.writeReg_writeReg_comm` — same tactic, same hashmap comm step, no dependent cast — passes at the
default and pinpointed the `acLt` cause; `Faithful/CPUState.lean`'s third interaction anchor does
strictly *more* work than the two ceilinged ones (same `hbk`, same binding hypotheses, plus a 4-entry
`List.Perm` instead of a filtered `=`) and has never carried a ceiling — which correctly predicted
both floors at ≤2500 against a declared 1M.

**Declared magnitudes are uninformative.** Across ~100 measured sites the declared value has never
correlated with the true floor: 16M families flooring at ≤40k, 8M at ≤20k, 1M at ≤1500, and the
highest-floor file in a batch carrying the same number as the lowest. Treat the number as evidence of
nothing but a copy-paste.

**Batch whole files, and use the rung itself as the label.** Separating ownership requires laddering
sites at *distinct* rungs — but the timeout message **embeds the rung it hit**, so giving each
candidate *group* a distinct rung disambiguates them even when every error is reported at the same
position (the shared `variable` line). That turns ownership separation from a serial search into one
pass. Measured: `Faithful/ChipOracle.lean` settled **11 sites in 6 passes (0.55 passes/site)** against
~3.5 passes/site for the serial method.

**The file protocol** — usually *one* round-trip after the control:

Set **every** ceiling in the file to a distinct rung, all of them **≤ 40000**, and elaborate once.
Everything that passes is removable: a site passing at ≤40000 *implies* it passes at the plain 200k
default with ≥5× headroom, so there is nothing left to check. Only the sites that fail need a
staggered follow-up, and those can again be batched by distinct rung.

> **Use distinct rungs at *one* magnitude — `40000, 39999, 39998, …` — not rungs spread across
> decades.** The rung is only a *label* in this pass; spreading them across magnitudes conflates "which
> site failed" with "what its floor is", and answers a question you did not ask. One uniform magnitude
> with unique labels answers the only question the pass poses — *does this site clear 40000?* — for
> every site simultaneously. `Advance.lean` settled **34 sites in a single pass** this way.
>
> **Measure a file-scoped ceiling separately from the scoped `… in` ones.** A file-scoped
> `set_option maxHeartbeats N` (no `in`) covers *every* declaration in the file, so it cannot take a
> distinct rung alongside the scoped sites — doing so makes every unceilinged declaration fail at one
> indistinguishable rung. Do the scoped sites first at uniform labels, then remove them and give the
> file-scoped one the whole file at a single rung. `Advance.lean`'s file-scoped 4M turned out to be
> owned by exactly one tactic call.

> Earlier guidance here described a two-pass form — delete-all, then 40000-all. **Pass A is redundant
> whenever pass B passes in full**, since the ≤40000 result already subsumes it. Keep the delete-all
> pass only as an optional cheap first shot on a file you expect to clear entirely. Measured:
> `RTypeReader` used the full two-pass form (5 passes); five sibling files used the collapsed form and
> took 2–3 each, settling 14 sites in 17 elaborations including controls.

Gate pass B on **40000, not the plain default** — the floor distribution inside a single namespace is
wider than it first appears (`ChipOracle`'s eleven ran ≤500 to 30000, a 60× spread).

**Two diagnostics that fall out of this, both validated:**

> **An in-body failure position is not stable across runs.** Three identical invocations at rung
> 60000 on `DivRemOperation/Core.lean` named **three different owners**, while the *signature*
> positions stayed fixed. Trust a signature position for attribution; treat a secondary in-body
> position as a hint only, and re-run before concluding which declaration owns a budget.

- **Where a site fails is an ATTRIBUTION tool, not a floor predictor.** It has now been wrong twice in
  the same direction, so treat it narrowly: a failure position tells you *which declaration or tactic
  owns the budget*, and nothing reliable about *how large* that budget is.
  `Faithful/LtOperationUnsigned.ltUnsigned_constraints_faithful` failed at an in-body tactic position
  (`itauto`) and floors at **~60000** — the highest floor measured anywhere in `Faithful/`, against a
  heuristic that predicted hundreds-to-low-thousands. Always ladder; never infer a magnitude from a
  position.

  The original over-claim, kept for context: *sites failing at their **signature** are the
  high-floor ones; sites failing inside a **tactic line** floor in the hundreds-to-low-thousands and
  mask nothing. In `ChipOracle` this sorted all eleven correctly.
- **The sibling screen is a reliable *ranker*, not a keep/remove oracle.** It ordered all eleven
  `ChipOracle` sites by floor with zero measurements — but the group it flagged "plausibly genuine"
  (the only one with no unceilinged comparable sibling) was still ~40× over-provisioned. Use it to
  prioritise and to predict *relative* cost; never to decide removal without a ladder.

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
  > **Masking is rung-dependent — never conclude "no masking" from one low rung.**
  > `MulOperation/RawSpec.full_product` masks or does not mask depending where you probe: at 200k/400k
  > it fails *inside* its tactic block, gets added `sorry`'d, and its dependents stay visible; at 1M
  > the failure moves to `whnf` at the **signature** and both dependents cascade to
  > `(kernel) unknown constant`. Check for masking at the rung you actually intend to use.
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

  > **Then take the second step: partially apply the helper.** Collapsing each repeated bridge to a
  > one-liner is only half the win. On `DivRemOperation/Core.lean` the same two-line
  > `rw [← h, Vector.getElem_map]` bridge appeared **176 times**; folding to one-liners took 352 → 176
  > lines, and *partial application* — replacing each per-index family with one **quantified
  > `simp only` rule** — took 176 → **25**. Total −466 (−40% of the file), and elaboration improved
  > 19.0s → 15.8s. Whenever you have collapsed N copies to N one-liners, ask whether one quantified
  > rule replaces the whole family.
  >
  > **The quantified `simp only` rule only fires when the helper's bound *is* the vector's own
  > length.** `StoreWordChip`'s `eoap : ∀ i (hi : i < 2), … prev_value[i] = …` is stated at bound 2
  > over a **length-4** `Word`, so the `getElem` side condition is a derived `omega` term rather
  > than `hi` itself and simp cannot key the pattern. It **fails silently** — no tactic error; it
  > surfaces four lines later as `Application type mismatch` on the consuming `exact`. When the
  > bound and the length disagree, leave that helper at explicit indices.
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
3. **`lake build SP1Clean`**, teed to a log. **There is no `-j` option** — Lake 4.31 in this
   toolchain accepts only `-J/--json`; both `lake build SP1Clean -j 3` and `lake -j 3 build
   SP1Clean` fail to parse, and two W4 gate runs were burned discovering it. To serialise a
   Tier-S build, control concurrency by *not running anything else* (reap stale `lean --worker`
   children first, per the note below) rather than by a flag. Default parallelism measured
   640% CPU / 7:24 wall on a cold-ish 3610-job build.
4. **Log assertions** — zero `error:`, zero `warning:`, zero `info:`.
> **Never kill `lean --server` or `lake serve` — but stale `lean --worker` processes from *exited*
> agents are fair game.** The distinction matters and cost the campaign a session restart before it
> was understood. The `lean-lsp` MCP server *is* `lean --server`/`lake serve`; killing those takes the
> MCP connection down for everyone. Their `lean --worker` children, however, outlive the agents that
> opened them: `Advance.lean`'s worker found **7 stale workers holding 22 GB RSS**, which is the likely
> reason an earlier attempt at that file died outright. Reaping those is safe and sometimes necessary
> before a Tier-S file.
>
> The original over-broad form of this rule read:
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
