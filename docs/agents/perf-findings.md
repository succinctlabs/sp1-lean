# Elaboration budgets — how to avoid needing one

**This repo does not raise elaboration budgets.** Hand-written Lean carries zero
`set_option maxHeartbeats`, matching upstream Clean, which has none in 44,603 lines and enforces that in
review. Three hand-written `maxRecDepth` sites remain, all structural and measured.

`scripts/check_option_escapes.sh` enforces this: any `maxHeartbeats` or `maxRecDepth` site under
`SP1Clean/` or `SP1CleanTest/` that is not named in `scripts/option_escapes_allowlist.txt` fails the build.
It is a prohibition, not a budget — it does not count, and it does not permit a new hatch in exchange for an
old one. Every allowlisted site is on a generated definition or is a measured structural case, and each
entry carries its floor bracket and mechanism.

**So when a proof is slow, the job is to fix the cause.** This file is how. It is not a record of what was
fixed; it is the set of techniques that work, in the order to reach for them.

---

## 1. The rule: extract over **opaque** arguments

Nearly every blowup in this tree is the same shape — a value that should have stayed abstract reaches a step
that has to unfold it. The fix is to put an opaque variable between the two. It is almost never to make the
expensive step cheaper.

The cost is rarely where it looks. Real examples of where it actually sat:

| symptom | where the cost was | fix |
|---|---|---|
| a closing `tauto` | the **local context**, not the goal — spent hypotheses still mentioned `(…main …).operations offset`, and `tauto` normalises everything | `clear` the spent hypotheses. Floor moved 25× |
| a `rfl` on a `toElements` | the **spelling of a definition** — a struct *literal* forced `toElements` through `componentsToElements` | build it with `fromElements`, so `toElements_fromElements` fires in one step |
| a `have … : …` block | the **type**, not the proof — `(populate …).field[k]` in a *statement* forces `whnf` through a `let`-bundle, once per concrete `k` | restate over an opaque struct so the projection is inert; apply with no written-out type. 22× |
| a `simp` fixpoint | the **order** of two pipeline steps — it ran after `main` had been unfolded into the context | hoist it above the unfold. 1000× on that step |
| 24 `rw [gate] at e; linear_combination e` pairs | each one renormalising a ~115-hypothesis context | one 3-line opaque-argument lemma, applied as a **term** |

**The corollary that gets learned the expensive way:** extracting a block *within* the same proof buys
nothing. A recorded negative result in `DivRemChip/Evidence/` — "extracting the componentwise `Vector.ext`
sweep into its own lemma moved nothing" — stood for a long time as evidence that a site was irreducible. It
had been extracted into a `have` inside the branch, so it kept the whole branch context. The same extraction
to a lemma over opaque arguments is what paid.

So when an extraction "doesn't help", check **what the extracted thing can still see** before concluding the
cost is intrinsic.

### The meta-rule: a correlate found by reading code predicts nothing

Structural hypotheses derived from reading the source have a poor record here. Four were promoted on
code-reading and all four were corrected by measurement — including one that was upstream Clean's own
documented performance rule (measured delta: **0.008%**), and two that were *correct diagnoses of real
phenomena that simply were not the cost*.

That last category is the trap: a mechanism can be genuine, verifiable, and irrelevant. **Ladder before you
believe it, including — especially — when you found it yourself.**

---

## 2. The predictor

**What binds is not *touching* an unfolded generated list — it is letting that list reach a
`congr` / `isDefEq` / unification step.**

This is Clean's whnf-into-expensive-values doctrine, measured. A proof that rewrites a generated
`asserts` / `interactions` / `.operations` list with targeted `simp only` over `rfl`-projection lemmas,
never unifying against it, is cheap with the list right there in the goal. Contact is necessary, not
sufficient — screen on the **unification step**.

### It discriminates between proofs that look identical

- Two lemmas can share byte-identical tactic text and differ >25× in cost. Four `*_roundtrip` siblings in
  `Faithful/DivRemChip.lean` split into **three** distinct floor brackets, because the header chunk's offsets
  land in the first `Vector` append arm and terminate its `rw` ladder early.
- Adjacent lemmas over the same 19-cell structure split >25×: *producing* a `toElements` normal form is
  expensive, consuming one is not.
- **Tactic-text similarity is not evidence of similar cost; the narrowing order is.** Branches that narrow
  with `right; …; left` *first* and only then apply a targeted `simpa` are cheap where the same text without
  the narrowing is not.

**But do not over-apply it either.** Nine `Faithful/{Load,Store}*.lean` siblings with four documented
structural differences between them measured to the *identical* bracket, because their depth was set by a
shared opener and every difference lived downstream in a shallow closing assembly. Siblings diverge where the
variation is — check whether that is where the cost is.

---

## 3. Cause classes, with their fixes

**Search duplication in a `first | … | …` ladder.** `first` restarts the ladder for every goal, so if the
matching alternative sits late, every earlier alternative is elaborated all the way through its side
conditions and discarded. Fix: `rcases … with rfl | rfl` (substituting makes side conditions uniform), hoist
fixed arguments into one `have`, and replace `first` with **ordered bullets**.
- First check whether the ladder is just `assumption` — if every alternative is a bare context reference,
  the whole thing collapses to one token, cheaper than ordered bullets.
- Sorting the ladder does **not** help; a ladder already in goal order still pays for every alternative.

**Permutative-`simp` term ordering over a dependent cast.** A permutative `@[simp]` lemma makes `simp` pick a
direction with `Lean.Meta.acLt`, whose cost scales with the compared arguments. When one is a `▸` cast whose
proof is a large `match`, that comparison dominates — and it presents as an opaque
`timeout at «Lean.Meta.acLt»` with **no hint of which simp lemma is responsible**. Fix: `unfold`,
`generalize` the cast away, re-run.

**`simp_all` under `circuit_proof_start`.** One `simp_all` closing a small goal against the *entire*
post-opener context can own a file's budget. Narrow it, or extract the obligation as a `private lemma` when
it never needed the context at all — that pattern has moved sites over 100×.
- **Before measuring an inline `by …` obligation, look for a proved sibling analogue.** When such an
  obligation mentions none of the surrounding circuit's variables, that asymmetry *is* the diagnosis — and
  the extraction may already exist somewhere in the tree. `Model/Semantics/Decode.lean` owned
  `storeOpcode_pin_one` while the `loadOpcode` analogue was being re-discharged inline in six places.
- Known false negative for sibling screening: a byte-identical `simp_all` in a proof that destructures less
  context is fine. When the suspect tactic is context-sensitive, measure rather than screen.

**`set` over a large term is an `isDefEq` abstraction across the whole goal.** Clean explicitly rejects
`set x := e with hx` as an opacity device — the kernel can still zeta-unfold it, *and* it leaves the giant
equation in context for later tactics to re-ingest. Use `obtain ⟨S, hS⟩ : ∃ S, e = S := ⟨_, rfl⟩` and
`clear hS` once you are done with it. A bare `set` for readability on a large term is a perf hazard.

**Leaving spent hypotheses in context.** `clear` is a performance tactic. A closing `omega`/`tauto`/`ring`
ingests everything in scope; sixteen column equations left live after they have served their purpose can be
most of a proof's cost.

**LCNF-compiler-bound, not elaboration-bound.** A `timeout at «LCNF simp»` / `«LCNF compiler»` is code
generation, and **none of the fold recipes apply** — they all target elaboration. `noncomputable def` removes
the compiled body and is viable only where nothing evaluates the definition; `SP1CleanTest` runs
`native_decide` over the Native circuits' witness closures, so it is not viable for those. Note per-declaration
`noncomputable` only — a `noncomputable section` over computable declarations produces an LCNF panic cascade
on this toolchain.

**Duplicated `.val`-bridge facts.** A raised ceiling is often a proxy for missing shared substrate — one half
of a file re-deriving by hand what the other half already calls, or re-proving a bound that `Math/` already
proves once over loose variables. Check `Math/` before writing arithmetic; several sites were fixed purely by
adopting helpers that were already imported and opened in the file but had never been used.

**Repeated per-index bridge lemmas.** Replacing a per-index family with one **quantified `simp only` rule**
collapses hundreds of lines. *Landmine:* the quantified rule only fires when the helper's bound **is** the
vector's own length; otherwise the `getElem` side condition becomes a derived `omega` term that simp cannot
key, it fails silently, and it surfaces several lines later as `Application type mismatch`.

**A `congr` chain peeling a right-nested `List.append`.** Twenty consecutive bare `congr 1` peel by
unification, once per element. One `simp only [List.append_cancel_left_eq]` peels the whole chain by
rewriting instead. This is worth ~26× on a large anchor.

---

## 4. Diagnosing a site

### The instrument

```lean
set_option diagnostics true in
set_option maxHeartbeats 40000 in   -- a LOW budget: see below
theorem foo : … := by …
```

The `[diag]` block is emitted **before** the error, so it works on a declaration that fails. `Eq.rec` /
`List.rec` / `dite` / `Vector.append` / `Nat.rec` in the tens of thousands is the signature of a runaway
`whnf`. `set_option trace.Meta.Tactic.simp.rewrite true` shows what simp is actually doing, including which
lemma fires and how often.

**Diagnose at a LOW budget, not a raised one.** The counter *ranking* is invariant across budgets for a
single declaration — the same top ten in the same order, uniformly scaled — and the failing run is the faster
of the two.

⚠ That invariance holds for **one declaration across budgets**, not for two variants at a cutoff neither
reaches. At a budget both fail at, each variant's counters are truncated wherever its own elaboration
stopped, and the ratio between them measures nothing. Use counters to find the *mechanism*; use a ladder to
score the fix.

### Ablation, in two steps

When a `have` block is the suspect, ablate **twice**: first the whole block, then the proof body alone with
the written-out type retained. If the second ablation does not move the bracket, the cost is in elaborating
the *statement* and no work on the proof will help — the fix has to change how the statement is spelled. This
distinction is invisible to both the phase name and the counters, which just say `whnf`.

### Laddering

Bisect with `set_option maxHeartbeats <N> in` at descending rungs; the floor is the highest rung that
*fails*, so the bracket is (fail, pass]. Record it in a one-line source comment above the declaration.

⚠ **Never write the phrase `set_option maxHeartbeats` or `set_option maxRecDepth` into a Lean comment or
docstring under `SP1Clean/` or `SP1CleanTest/`.** The guard greps those exact phrases and does not parse
Lean, so a comment quoting a whole directive scores as a live site. The bare option name in prose is fine; it
is the full `set_option …` phrase that matches. Write "the former 8M ceiling was ~200× over".

---

## 5. Measurement traps

- **The two options mask each other.** A recursion-depth need can be hidden behind a heartbeat failure and
  surface only once the heartbeat budget is satisfied. Ladder one option at a time and re-run to a fixpoint.
- **`try` does NOT insulate a tactic from either ceiling.** Both errors propagate out of `try`/`first`; Lean
  treats them as unrecoverable. A `first | cheap | expensive` fallback will not rescue a proof, so a fix has
  to reorder or restructure rather than add an alternative.
- **The error's phase name is a hint, not a diagnosis.** It misleads whenever the closer is a search
  procedure: a site reporting `timeout at whnf` with a max counter of 12,592 was five `tauto` calls. Where
  the phase name has held up it is informative — `whnf` sites respond to context-shrinking fixes, `isDefEq`
  and `elaborator` sites do not — but a `tauto`/`grind`/`omega` closer voids the signal.
- **A high `[reduction]` counter is not proof of a whnf problem.** Cross-check against the error's phase.
- **Counters are cumulative over the declaration**; they do not attribute cost to a tactic line. `[simp]`
  blocks *are* per-call and appear in source order — the one place you get intra-declaration attribution.
- **`#count_heartbeats` needs `set_option Elab.async false`.** Without it, 4.31's async elaboration
  undercounts by roughly 4×. With it, it gives exact totals where a ladder gives only a bracket.
- **A declaration's total work can exceed the budget it passes at.** Lean elaborates the signature and the
  tactic body as separate tasks with separate budgets, so a `#count_heartbeats` total above the ceiling is
  not a miscount — check which half you are looking at.
- **`lake env lean` does not rebuild edited dependencies** and exits 0 on a stack overflow. It is *stricter*
  than the real build on stack size and `synthInstance` budget, so a pass there is conservative — but always
  finish with a real `lake build`.
- **Warm versus cold runs.** A first elaboration of a file can be several times slower than the steady state.
  Compare warm to warm.
- **Verify the harness before trusting a clean sweep.** If a batch of sites all pass at the default, inject a
  deliberately impossible ceiling into one and confirm it fails. A sweep that cannot fail proves nothing.
- **A cause class rarely explains a whole file.** Fixing one usually re-attributes the cost rather than
  removing it, and the owner moves — a file's cost sat with two lemmas before one fix and with a completely
  different third lemma afterwards. Re-measure the file, not just the site you touched.
- **A timeout's reported location is not necessarily the declaration that failed.** `timeout at whnf` is
  reported at column 1 of a *signature*; at very low rungs it lands on the shared `variable` line and is
  useless for attribution. Separate ownership by laddering sites at *different* rungs until each failure
  lands inside a declaration body.
- **Apparent dead bindings are usually live.** Verify by elaboration, never by grep — repeated sweeps for
  "unused" hypotheses have found them feeding a later `subst`, a bare `omega`, or `get_elem_tactic` for an
  index appearing in a *statement*.

---

## 6. `circuit_proof_start`, and when to stop using it

`circuit_proof_start` is a fixed, **untunable** 13-step pipeline
(`Clean/Utils/Tactics/CircuitProofStart.lean`). Its core — `circuit_proof_start_core` — does exactly one
thing: match the goal's head against the supported `Soundness`/`Completeness` forms, unfold it, and `intro`
the binders. No `simp`, no `dsimp`, no unfolding of `main`.

The full tactic adds ~15 whole-context passes on top, including six `… at *` traversals and
`dsimp +instances only [main] at *`, which unfolds the entire circuit into every hypothesis *and* the goal.

**For a heavy composition, stop using the full tactic.** Run `circuit_proof_start_core`, then reproduce by
hand only the steps the body needs: `dsimp only [main, circuit_norm] at h_env` (definitional, castless),
project components with `.1`/`.2`, `clear h_env`, and `simp only [circuit_norm, h_input, <child circuits>]`
on each small component separately.

Two levers compose and are separable:

1. **Declaration splitting** resets the heartbeat counter (it is per-declaration) and gives each piece its
   own kernel check.
2. **`_core` + hand-sequenced casts** avoids the `at *` traversals, so an assembly theorem stays cheap enough
   to delegate with bare `exact`s.

**Step order matters more than step cost.** On one chip, 98% of the budget sat in a single step —
`provable_struct_simp` — purely because the pipeline runs it *after* `main` has been expanded into `h_holds`
and the goal. Against the still-folded context the same fixpoint costs ~1000× less and destructures
identically, because destructuring is driven by `h_input`/`h_assumptions`. Both of the hot spots named in
upstream's own doc were irrelevant there. `SP1Clean/Proofs/CircuitProofStart.lean` holds named variants that
perform this reordering; prefer adding a documented variant there over copying a bespoke tactic block between
chips.

**A caveat on that reordering:** `provable_struct_simp`'s struct-eval set is deliberately *not* a
`circuit_norm` subset (its `getElem` lemmas loop against `circuit_norm`'s element-map spelling). Hoisting it
above the unfold means it no longer reaches the unfolded hypothesis; restore that with a **scoped**
`simp only [<structEvalSimpLemmas>] at h_holds ⊢`, never by adding those lemmas to a `circuit_norm` call.

**Related, and cheap to check on any new chip:** Clean's `AGENTS.md` says passing `elaborated` as an explicit
field is "very important" for performance. Follow it when writing a chip — it costs nothing there. It is
**not** a remediation lever for an existing ceiling: tested on the one chip where the correlation looked
strongest, it moved the measured total by 0.008%.

---

## 7. When a site is genuinely irreducible

Rare. It has happened once in this tree in a way that survived measurement, and four other inherited
"irreducible" verdicts turned out to be untested guesses.

Before concluding it, you must have:

1. a **measured floor bracket** from a real ladder, not an estimate;
2. a **named mechanism** — which pass, which term, which step;
3. at least one **attempted fix** from §1 and §3, with its measured result; and
4. a reason the cause cannot be moved, not merely that a first attempt did not move it.

Only then add an entry to `scripts/option_escapes_allowlist.txt`, carrying all four. The allowlist is a last
resort, not an allowance: it exists so that a handful of genuinely irreducible generated definitions do not
force the guard to be weakened for everything else. Prefer fixing the generator over adding an entry — the
emitters in `update_extracted.py` carry measured tables for exactly this reason, and blanket emission there
has repeatedly turned out to be one to two orders of magnitude over what any definition needed.

For calibration, the one confirmed case: a generated system-table definition contains a *single* list entry
whose transitive `let`-closure is **1239 bindings**, and the extractor's chunker bottoms out there — chunking
at one entry per part still leaves 1239. That is what "irreducible" has to look like.
