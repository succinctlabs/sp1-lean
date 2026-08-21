# Clean upstream — the fork pin, the split rule, and the PR queue

This project builds on the [Clean](https://github.com/Verified-zkEVM/clean) zk-circuit DSL. As of
2026-08-13 the `Clean` dependency is pinned to a **fork**, because some of what we need is a change
to an existing Clean declaration rather than an addition. This file records the fork's state, the
rule for what may go in it, and the queue of changes with the measurements that justify each one.

Reader-facing trust consequence: `../release-audit.md` § "Audited sources". The short version of the
rule also lives in `../../AGENTS.md` § "Clean-native principles".

## The split rule

**Modifies an existing Clean declaration → the fork.** One branch per upstream PR. It *cannot* live
in `ToClean/`, because Clean's own downstream theorems refer to Clean's declaration and not to our
copy. `AgreesBelow` is the worked example: a local copy carrying the two extra conjuncts yields a
*weaker* `ComputableWitnesses` obligation, and Clean's `witgen_usesLocalWitnesses` needs the stronger
one — so the shim would not feed the theorem it exists to feed.

**Pure addition → `ToClean/`.** No pin bump, and acceptance upstream is a plain deletion plus a
repoint of importers to `Clean.*`. Current residents: `Circuit/WitgenBridge` (the zero-witness
`ComputableWitnesses` composition lemmas), `Circuit/WitgenEval` (struct-level `Witgen.eval`
collapse + the `gateFE`/`iteFE` gate combinators), `Circuit/InteractionRecovery`,
`Circuit/WitnessCombinator` (`witnessVectorIR` — but see U10), and `Tactic/GetElemFastPath` (whose
upstream is Std, not Clean — see the last section). Everything here must have live importers; an
upstream-destined addition with no call site belongs in this document as a snippet, not in the
build (see U2). **`Circuit/WitgenCongr` was deleted under exactly that rule on 2026-08-19** — see
"Clean's direction" below.

**Before queueing anything as a fork change, check that what you need to reach is actually private.**
U2 was queued as a modification and turned out to be an addition, because the data it needs is a
public `def` that a tactic can read at elaboration time. Meta-level data is not automatically
out of reach.

**Edge case that looks like a modification and is not.** Tagging a lemma into `circuit_norm` that
Clean left untagged works from our side, because attributes are global. `Model/Channels.lean:201`,
`Math/Word.lean:31`, and the `eval_fromElements` priority override in two DivRem files are all in
this category: upstreaming them is courtesy, not a blocker, and they stay local.

## Fork state

| | |
|---|---|
| Fork | `https://github.com/dtumad/clean` |
| Pinned branch | `sp1-integration` — the merge of every open PR branch; this is what `lakefile.toml` pins |
| Pinned rev | `2dad7788d58b09eabeb3898506e4cb896e5d3e9d` |
| Upstream base | `0e53b9f2` (v4.32.2 `main`, post PR #443) |
| Toolchain | `leanprover/lean4:v4.32.2` — identical to ours |

`sp1-integration` **must keep the pinned rev reachable**: Lake clones `refs/heads/*` plus tags and
then checks out, so a commit living only on `refs/pull/*` fails with `fatal: unable to read tree` on
every machine without a warm cache. Never force-push or delete it. (`lakefile.toml` records the past
incident where a PR-head pin broke exactly this way.)

**Exit condition.** Re-pin to upstream as each PR merges; when the queue empties, the `git` URL goes
back to `Verified-zkEVM/clean` and this file becomes a historical record.

### Branch → PR map

| Branch | Change | PR | Status |
|---|---|---|---|
| `agreesbelow-data-hint` | U1 — `AgreesBelow` constrains `data`/`hint` | **[#450](https://github.com/Verified-zkEVM/clean/pull/450) — open, approved 2026-08-14, pending merge** | in `sp1-integration` |
| `witgen-share` | U11 — `WitgenIR.share` subterm sharing + proven `eval_share` (the wire format has `steps`/`localVar` sharing but nothing produced it; without the pass, SP1's DivRem witness programs serialize to 1.22 GB — 1.04 MB with it), plus the two PR riders: the scoped `Hashable` instance and `doc/witgen-wire-format.md`. Adjacent upstream context: issue #404 (the requested Rust interpreter needs shared programs to evaluate at sane cost) | **FILED: draft [#453](https://github.com/Verified-zkEVM/clean/pull/453)**, rebased onto `agent/fixed-columns-prover-data` @ `89e9abec` and gated by `shareIfSmaller` (see U11) | first 2 commits in `sp1-integration`; riders on the branch only |
| `u64wrap-prefilter` | U3 — two `u64Wrap` screens | — | **not merged**; pushed as a record of a rejected approach (see U3) |
| *(unfiled)* | **U12 — thread `ProverData` through witness generation.** `ProverEnvironment.fromArray`/`fromList` hard-code `data _ _ := #[]`, so `Circuit.witgen_usesLocalWitnesses` — the theorem that makes array-backed witness generation *honest* — is available only at the **empty** commitment. Any consumer that builds an AIR `Table` needs it at the table's real `data`, and the fact cannot be transported across a change of `data`: witness IR has `FExpr.dataGet`, and `AgreesBelow` deliberately refuses to identify environments committing different data (`Clean/Examples/DataWitness.lean`'s `not_computable_from_cells_alone` is the falseness witness). Clean's own module docstring records the omission as deferred. Staged additively as `ToClean/Circuit/WitnessGenerationData.lean` (`witgenWithData` + the chain, each proof Clean's own plus the parameter). **Upstream this is a generalization of existing declarations — add the argument in place — so by the standing split it belongs in the fork, not `ToClean/`, and the `WithData` suffix disappears on acceptance.** Found 2026-08-22 while building the W4 completeness substrate. | — | **not filed** |

A branch reaching `sp1-integration` means it earned its way there: Clean's own suite green *and* a
measured effect on local chip work. `u64wrap-prefilter` cleared the first bar and failed the second,
so it stays out. Keeping it pushed is cheaper than re-deriving why it does not work.

## Clean's direction (investigated 2026-08-19) — what we file and what we hold

Before filing anything upstream we read the maintainer's in-flight work end-to-end, because a
contribution that upstream plans to delete is worse than no contribution. Findings, with the
evidence, because every queue decision below now depends on them:

**Clean is not abandoning the witness IR. It is abandoning the JSON *runtime interpreter*.**
PR #446 (branch `agent/fixed-columns-prover-data`, the live head; #445 is its frozen base) deletes
`backends/plonky3/src/{clean_ast,clean_air,check_constraints,lookup,…}.rs` (−10,301) and the
Lean-spawning harness including `tests/helpers/lean_runner.rs` — the exact file issue #404 tells an
implementer to imitate — and drops `serde` from the backend. But `Clean/Circuit/WitnessExport.lean`
**survives and is maintained in lockstep** (+4/−0, keeping `FExpr.toJson` total over new
constructors), with its golden test still gated in CI. The stated policy, from
`doc/plonky3-polished-demo-requirements.md`: *"JSON may remain as an optional diagnostic or
build-time manifest, but it must not be the runtime constraint evaluator."*

**Their codegen makes subterm sharing more valuable, not less.** `Clean/Air/Extraction/`
{`IR`,`Lower`,`Rust`}`.lean` **reuses `Clean/Circuit/WitnessIR.lean` directly** — there is no
second IR; `Extraction.WitnessBlock` wraps `Witgen.Step`/`VExpr` plus a decidable well-formedness
proof. `Rust.lean`'s `stepsToRust` emits each step **one-for-one** as `let local_N: F = …;` and
inlines every other node as a tree, and `Lower.lean`'s `lowerWitness` is a verbatim passthrough:
**there is no CSE, hash-consing, or dedup anywhere in the pipeline** (both files read end-to-end;
the two checked-in generated `.rs` artifacts contain zero `let local_`). Sharing today is a manual
authoring decision, and `doc/witgen-authoring.md` records the open problem — sharing behind an
opaque program prefix — closing with *"If a use case ever genuinely needs sharing behind an opaque
prefix, that's the signal to add a locals-boundedness lawfulness class to `Witgen.M`."* A
**post-hoc** pass carrying `eval_share` sidesteps that problem entirely (it runs after all proofs
are done, so it needs no lawfulness class and no `circuit_norm` handle), and SP1's DivRem is that
use case.

**Consequences, applied:**

| payload | verdict |
|---|---|
| `WitgenIR.share` + `eval_share` (U11) | **FILED (#453)** after rebasing onto their live line. Reframed once more by measurement: it is a safety net for *generated* programs, and a proven no-op on the circuits Clean authors by hand. Serialization-agnostic: shared steps become `let` bindings in generated Rust exactly as they become `steps` in JSON. |
| `doc/witgen-wire-format.md` (U11 rider) | **Hold — stays ours.** Upstreaming it would promote a now-consumer-less debug printer to a specified, versioned external interface, in the direction they just walked away from. It documents *our* contract; it stays in `docs/`. |
| `rust/witgen-interp` as an answer to #404 | **Hold — stays ours.** #404 is stale-open (0 comments since 2026-06-11) and its concrete instructions reference files #446 deletes. The copy-of-record is the SP1-vendored copy; SP1 will never link Clean's generated Plonky3 Rust. |
| `Circuit/WitgenEval` | **Split.** `toElements_eval`, `getElem_eval_toElements`, and the three congr bridges are superseded by #448's `Witgen.WitgenIR.eval_ofCompositeFExpr`, `getElem_eval_ofCompositeFExpr`, and `eval_ofCompositeFExpr_eq_iff`. **`gateFE`/`iteFE` and their four eval/congr lemmas have no upstream counterpart** (the IR has cell-level `.ite` only, while gated column population is a universal prover idiom) — that half stays file-able, after #426. |
| `Circuit/WitgenBridge` | **Never file; retire at the pin bump.** Its stated reason to exist — "a `FormalAssertion` or `GeneralFormalCircuit` child carries no `ComputableWitnesses` field" — is *falsified* by #426, which puts the field on `FormalCircuitBase` and supplies the composition lemmas. It has 15 live call sites today, so it stays in the build until we migrate. |
| `Circuit/WitgenCongr` | **Deleted 2026-08-19.** Not duplicated upstream, but architecturally competing with the maintainer's 1068-line `computable_witnesses` tactic — and it had **zero call sites in our own tree**, violating the residency rule above. Its content (read-set collectors `FExpr.exprs`/`U64Expr.exprs`/`BExpr.exprs`/`Step.exprs`/`VExpr.exprs`/`envIndices`, the `CtxAgree` relation, and the capstone `WitgenIR.eval_congr`) is recoverable from git history at `73fab103`. **Follow-up at the next re-pin: check whether Clean's `computable_witnesses` tactic discharges what our five bespoke per-gadget congruence lemmas do — and with them the last five `-Witgen.u64Wrap` disable sites.** |
| `Circuit/WitnessCombinator` (U10) | **Don't file the combinator — file the one-attribute ask.** See U10. |

**The migration this schedules.** When #426/#448/#451 land, the next Clean pin bump is a real
piece of work, not a version string: `WitgenIR.ofFExprs` is renamed to `ofCompositeFExpr` (breaking
`Circuit/WitgenEval`), `FormalCircuitBase` gains a `computableWitnesses` field discharged by an
autoparam tactic (every chip's bundle), the free-standing
`FormalCircuitBase.compose_computableWitnesses` and `Circuit.subcircuit_computableWitnesses` are
deleted (breaking `Circuit/WitgenBridge`'s 15 call sites), and #451 changes the struct/vector
`eval` normal form by discriminating *literal* from *opaque* subjects. Budget for all 25
`Proofs/Chips/*/Witgen.lean` plus the two ToClean files. Nothing here blocks us today — the pin is
stable — but it is scheduled work, and letting the fork drift further raises its cost.

**#451 is upstream's answer to our own recorded design discussion** (see "Design discussion, not a
patch" below): rather than picking an orientation for `eval_eq_eval`, they discriminate literal
from opaque subjects so both orientations coexist confluently. Our 303-occurrence
`← ProvableStruct.eval_eq_eval` census is therefore *input to #451*, not a fresh problem report.

## The queue

Ordered by leverage, not by size. Each entry records what it unblocks and the measurement behind it,
because two of them looked obvious on a code read and turned out to need a different fix than the one
I first specified — see the "sizing correction" notes.

### U1 · `ProverEnvironment.AgreesBelow` should constrain `data` and `hint` — **FILED: PR #450, approved, pending merge**

> **Status (2026-08-19).** `Verified-zkEVM/clean#450` is OPEN, **approved by mitschabaude on
> 2026-08-14**, `mergeable: MERGEABLE`, `mergeStateStatus: CLEAN`, and still unmerged. The
> maintainer's comment: *"yes this is needed and #426 which should land soon also has this change."*
> Two things to carry into any nudge: (1) **the conjunct order differs** — #426 has
> `hint ∧ data`, #450 has `data ∧ hint`, so whichever merges second rebases by swapping two
> conjuncts (and deciding whether to keep #450's `.get_eq`/`.data_eq`/`.hint_eq` accessors and
> `agreesBelow_rfl`, which #426 does not add); (2) **`Clean/Examples/DataWitness.lean` is unique to
> #450** — #426's 80 files do not include it, and it carries `not_computable_from_cells_alone`, the
> in-tree *proof* that the old obligation was false rather than merely awkward. #426 also unfolds
> `AgreesBelow` under `circuit_norm`/`grind`, which #450 deliberately does not.

`Clean/Circuit/Basic.lean:424`. A `ProverEnvironment` has three channels a witness generator can
read: cells (`get`), committed data (`data`, via `FExpr.dataGet`) and prover hints (`hint`, via
`FExpr.hintGet`). `AgreesBelow` constrained only the first, so `Operations.ComputableWitnesses` —
whose whole content is `AgreesBelow n env env' → compute.eval env = compute.eval env'` — was **false**
for any program using the IR's documented nondeterministic escape hatch.

Non-breaking: `AgreesBelow` is in hypothesis position everywhere except one discharge site
(`FlatOperation.proverEnvironment_usesLocalWitnesses`), where both environments are
`ProverEnvironment.fromList _ hint` with constant `data`, so the two new components are `rfl`.

The PR argument is `not_computable_from_cells_alone` in `Clean/Examples/DataWitness.lean`: it proves
the old obligation was false, which makes this a bug fix rather than an ergonomics request.

**Payoff here, verified 2026-08-13**: `WitgenIR.eval_congr` now applies at a gadget's obligation.
Checked end to end against `AddOperation.populateIR` — the lemma unifies (`ofFExprs` unfolds to
`.ir [] (.lit …)`), `AgreesBelow.data_eq`/`.hint_eq` supply the two new premises, the `hcells`
premise is vacuous because the program has no `envRange` node, and the syntactic read set reduces to
a literal list of operand expressions. The recipe, including the two things that block a naive
`simp only` (gadget `let`s must be zeta-reduced; `VExpr.exprs (.lit es)` needs `Vector.toList_mk`),
is in `ToClean/Circuit/WitgenCongr.lean`'s "How to apply it" section.

Still to cash: retire the five bespoke per-gadget congruence lemmas onto it, which also removes the
last five `-Witgen.u64Wrap` disable sites in the tree.

### U2 · The struct-eval set at a chosen location — **reclassified: an addition, in `ToClean/`**

`Clean/Utils/Tactics/ProvableStructSimp.lean`. The struct-eval set is meta-level data
(`def structEvalSimpLemmas : Array Name`, line 40), so it is unreachable from surface `simp only`,
and `private simpPass` hardcodes the location:

```lean
evalTactic (← `(tactic| simp +instances only [$[$lemmas],*] at *))   -- line 207
```

`elab "provable_struct_simp" : tactic` accepts no location. To run the set `at h_holds ⊢` instead of
`at *`, `SP1Clean/Proofs/Chips/JalrChip/Formal.lean` used to **copy all 26 names verbatim**, under a
comment reading *"Keep the list in sync with Clean if that set changes."*

**Measured**: the narrower location took Jalr soundness's hot step from **2.90M of 2.97M budget units
to ≈2.2k — a 1000× drop**, because `at *` is ~15 whole-context traversals on a chip-sized goal state.

> **Reclassified twice, and the second time dissolved it.**
>
> *First:* not a fork change. `structEvalSimpLemmas` is **public** (`def`, no `private`), so a tactic
> outside Clean can read the array at elaboration time and apply it anywhere. That is five lines and
> needs no pin bump — the set then cannot drift, because there is no transcription left to maintain:
>
> ```lean
> open Lean Elab Tactic Lean.Parser.Tactic
> elab "struct_eval_simp" loc:(location)? : tactic => do
>   let lemmas ← ProvableStructSimp.structEvalSimpLemmas.mapM fun name =>
>     `(simpLemma| $(mkIdent name):ident)
>   let loc ← match loc with | some loc => pure loc | none => `(location| at *)
>   evalTactic (← `(tactic| simp +instances only [$[$lemmas],*] $loc:location))
> ```
>
> *Then:* building that tactic and swapping it in revealed the transcription was **dead code**.
> Measured 2026-08-13 at `JalrChip/Formal.lean`: with the enclosing `try` removed, `simp` reports
> *"made no progress"* in `soundness`, and `completeness` has no `h_holds` at all — `try` had been
> swallowing both failures. Both proofs elaborate identically with the step deleted (5.3s, versus
> 5.4s with it). The transcription was byte-identical to Clean's current 27 names, so no drift had
> actually occurred; the hazard was real but had not fired. **The fix was to delete the step, not to
> replace it**, so the tactic above has zero call sites and is not carried in `ToClean/` — this
> repo does not keep code without importers. It is recorded here because the gap is real and
> re-deriving it costs nothing.
>
> Two lessons worth generalising. Before queueing a fork change, check whether what you need is
> actually private — meta-level data is not automatically out of reach. And a `try`-wrapped step is
> unfalsifiable while it stays wrapped: strip the `try` before believing a comment that says the step
> is load-bearing.

What survives is U4: the *hoist* is real and measured, and it is the whole of what
`jalr_proof_start` buys. Residual upstream contribution, additive and non-blocking: let Clean's own
`simpPass` take a location, so the set is reachable without an out-of-tree elab.

### U3 · `u64Wrap` is expensive on the *successful* path — **screens tried and rejected**

`Clean/Circuit/WitnessIR.lean:252`, registered as `simproc u64Wrap` and tagged `@[circuit_norm]`
globally. On any `n % 2^64` or `n % 64` it invokes `omega` to decide whether the wrap is vacuous.

**Measured 2026-08-13** on `AddOperation.populateIR_congr` (the tree's five `-Witgen.u64Wrap` sites
are all this shape): the `simp` takes **118 s** with the simproc enabled — it needs a 4M-heartbeat
budget to finish at all — against **1.9 s** for the whole module with it disabled. Roughly **60×**,
and the profile is *diffuse*: no single entry above threshold, i.e. many small operations rather than
one hot spot.

> **Two screens were implemented, measured, and abandoned.** Both are on the fork branch
> `u64wrap-prefilter` (`b04a0e8c`), which is deliberately **not** merged into `sp1-integration`.
>
> 1. *Filter omega's input* to the hypotheses it can consume (comparisons/equations at `ℕ`/`ℤ`).
>    Clean's suite stayed green; our proof still timed out at 200k.
> 2. *Skip the call entirely* when neither `n`'s own shape nor any readable hypothesis could bound
>    it. Also green upstream, also no effect on our proof.
>
> The reason both failed is the reason the entry above was wrong: **these omega calls succeed.** The
> operands are structurally bounded (`(… % 65536) % 2^64`), so omega discharges them, and the cost is
> the *volume of successful calls*, not wasted failures. A screen cannot help with work that is being
> done on purpose.
>
> An earlier version of the first screen also skipped the call when no hypothesis looked useful, on
> the theory that a bound must come from a hypothesis. That is false and Clean's suite said so at
> once — Ch32, Maj32 and Add32 broke, because omega derives bounds from term structure
> (`x % k < k`, `UInt64.toNat x < 2 ^ 64`, `Fin.val i < n`) with an empty context.

So the useful change, if anyone wants it, is **not** a screen: it is a small syntactic bound computer
that discharges the common shapes (`a % k`, `UInt64.toNat`, and `+`/`*`/`/` over them) with a fixed
lemma set and never reaches `omega`. That is a real piece of meta-programming, ~60–100 lines with
proof construction, and it should not start without a measurement showing the bound computer covers
the shapes that dominate — the three wrong hypotheses above are what guessing costs here.

Two constraints for whoever takes it: `Add32.lean:326` names `Witgen.u64Wrap` in a `simp only` set,
so the registration cannot be renamed; and over-pruning fails *silently*, so add a regression example
to `Clean/Utils/Test/TestU64Wrap.lean` in the `And8` shape (bound over a field element's `.val`,
not a `ℕ` variable) first.

**Priority: low.** It blocks no chip work — the five sites work today with `-Witgen.u64Wrap`, and F1c
removes them.

### U4 · `circuit_proof_start` step order should be tunable

A fixed, untunable 13-step pipeline, including six `… at *` traversals and a
`dsimp +instances only [main] at *` that unfolds the entire circuit into every hypothesis *and* the
goal. Running `provable_struct_simp` **after** `main` expands is what put 98% of Jalr's soundness
budget in one step. We carry a near-verbatim reimplementation with the pass hoisted —
`SP1Clean/Proofs/CircuitProofStart.lean:60`, 9 call sites.

Clean already exposes `circuit_proof_start_core`, so half the composition story exists; what is
missing is a way to reorder without rebuilding the pipeline. Size **M**.

### U5 · `witgen` cannot carry committed data

`ProverEnvironment.fromList` hardcodes `data _ _ := #[]`, and the interpreter chain
(`dynamicWitness` → `dynamicWitnesses` → `proverEnvironment` → `Circuit.witgen`) threads `hint` but
not `data`. Needed by the completeness programme, where the honest-row bridge must move
`ConstraintsHold` from the witgen environment to the real table environment
`Environment.fromArray row data` — and those differ in `data` by construction for *every* circuit,
whether or not it reads data.

**14 definitions + 13 theorems across 4 files**, but ~0 external call sites (`Circuit.witgen` and
`FlatOperation.witgen` have none outside their defining file). Size **M**, **L** if `LookupCircuit`
and the examples land in the same PR.

> **Sizing correction.** Take a *bundle*, not a second positional argument: `ProverData` and
> `ProverHint` are the **same type** (`String → (n : ℕ) → Array (Vector F n)`), so threading two
> positional functions through nine definitions invites argument-order bugs that typecheck.
> `Environment.fromArray (row, data)` already establishes witnesses-then-data ordering to match.
> Riskiest spot: `Theorems.lean:492-501`, whose `simp [ProverEnvironment.fromList]` calls currently
> rely on `data` being the closed literal `fun _ _ => #[]`. Note `LookupCircuit.lookupCircuit`/`.lookup`
> are `@[circuit_norm]`, so a new parameter changes the normal form every downstream lookup proof sees.

Clean has already scheduled this in a source comment (`WitnessGeneration.lean:20-24`) and has two
waiting consumers (`Examples/DataWitness.lean`, `Examples/FemtoCairo`). **Send it alone** — it is the
only queued change that rewrites load-bearing proofs, and mixing it makes fallout hard to attribute.

### U6 · `U64Expr` lacks signed division — **WITHDRAWN: the premise was false**

This entry said the missing `sdiv`/`srem` meant "DivRem's populate cannot be expressed and that chip
stays on the `.native` escape hatch. Blocks cutover wave **W6**." That is wrong, and it is worth
saying why, because the entry would otherwise send someone to build an upstream feature we do not
need.

**Signed division *is* the sign/magnitude construction over the unsigned ops the sort already has.**
Lean core defines it that way — `BitVec.sdiv` is a four-case match on the operand msbs, each arm
`udiv` applied to `.neg`-normalized operands, with `BitVec.sdiv_eq`/`srem_eq` as the equation
theorems. This repo had already proved half the reduction before the entry was written:

```lean
-- SP1Clean/Proofs/Chips/DivRemChip/Populate/Abs.lean, srem_eq_bvAbs
private lemma srem_eq_bvAbs {w : ℕ} (x y : BitVec w) :
    x.srem y = if x.msb = true then -((bvAbs x) % (bvAbs y)) else (bvAbs x) % (bvAbs y)
```

The `sdiv` twin is the same three lines with the sign as the *xor* of the two msbs. Negation is one
node (`x * (2^64 - 1)`, since every u64 op wraps), and the chip already commits the magnitudes and
signs as columns (`populateAbsC`, `populateBNeg`, …) — so this is the arithmetization SP1 itself
uses, not a reformulation invented to dodge the gap.

Three of the entry's own caveats invert under that encoding. `i64::MIN / -1` needs no special case
(`bvAbs intMin = intMin`, `bvAbs (-1) = 1`, negate → `intMin`, which is Rust's `wrapping_div`) — and
there is no signed primitive left to diverge on. The divide-by-zero `.ite` was already an outer
branch in the populate, before any `sdiv`. And the "no `Int` normalization set" objection is the
strongest argument *for* the magnitude form: it keeps everything in `ℕ`, where `u64Wrap` and `omega`
already work.

**Adding `sdiv`/`srem` upstream would not have unblocked DivRem** — the actual costs (the hint
encoding, now fixed; and the sheer volume against a ~14,000-line proof stack) are untouched by it,
and it would additionally have forced a wire-format version bump.

Kept as a record rather than deleted: the useful lesson is that a "missing primitive" ticket should
first check whether the primitive is *definitionally* the ops already present.

### U7 · `<Sub>.circuit.localLength` is syntactically distinct from `elaborated.localLength`

So `localLength_eq` never fires on it, forcing a second `circuit_localLength` `rfl`-lemma on every
composable operation and reader. Already globalized here from a per-chip workaround. Unsized.

### U8 · `ElaboratedCircuit` default field tactics are expensive or fail

`localLength_eq`'s `rfl` default whnf-unfolds `main` (~15s on a 17-op main); `channelsLawful`'s
default *fails outright* on channel-heavy mains. Omitting a field costs +63% to +132%, or an outright
`timeout at whnf`. The trap is that the defaults **succeed** on smaller files, so an untimed edit
reports a clean −2 lines while silently adding 60–130%. Unsized.

### U9 · Clean wraps field elements as `id (ZMod p)`

Which blocks `ring`'s instance synthesis (`IsRightCancelAdd (id (ZMod p))`); `clear_value` does not
help. Unsized.

### U10 · The witness-IR width question — **diagnosis first, do not submit**

`witnessIR (fields m)` emits `.witness (size (fields m))`, which is definitionally but not
syntactically `m`. `ToClean/Circuit/WitnessCombinator.lean`'s `witnessVectorIR` exists to avoid that,
after real breakage (3 `Faithful/` anchors, `Soundness/TypedMemorySelectors`, `exposedChannels_eq`).

> **The breakage was real; the cause may be misattributed.** `size` is already tagged
> `@[circuit_norm]` (`Provable.lean:39`) *and* `@[explicit_circuit_norm]` (`Explicit.lean:571`), and
> `ProvableType (fields n)` sets `size := n` — so a `simp only [circuit_norm]` path should unfold
> `size (fields 2)` to `2` and let `Nat.reduceAdd` collapse the offset. The leak can only bite where
> `size` is never unfolded: instance synthesis at reducible transparency, `dsimp only []`,
> `rfl`-closing a `localLength` goal, or a simp-ordering accident.

This decides both whether there is a Clean change here at all — a one-line
`@[simp, circuit_norm] size_fields` lemma may fix it at zero blast radius — and whether
`witnessVectorIR` can be **deleted** rather than upstreamed. Reproduce one stall and identify the
tactic that fails to unfold `size` before choosing. House rule: *ladder before you believe a cause you
found by reading code*.

If a combinator does turn out to be right, the minimal upstream shape is to inline
`witnessVectorProgram` so it emits the literal width; that breaks exactly one declaration (the
`inferInstanceAs` delegation at `Explicit.lean:361-363`), replaced by a 5-line explicit instance
modelled on `witnessVector`'s at `Explicit.lean:343`.

> **Sizing correction (2026-08-19): the lemma already exists upstream — with the wrong attribute.**
> PR #426's branch carries `@[grind norm] theorem size_fields (n : ℕ) : size (fields n) = n := rfl`
> in `Clean/Circuit/Provable.lean` (absent from `main`). `@[grind norm]` fires inside `grind` —
> which is what their `computable_witnesses` tactic uses — and **not** under
> `simp only [circuit_norm]`, which is precisely where our structural anchors stall. So the ask
> shrinks from "upstream a combinator" to "**also tag it `@[simp, circuit_norm]`**", and if that
> lands, `ToClean/Circuit/WitnessCombinator.lean` is *deleted*, not upstreamed. The house rule
> still applies before filing even that: reproduce one stall and name the tactic that fails to
> unfold `size`, because `size` is already `@[circuit_norm]` and it is not yet established that our
> stalls were ever attributable to this lemma's absence rather than to narrower `simp only` lists.

### U11 · `WitgenIR.share` — subterm sharing for serialized witness programs — **landed in the fork**

The wire format has always had `steps`/`localVar` sharing, but nothing produced it: the serializer
walked the authored expression trees verbatim, and production-scale programs re-expand every shared
subterm. At SP1 scale that is fatal — DivRem's two heaviest witness ops serialized to 552 MB each,
1.22 GB for the chip; with the pass the same chip is **1.04 MB** (1143×), Mul 1.86 MB → 201 KB, and
the whole 25-chip export is ~2.3 MB, byte-stable.

Branch `witgen-share`: **2 commits off the upstream base `0e53b9f2`, no AgreesBelow contamination**
(`410ffba8` the pass, `4a9c2c7b` the proof). Footprint: `Clean/Circuit/WitnessShare.lean` (new,
+2173 — hand-written mutual `beq`/`hashCode`, an untrusted-cache intern that re-verifies every hit
against the steps array so the proof never reasons about `HashMap` internals, and the kernel-checked
`WitgenIR.eval_share` at `[propext, Classical.choice, Quot.sound]`) and
`Clean/Circuit/WitnessExport.lean` (+29/−6: `witgenJsonList?` factoring, `FlatOperation.share`, the
new entry point `Operations.witgenJsonShared?`). The proof caught a real bug during development: a
shared `.letU .idx` step substituted into `mapRange` bodies would re-bind `idx`, so `shareU`
rewrites `.idx → .const 0` in shared positions.

Both PR riders are **on the branch** (2026-08-18): `86f35a74` adds the scoped
`Witgen.instHashableOfVal` canonical-value `Hashable` instance (so `witgenJsonShared?` is callable
stock — until the re-pin, `scripts/witgenExport.lean:55` keeps its local copy), and `d8a2dc36` adds
`doc/witgen-wire-format.md` (adapted from this repo's spec — upstream has no wire format spec at
all; `doc/witgen-authoring.md` covers only the authoring surface, and its dangling
`witgen-ir-plan.md` pointer is fixed in the same commit). Ready-to-file issue/PR texts:
`upstream-drafts.md` (posting is owner-gated). **This is the single Clean-side prerequisite for the
exported artifacts to be producible from stock upstream Clean** — U1 is orthogonal to the exporter
path.

> **Re-scoped 2026-08-19, after reading upstream's live line** (see "Clean's direction" above).
> Three changes to how this gets filed:
>
> 1. **The framing moves from JSON size to generated-Rust size and speed.** #446 retires the JSON
>    *interpreter*, but their codegen renders each `Witgen.Step` one-for-one as `let local_N: F = …`
>    and does **no CSE at all** — so the pass buys them exactly what it buys us, on the path they
>    are actually building. The `doc/witgen-wire-format.md` rider is dropped from the PR (it stays
>    ours), and the #404 interpreter offer is withdrawn.
> 2. **The rebase target is their live branch, not `main`.** Stacking on feature bases is
>    idiomatic there (several merged PRs target `halo2-clean-2` / `agent/*`), and rebasing onto
>    `agent/fixed-columns-prover-data` is what demonstrates the pass against the IR they now have.
> 3. **The rebase debt is real and is the work**, not a formality:
>    - three new `FExpr` constructors — `.index`, `.listGetAtIndex`, `.proverInputGet` — need
>      `shareF`/`remapF` cases, `beq`/`hashCode` arms, and matching spec cases;
>    - `evalSteps` gains `idx` and `proverInput` parameters, threading through the ~8 step lemmas
>      and `eval_share`;
>    - **the `idx` question must be answered, not papered over.** Our `shareU` rewrites
>      `.idx → .const 0` in shared positions, justified because every position the traversal
>      reaches evaluates at `idx = 0`. #446 adds `RowProgram`, whose steps evaluate at
>      `idx := row`, and `.index`/`.listGetAtIndex` are idx-dependent for the same reason. The
>      premise survives for `WitgenIR` (`witnessBlockToRust` still passes `"0u64"`) but not for row
>      programs. Either intern only idx-independent subterms or thread the index — and if row
>      programs prove deep, ship the pass *restricted to `WitgenIR`* with the restriction stated
>      and proved, rather than an unsound generalization.
>
> The strongest available demo is wiring `share` into `Lower.lean`'s `lowerWitness` before its
> existing `witnessProgramWellFormed` check — which then simply re-runs on the shared program, so
> the integration costs no new proof obligation — and showing the generated-Rust delta on a
> duplication-heavy gadget from their own tree.

> **FILED 2026-08-19 as [#453](https://github.com/Verified-zkEVM/clean/pull/453) (draft)**, from
> `dtumad/clean:witgen-sharing-pass` onto `agent/fixed-columns-prover-data` @ `89e9abec`. The rebase
> was textually clean; the work was the ten `Missing cases` the three new `FExpr` constructors
> opened across `shareF`/`remapF`/`hashCode`/`scoped`/`beq`/`beq_eq`/`scoped_mono`/
> `eval_congr_locals`/`shareF_spec`/`remapF_scoped`/`remapF_spec`. `eval_share` is still
> `[propext, Classical.choice, Quot.sound]` on the new base, and the full `lake build` is green
> (1859 jobs).
>
> **The `idx` question, answered.** `.index` and `.listGetAtIndex` are frozen at the step context's
> `idx = 0` (`FiniteField.fromNat 0 = 0` is `@[simp, circuit_norm]`; `.listGetAtIndex xs` is
> definitionally `evalList _ 0 xs` there, i.e. `.listGet xs (.const 0)`), which is exactly the
> pre-existing treatment of `shareU`'s `.idx`, and is forced by the same mechanism: `oldRefF`/
> `oldRefU` substitute whole expressions into `mapRange` bodies, which re-bind the index.
> `.proverInputGet` is index-independent and interns normally. **`RowProgram` is deliberately not
> claimed** — its steps evaluate at `idx := row`, so sharing one would need the index in the
> interning key. The PR states the restriction rather than generalizing it.
>
> **The measurement changed the design.** Wired into `lowerWitness`, unconditional sharing made
> `export_femtocairo_flat_air_rust` **larger** (46,812 → 48,832 bytes). Cause, measured over their
> gadgets: Clean's hand-authored programs have essentially no recoverable duplication, because
> `witnessProgram`/`←` already hoists what is worth hoisting. `Keccak256.Permutation` 272,736 →
> 596,970 nodes (162,180 single-use hoists, +2 nodes each); `Xor64` 49 → 145; `IsZeroField` 16 → 24.
> So the PR adds `WitgenIR.shareIfSmaller` — keep the rebuilt program only when it is syntactically
> smaller — with `eval_shareIfSmaller` closing on either branch (`eval_share`, or `rfl`). Both
> `export_*_rust` outputs are then **byte-identical** to pre-PR. The honest pitch upstream is a
> safety net for *generated* witness programs, not an improvement to the circuits they author.
> The finer per-subterm policy (hoist iff used ≥ 2×) is blocked by `OkF.atom`: the pass would have
> to return non-atomic terms, which is what makes `remapF`'s index-independence argument work. That
> is recorded in the source as a follow-up.
>
> Still unposted: the #450 nudge in `upstream-drafts.md` (Draft 1) — `gh pr comment` is blocked by
> the local permission classifier, so it needs the owner to post it.

## Design discussion, not a patch

**`circuit_norm`'s struct-eval orientation.** Clean's normal form pulls projections *up* out of `eval`
(`ProvableStruct.eval_eq_eval` is `↓ high`, and `StructEvalSimprocs`' lift simprocs rewrite
`eval env (s.f)` to `(eval env s).f`). Consumers repeatedly want the other direction, and the two
orientations of one equation cannot both live in a confluent simp set. The evidence: this tree carries
**303 occurrences of `← ProvableStruct.eval_eq_eval` / `← ProvableType.getElem_eval_fields` across 33
files**, all manually undoing the chosen normal form. That number is worth showing Clean's maintainers,
but it is a conversation to open, not a patch to send.

> **Upstream got there first, and with a better answer (2026-08-19).** Draft PR #451 ("Confluent
> vector/struct eval layer — discriminated literal/atom simprocs", updated 08-16) replaces the
> unconditional `eval_vector`/`eval_fields` membership in `circuit_norm` with a *discriminated*
> design: `vectorEvalLiteral` handles constructed subjects (inward), `vectorAtomLift` handles
> opaque-rooted subjects (outward). So the two orientations do not have to fight for one simp set —
> they apply to syntactically disjoint subject classes. Our census is therefore **corpus evidence
> for #451**, not a new problem statement; the useful contribution is which orientation consumers
> actually reach for, on 303 real sites.

## Not a Clean matter

`ToClean/Tactic/GetElemFastPath.lean` is misfiled by intent: it shadows a `macro_rules` in Lean
core/Std (`Init/Data/Range/Polymorphic/GetElemTactic.lean`), and Clean neither defines nor touches it.
Not worth a third top-level library for 24 lines; its docstring names the real upstream.
