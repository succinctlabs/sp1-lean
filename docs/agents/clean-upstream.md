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
`ComputableWitnesses` composition lemmas), `Circuit/WitgenCongr` (`WitgenIR.eval_congr`),
`Circuit/InteractionRecovery`, `Circuit/WitnessCombinator` (`witnessVectorIR` — but see U10), and
`Tactic/GetElemFastPath` (whose upstream is Std, not Clean — see the last section). Everything here
must have live importers; an upstream-destined addition with no call site belongs in this document
as a snippet, not in the build (see U2).

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
| Pinned rev | `8301b77ac14f3463c7c1b016915b13e32328f7b6` |
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
| `agreesbelow-data-hint` | U1 — `AgreesBelow` constrains `data`/`hint` | *not yet filed* | in `sp1-integration` |

## The queue

Ordered by leverage, not by size. Each entry records what it unblocks and the measurement behind it,
because two of them looked obvious on a code read and turned out to need a different fix than the one
I first specified — see the "sizing correction" notes.

### U1 · `ProverEnvironment.AgreesBelow` should constrain `data` and `hint` — **landed in the fork**

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

**Payoff here**: makes `WitgenIR.eval_congr` applicable at a chip's obligation for the first time,
retiring five bespoke per-gadget congruence lemmas and all five `-Witgen.u64Wrap` disable sites.

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

### U3 · `u64Wrap` should fail cheaply

`Clean/Circuit/WitnessIR.lean:252`, registered as `simproc u64Wrap` and tagged `@[circuit_norm]`
globally. On any `n % 2^64` or `n % 64` it runs full `omega` against all local hypotheses; on failure
it returns `.continue` and the cost is discarded. In a *congruence* goal there are no bounds at all,
so every `%` subterm pays a complete failing `omega`.

**Measured**: ≥32×; still failing at eight times the default heartbeat budget; passing at a quarter of
the default with the simproc disabled.

> **Sizing correction.** The filter I first specified — bail when no local hypothesis mentions a free
> variable of the operand — is probably *low-yield*. In both real Clean consumers
> (`Gadgets/And/And8.lean:110`, `Gadgets/SHA256/Add32.lean:326`) the operand's free variables (`env`,
> or a field element `x`) appear in nearly every hypothesis, so the guard is satisfied trivially. The
> discriminating version is: bail unless some hypothesis is an **arithmetic comparison at `ℕ`/`Int`**
> whose fvar set meets the operand's. Two hard constraints: `Add32.lean:326` cites `Witgen.u64Wrap`
> **by name** in a `simp only` set, so the registration cannot be renamed; and over-pruning fails
> *silently* — a proof stops closing, far from the edit. **Add a regression example to
> `Clean/Utils/Test/TestU64Wrap.lean` in the `And8` shape** (bound stated over a field element's
> `.val`, not a `ℕ` variable) **before** touching the simproc. Orthogonal cheap win: when `n` is a
> closed literal, decide `n < m` directly instead of invoking `omega`.

Precedent for the style exists — `u64WrapSimproc` already has four syntactic bails, and
`evalProjectionSimproc` / `evalStructLiteralSimproc` are built the same way. What is new is
consulting `getLocalHyps` for a pre-decision; call that out in the PR.

Size **S** (1 file, 1 decl, 0 call sites). Blocks nothing once F1c retires our five disable sites.

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

### U6 · `U64Expr` lacks signed division

The u64 sort has unsigned `div`/`mod` but no `sdiv`/`srem`, so DivRem's populate cannot be expressed
and that chip stays on the `.native` escape hatch. Blocks cutover wave **W6**.

Plumbing is **S**: exactly two matchers to extend (`U64Expr.eval` at `WitnessIR.lean:171`,
`U64Expr.toJson` at `WitnessExport.lean:78`), no `deriving` clauses, 0 call sites broken, and the
existing `#witgen_json` goldens do not change (a missing arm is a *compile* error, not a silent diff).

> **The real cost is semantic, not structural.** There is no `Int` normalization set analogous to the
> `UInt64.toNat_*` block at `WitnessIR.lean:211-217`, and `u64Wrap` only knows `ℕ` moduli, so every
> proof touching a signed op lands in unnormalized territory. The rounding convention must match Rust
> `i64` (`tdiv`, truncating toward zero) and `i64::MIN / -1` *panics* in Rust — a divergence hazard for
> the differential test. `BitVec.sdiv` returns 0 on a zero divisor while RISC-V `DIV` wants −1, so a
> gadget must wrap an `.ite`; and 64-bit sdiv **cannot** express `DIVW`/`REMW`. Finally, this is a
> wire-format change: bump `("version", 1)` at `WitnessExport.lean:169`.

Size **S** plumbing, **M** usable.

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

## Design discussion, not a patch

**`circuit_norm`'s struct-eval orientation.** Clean's normal form pulls projections *up* out of `eval`
(`ProvableStruct.eval_eq_eval` is `↓ high`, and `StructEvalSimprocs`' lift simprocs rewrite
`eval env (s.f)` to `(eval env s).f`). Consumers repeatedly want the other direction, and the two
orientations of one equation cannot both live in a confluent simp set. The evidence: this tree carries
**303 occurrences of `← ProvableStruct.eval_eq_eval` / `← ProvableType.getElem_eval_fields` across 33
files**, all manually undoing the chosen normal form. That number is worth showing Clean's maintainers,
but it is a conversation to open, not a patch to send.

## Not a Clean matter

`ToClean/Tactic/GetElemFastPath.lean` is misfiled by intent: it shadows a `macro_rules` in Lean
core/Std (`Init/Data/Range/Polymorphic/GetElemTactic.lean`), and Clean neither defines nor touches it.
Not worth a third top-level library for 24 lines; its docstring names the real upstream.
