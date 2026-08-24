# Proposal: consolidate the bus-representation layer

**Status: proposal, 2026-08-24. Not current status** — that is
[`architecture.md`](../architecture.md). **Not a work queue** — that is [`roadmap.md`](../roadmap.md).
This document argues one thing: that the bus/ledger layer carries too many partial representations of
one object, says which of them are essential and which are not, and costs the consolidation.

## Why now

Closing State and Memory bus balance took five sessions in August 2026. Almost none of that time went
into mathematics. The two theorems that carry the content —
`LookupAccessList.chainLedger_perm_handoff` and `multiChainLedger_perm_handoff`
(`SP1Clean/Model/InteractionBus.lean`) — depend on `[propext]` alone and are a few dozen lines each.
Around them sit `busLedger_eq_channelLedger`, `tableCleanAccesses_filterKind`,
`multiplicitySum_filterKind`, `toAccess_pulledIfValue` / `_pushedIfValue`, `active_append`,
`active_flatMap_gatedPair`. Every one of those is pure translation between representations of the same
multiset.

That ratio is the symptom. This document is the diagnosis.

## The thesis

> The four-object design rule is correct at the **chip** boundary. It has propagated to the **bus**
> layer, where the objects are not four different things but one multiset seen through projections —
> and there it produces bridges instead of clarity.

`architecture.md` § "Design rule" says: *"This produces four distinct objects: a proof-oriented native
Clean circuit; a semantic chip contract; a complete extracted Rust AIR oracle; and a Sail instruction-step
theorem. No one of these objects is silently treated as another."*

That is right, and it is why the chip layer is auditable. But "do not silently treat X as Y" has two
readings. At the chip boundary it means *these are genuinely different objects, keep them apart*. At the
bus layer it has been read as *give each view its own definition* — and a view that is definitionally the
same object does not become safer by being redefined. It becomes a bridge obligation.

## The measurements

Two kinds of number below. **Reproduced** ones come with the command that produces them, run on this
tree at `dtumad/provider-closure`. **Estimated** ones came from a survey pass and are labelled as
such — do not quote them as counts.

### Reproduced

| Measure | Count | How |
|---|---|---|
| `def`s whose declared result type is `LookupAccessList` | **41** | regex over `SP1Clean/`, `ToClean/`, `ToMathlib/` for `def NAME … : LookupAccessList :=`, excluding `.lake/`, `.claude/worktrees/`, `local-review/` |
| Fields in `SupportedCoreTraceWitness` | **59** | `Proofs/Completeness/Assembly.lean:86–157` |
| Fields in its `WellFormed` | **36** | `Proofs/Completeness/Assembly.lean:172–230` |
| Fields in `Composition.ExtractedInstructionRows` | **25** | `Composition/Ensemble.lean:49` |
| Constructors of the one table enum, `CoreProfile.Table` | **36** | `FormalModel/CoreProfile.lean:32` |

The 41 includes generic combinators that are *views* rather than producers (`active`, `filterKey`,
`handoff`, `linkAccesses`) — those are exactly what the proposal wants more of. The producers proper
are the ~30 that name a specific bus, table family, or orientation, and those are the target.

Three parallel hand-maintained 25-wide records is the sharpest number here: the trace witness, its
well-formedness predicate, and the extracted row bundle each enumerate the same 25 chips by hand, and
a fourth 25-arm dispatch (`FaithfulPropFor`, `Faithful/SupportedMachine.lean:106`) enumerates them
again over `CoreProfile.Table`. Adding a 26th chip means editing four places that nothing forces to
agree.

### Estimated — treat as direction, not as data

A survey pass over the interaction/ledger family put the distinct *carrier types* for "an emitted
interaction" at roughly a dozen, proved bridges between representations at around three dozen, and
per-chip declaration sites for `Add` alone in the low hundreds across ~14 groups. These were not
re-derived mechanically and the exact figures should not be cited. What survives scrutiny is the
shape: the bridges substantially outnumber the theorems that carry content, and that ratio is the
argument.

## Three classes, kept apart

The proposal is only credible if it does not claim every representation is waste. It does not.

### Class 1 — essential. Do not collapse.

**`SP1Clean/Model/BalanceBridge.lean`.** Clean balances *field* multiplicities with a
`length < ringChar` guard (`.lake/packages/Clean/Clean/Air/Balance.lean:25`); we balance
*signed ℤ* multiplicities via
`signedVal`. These are genuinely inequivalent for non-binary multiplicities, and the provider closure
**deliberately** emits aggregate counts — a Range provider row carrying multiplicity 9 is the normal
case. Clean has no ℤ layer to adopt: a grep of `.lake/packages/Clean/` for `trail`/`ledger` returns one
hit, in an SHA-256 comment, and Clean's per-key notion is `balanceOf ins msg : F`
(`.lake/packages/Clean/Clean/Air/Balance.lean:17`) keyed on `Array F`, with the channel *outside*
the key.

The asymmetry inside this bridge is also real and correctly handled: the soundness direction needs
multiplicities in `{0, ±1}` (`isConsistentBalanced_of_balancedInteractions`, `:151`); the completeness
direction does not (`balancedInteractions_of_isConsistentBalanced`, `:171`).

**The Rust-vs-Clean orientation**, for as long as the extracted oracle exists.
`Faithful/ChipOracle.lean:774`'s `nativeAccesses` dualizes Memory and Program with `negMult` because
SP1's Rust AIR *sends* where our native channels *pull*. That is a fact about SP1, not a modelling
choice. (See Class 3 for what should change about it anyway.)

### Class 2 — accidental. Collapsible.

Roughly a dozen carrier types (estimated — see above) where one canonical representation plus proved
views would do. The full inventory is long; the load-bearing observation is that `tableCleanAccesses`
(`SP1Clean/Model/CleanLedger.lean:36`) is already the natural primary — it is computable, it is in
Clean orientation with no dualization, and `List.filter` on it recovers every per-bus view. The
per-channel projections (`Table.interactionsWith`, `EnsembleWitness.interactionsWith`) are
`noncomputable`, which is the reason a bus-local obligation stated over them cannot be evaluated on a
concrete shard.

### Class 3 — stale, and in two places wrong.

This is the class the exploration found that the thesis did not predict.

## Finding 1 — about 2,400 lines of the bus layer are dead

Reached only by the root aggregator `SP1Clean.lean` and the test library — never by a capstone:

| Module | Verified by |
|---|---|
| `Soundness/ByteConsistency.lean` | only importer is `SP1Clean.lean:426` |
| `Soundness/MemoryConsistency.lean` (+ `MemoryIsU64.lean`, `MemoryGlobal.lean`) | importers are those two files and `SP1Clean.lean:434`; neither is in a capstone's closure |
| `Model/ChipAir.lean` | only importer is `SP1Clean.lean:326`; zero references to its declarations anywhere |
| `Soundness/ProgramProviderSpike.lean`, `Composition/ExactBalance.lean` | same shape |
| the *bus half* of `StateConsistency.lean` and `ProgramConsistency.lean` | every declaration except `StateAccess`/`stateAccess` and `ProgramAccess`/`programAccess`/`toRow` is referenced only inside its own file |

**Size, measured:** the seven whole files above are **1,899 lines** (`wc -l`); the retired bus halves
of `StateConsistency.lean` (374) and `ProgramConsistency.lean` (218) contribute most of a further 592.
Call it ~2,400.

*How the absence was checked:* `grep -rn "^import <module>"` across `SP1Clean/`, `SP1CleanTest/` and
`SP1Clean.lean`, then transitive closure of the importer set. A module whose closure is
`{SP1Clean.lean, SP1CleanTest.*, scripts.*}` is reached by the root index, the audit battery and the
axiom probe — and by no theorem.

`docs/bus-model.md`'s own HISTORICAL banner already named this stratum: *"the transitional
two-mechanism world (in-circuit channels + the `*Lookups` ℤ-shadows)"*. The migration that superseded
it landed; the shadows did not leave. Six live source files still cite that historical document's
section numbers for design rationale.

## Finding 2 — two stale sign conventions, and two false claims in the tree

Both stale models are stale *the same way*: they predate the W11 polarity flip. Byte was already
known; **Memory is the same defect, and had gone unremarked.**

**Byte.** `Soundness/ByteConsistency.lean:60`'s `byteSend` uses multiplicity `+is_real` — a *send*.
The circuits emit `byteChannel.pullIf`, i.e. `−is_real`, after the W11 polarity flip
(`Model/Channels.lean:83` states the flip; `Native/Chips/MemoryBumpChip/Defs.lean:55` et seq. show it
structurally). There is no `byteLookups_eq_emitted` — it is the only missing member of the `*_eq_emitted` family
(`grep -rn "_eq_emitted"` over `SP1Clean/` returns State `StateConsistency.lean:339`, Program
`ProgramConsistency.lean:173`, and Memory `MemoryConsistency.lean:210`/`:338`, and no Byte) — and
at the stated sign it would be **false**.

`Model/Channels.lean:83` nonetheless says the byte pull "is discharged from bus balance
(`byteAccessValid_of_balance`)". That claim is **currently unbacked**: the premise of
`byteAccessValid_of_balance` (`ByteConsistency.lean:123`) is balance of
`aggregateChipRows rows byteLookups ++ prov`, while the live bus gives balance of a list whose consumer
half is negated and whose provider half is not. `isConsistentBalanced_map_negMult`
(`Model/InteractionBus.lean:308`) requires the *whole* list negated, so the premise is not derivable.

**Memory — the same flip, and nobody had noticed.**
`SP1Clean/Soundness/MemoryConsistency.lean:55`'s `memoryLookups` emits op_a *read-prior* at `+ir` and
the *write* at `−ir` (`:67–75`). The live reader does exactly the opposite
(`Native/Readers/ALUTypeReaderImmutable.lean:69–74`): `memoryChannel.pullIf` for the read-prior —
which projects to `−is_real` — and `pushIf` for the read-back at `+is_real`. It also gates op_c
additively (`is_real - imm_c`, `:83`) where `memoryLookups` gates multiplicatively
(`is_real * (1 − imm_c)`, `:66`). So `memoryLookups` is stale by the W11 flip in the same way
`byteSend` is — and `MemoryGlobal.lean` and the whole of `MemoryIsU64.lean` are built on it.

`:174`'s `memoryReadLookups` is the current-polarity replacement, and it is **orphaned**: zero
references outside its own file. The file's prose at `:165–173` claims the two are related by
`negMult`-invariance. That is false for three independent reasons: **6 entries vs 5** (the `rd` write
lives in `Readers/RegisterWrite` and is absent from the second), **different gates** (multiplicative
vs additive, agreeing only on register rows), and the **provider half is not negated** in any of the
nine downstream premises that cite it.

There is a further reason `MemoryIsU64.lean` (332 lines) is dead weight rather than merely unreached:
its conclusion — values on the memory bus are `isU64` — is now a **per-row channel guarantee**,
`memoryChannel.Guarantees msg _ := MemoryMsg.isU64 msg ∧ MemoryMsg.ClkBound msg`
(`Model/Channels.lean:52`), proved by the pusher and derived by the puller. The trace-level limb-chain
argument reaches a strictly weaker version of something already available row-locally.

Also: the theorem named `memoryLookups_eq_emitted` (`:210`) is about `memoryReadLookups`.

**No unsoundness follows** — nothing in any capstone's closure consumes any of this. But four sign
conventions are being maintained for nothing, and two statements in the tree are wrong.

## Finding 3 — the August 2026 hand-off work is not wired in

`Proofs/Completeness/ChipLedger.lean` is imported only by `SP1Clean.lean:529`.
`AIRCompleteness.lean`'s imports are `Assembly`, `Ledger`, `ClosureRealization`, `BalanceBridge`,
`AIR` — **not** `ChipLedger`.

Yet `stateLedger_perm_handoff` (`ChipLedger.lean:287`) and `memoryLedger_perm_handoff` (`:365`)
produce exactly the shape `balanced_of_closure_and_handoff` (`AIRCompleteness.lean:223`) asks for.
They are never composed. So `hstate` and `hmemory` remain free hypotheses of
`sp1Ensemble_statement_of_structural_balance` (`:339`) **even though the repository can prove
them**.

This is an import-direction problem, not a mathematical one, and it is the cheapest correctness win
available anywhere in this document.

## Finding 4 — the soundness and completeness paths are joined by nothing

| Direction | Chain | Types |
|---|---|---|
| Completeness | `event → <Chip>.Inputs → List Inputs → Array (ZMod p) → Table → List Table → EnsembleWitness` | 7 |
| Soundness | `EnsembleWitness → List Table → Array (ZMod p) → DecodedInstructionRow → Environment → Inputs × Cols → ChipRow → RowView` | 8 |

They hinge on the bare `Array (ZMod p)`, and **no theorem crosses the hinge.**

- Completeness builds *from* `Inputs` and never constructs `Cols`; soundness reads *into*
  `Inputs × Cols`.
- `Component.rowInput_buildRow` (`ToClean/Air/TableBuild.lean:214`) closes the `Inputs` half
  generically. **`rowOutput_buildRow` does not exist** — checked by grep across `ToClean/` and
  `.lake/packages/Clean/`. Nothing characterises the *general* `Cols` except the circuit's own `Spec`.
  But see P5: the part of `Cols` the bus ledger actually reads is already `rfl`.
- The symptom is visible in code written this month: `ChipLedger.lean:203`, `:288`, `:376` assume
  `hbinary : is_real ∈ {0,1}` on the decoded rows of a trace *the completeness layer itself built*,
  when `RTypeEvent.toAddInputs_is_real` (`FormalModel/TraceGen/Inputs.lean:393`) gives `is_real = 1`
  by `rfl` two files away.
- The only proved instance in the tree is one chip, one field, one hardcoded event:
  `SP1CleanTest/Audit/ActiveTraceNonVacuity.lean:184`.
- There is **no completeness-side registry**. `Proofs/Completeness/Assembly.lean:231`'s `tables` is a hand-written
  53-element literal that chooses `Table.build` vs `Table.buildHinted` by hand; the soundness side
  derives everything from `supportedChips.map` (`Soundness/SP1Ensemble.lean:221`,
  `Soundness/ChipRegistry.lean:45`). The two agree only by `rfl` (`tables_map_component`,
  `Proofs/Completeness/Assembly.lean:309`) — reorder the literal and it breaks, and nothing forces them to be one list.

## What to do

Ordered by (value ÷ cost), highest first.

### P0 — delete a redundant 28-line proof block in `ChipLedger.lean`. One file, no restamp.

`active_stateLedger_eq` (`ChipLedger.lean:202–276`) is 75 lines, of which `:243–271` exist only to
turn `signedVal (-x)` into `-signedVal x`: a local `hneg` proving the *binary-only* case, then two
hand-written `rw [show … from List.flatMap_congr …]` blocks threading it.

**That work was unnecessary when it was written.** `signedVal_neg`
(`Model/InteractionProjection.lean:80`) already proves `signedVal (-x) = -signedVal x` for **every**
`x`, with no binarity hypothesis — its own docstring says so — and the module is in scope
(`signedVal_neg_is_real` is used four lines away at `:245`). Replacing `hneg` with `signedVal_neg hp`
should collapse `:243–271` to a single `simp only [signedVal_neg hp]`.

This is mine to correct: I wrote the block this month. It is listed first because it is the cheapest
concrete win in the document and it validates that this analysis is grounded in the code rather than
in a reading of it.

### P1 — wire `ChipLedger` into `AIRCompleteness`. Free.

Add the import, or move the two `perm_handoff` theorems below `AIRCompleteness`. Discharges two
capstone hypotheses with no new mathematics. **Cost: one import line plus a layering check.**

*Layering note:* `ChipLedger` is stratum 9 and `AIRCompleteness` stratum 10, so the import direction
is legal; `scripts/check_layering.sh` is the gate.

### P2 — delete the dead stratum. ~2,400 lines.

Retire `ByteConsistency.lean`, `MemoryConsistency.lean`, `MemoryIsU64.lean`, `MemoryGlobal.lean`,
`ProgramProviderSpike.lean`, `Model/ChipAir.lean`, `Composition/ExactBalance.lean`, and the bus half
of `StateConsistency.lean` / `ProgramConsistency.lean`. Keep `StateAccess`/`stateAccess` and
`ProgramAccess`/`programAccess`/`toRow` — all 25 chip bridges use them — and move them to
`Soundness/RowEffectDefs.lean`, where their consumers already live.

Delete outright with no replacement: `TraceLookupConsistent` (`InteractionBus.lean:249`), `byteLedger`
and `programLedger` (`ClosureRealization.lean:813`, `:817`) — each has exactly one reference, its own
definition.

**Cost: an import sweep and a root-index update. No re-proving** — nothing in a capstone closure
depends on any of it. **Benefit beyond line count:** it removes both false claims of Finding 2, which
cannot be fixed in place because the objects they describe are stale.

*Before deleting, resolve one question:* `docs/bus-model.md` is retained solely because source
doc-comments cite its section numbers. Six files do. Either re-home that rationale or accept that the
historical doc outlives the code it describes.

### P3 — add the orientation bridge. One lemma.

`tableNativeAccesses = (tableCleanAccesses …).map (negMult on Memory and Program)`. The two ledgers
(`Composition/Table.lean:86` and `Model/CleanLedger.lean:36`) differ *only* by that dualization; both
files describe the difference in prose and no lemma states it. `negMult`
(`InteractionBus.lean:~95`) and `perm_filter_by_kind` (`:424`) exist precisely to make this short.

This is the highest-leverage missing bridge: it joins the entire `Faithful/` + `Composition/` family
(Rust orientation) to the entire `Proofs/Completeness/` family (Clean orientation), and it makes the
composite orientation statable — today the Byte flip in `Extracted.Interaction.toAccess`
(`Extracted/InteractionModel.lean:88`) and the Memory/Program flip in `nativeAccesses` are reconciled
only *inside* each of the 25 `ChipFaithful` proofs, so a 26th chip has no statement to cite.

**Cost: one lemma, plus optional simplification of call sites.**

### P4 — state the canonical model: **two primaries, one bridge**, and gate it.

An earlier draft of this proposal said there should be *one* canonical bus representation
(`tableCleanAccesses`), everything else a view. **That is wrong, and a stress-test pass caught it.**
The two directions have inequivalent requirements:

- **Soundness must say "this pull's message *is* this row's state."** That needs typed
  `Message (ZMod p)` values — `statePullMessage` / `statePushMessage` are `StateMsg (ZMod p)`
  (`Soundness/TypedState.lean:52`, `:55`), and `StateEmissionShape` (`:94`) is stated in exactly that
  vocabulary and proved 25/25. Projecting to `List ℕ` first discards the structure the Sail bridge
  consumes.
- **Completeness must recount provider demand across 53 tables and must *compute* on a concrete
  shard.** `EnsembleWitness.interactionsWith` is `noncomputable`
  (`.lake/packages/Clean/Clean/Air/FlatEnsemble.lean:228`) because it decides `RawChannel` equality
  classically. `fullLedger` (`ClosureRealization.lean:613`) is a plain `def` over closed terms an
  evaluator reduces — which is what makes the `native_decide` shard anchors possible at all.

So the rule to state is:

> **Primary A (typed, soundness):** `TypedInteraction`, `typedEnsembleInteractionsWith`,
> `producedMessages` / `consumedMessages`.
> **Primary B (ℤ, completeness):** `LookupAccess`, `tableCleanAccesses` / `fullLedger`,
> `multiplicitySum`.
> **Exactly one bridge:** `Interaction.toAccess` (`Model/InteractionProjection.lean:114`), lifted to
> ensembles by `busLedger_eq_channelLedger` (`ChipLedger.lean:137`) and to Clean's field balance by
> `Model/BalanceBridge.lean`.
> Everything else is a view of A or B, or is retired.

The repository already *has* this shape — `busLedger_eq_channelLedger` is deliberately stated once for
an arbitrary channel because "writing it twice would have been the same proof with two names"
(`ChipLedger.lean:135–136`). The split was never the problem; the ten satellites around it were.

Add the rule to `architecture.md` and to `docs/layering.md`'s laws, where structural rules in this
repository are made checkable rather than aspirational.

**Cost: documentation, plus whatever P2/P3 leave.** The point is to stop the regrowth; without it the
next migration leaves another shadow stratum.

### P4a — fix the `kindOf` raw-arm divergence. ~10 lines, and it is a latent defect.

`Extracted.Interaction.toAccess`'s `.raw` arm (`Extracted/InteractionModel.lean:104–106`) produces
`(InteractionKind.State, "SP1Raw/" ++ kind.lookupName, …)`. But `kindOf`
(`Model/InteractionProjection.lean:25–29`) is a four-way `if` whose **fallback is `.Byte`**, so
`kindOf "SP1Raw/memory" = .Byte`, not `.State`. The invariant every `filterKind` / `preprocessedKey`
argument silently relies on — `(keyOf a).1 = kindOf (keyOf a).2.1` — is **false on the raw arm**.

Unreachable today: `sp1Ensemble.channels` is exactly four, and `exactPayloadKey` is confined to
`Composition/ExactBalance.lean`. But `.Byte` being the *fallback* means any fifth channel added
without editing `kindOf` becomes closure-selectable by default. It fails safe now because
`SuppliesDemand` would be unprovable — that is luck, not design.

**Fix:** give `kindOf` an explicit `"SP1Byte"` case and a distinguished failure otherwise, or record
the divergence in a `kindOf_toAccess_raw` theorem. Do this regardless of the rest of this document.

### P5 — the seam. The only proposal that would justify re-stating a capstone.

Give `SupportedChip` (`Soundness/SupportedMachine.lean:69`, 5 fields) the four things a completeness
generator needs and does not have: `computableWitnesses`, an event type, `traceInputs`, and a padding
row. Then `Assembly.lean`'s 53-element literal becomes a `supportedChips.map`, both directions share
one registry, and `tables_map_component`'s `rfl` becomes unnecessary rather than load-bearing.

**Cost, stated honestly:** it touches all 25 chips, the trace record, and the assembly proof; the
`WellFormed` structure's 36 fields would need re-expressing as a per-chip predicate carried by the
descriptor. This is weeks, not days, and it is the one item here whose payoff is structural rather
than immediate.

**The `Cols` question, now answered — and the mechanical half is much cheaper than the paragraph
above implies.** The general `Cols` is indeed constrained only by `Spec`. But the seam does not need
the general `Cols`; it needs the part the bus ledger reads, and that part is already free:

1. **The `Inputs` half is generic and done.** `rowInput_buildRow` (`ToClean/Air/TableBuild.lean:214`)
   gives `(chip.decodeRow data (buildRow input data hint)).inputs = input` for all 25 chips with no
   per-chip work, since `decodeRow.inputs := chip.table.rowInput env`
   (`Soundness/WitnessDecode.lean:34`).
2. **The State-relevant `Cols` half is `rfl`.** Every chip's `ElaboratedCircuit.output` passes the
   `is_real` / CPUState / adapter blocks through unchanged — `Native/Chips/AddChip/Defs.lean:71`
   with its `directOutput_eq` `rfl` lemma at `:86`, and the same shape across the chip and reader
   families (`grep -rl directOutput_eq` over `Native/Chips` + `Proofs/Chips` returns 31 files). Since
   `rowOutput env = eval env (output rowInputVar rowOffset)`, the passthrough identity is
   `simp only [circuit_norm, directOutput_eq]` at *every* environment — no witgen, no `Spec`.
3. **Only `next_pc` on the control-flow chips needs `Spec`,** and `buildRow_spec_requirements`
   (`ToClean/Air/TableBuild.lean:280`) already delivers `Spec` at a built row.

So the seam splits into a **mechanical ~450 lines** (items 1–3 plus aligning `decodedInstructionRows`
with `tables`) and the **genuinely hard remainder**: discharging `IsHandoffChain` from a `SailChain`
over events, and Memory's per-location `hregroup`. Those two are the deferred mathematics and deserve
their own budget — plausibly 1,000–1,700 lines together.

**Do the mechanical half on its own merits, before deciding on the full `SupportedChip` extension.**
It changes what the repository can *say*: today `stateInstrLinks` (`ChipLedger.lean:186`) is a
`noncomputable` function of a `decodeRow` of a `buildRow`, so an auditor cannot see what the hand-off
premise asserts. After it, the premise is about events.

## Upstream posture

Clean `main` has not moved since 2026-08-04; our fork base **is** `main`
(`gh api compare/0e53b9f2...main` → `ahead_by: 0, behind_by: 0`). All Air-layer work is on side
branches.

**Adopt now: nothing.** Clean has no ledger vocabulary to adopt, and — relevant to the residue left by
the Byte-polarity question — **no channel-polarity predicate**. `grep -rn "IsPush\|IsPull\|Direction\|polarity"` over
`.lake/packages/Clean/` returns zero hits. Polarity lives only in `Interaction.mult` and the
`assumeGuarantees : Bool` flag. The one upstream attempt at an explicit direction token
(PRs #337 / #339, `Direction::Send`) was **closed unmerged**. So the fact that
`ConsumersOnlyPull` (`ChipLedger.lean:419`) has no idiomatic derivation is not a gap in our modelling —
upstream tried and abandoned the same idea.

**Track, do not build on:**

- **PR #446** (draft, `agent/fixed-columns-prover-data`) adds "interaction-driven preallocated tables,
  with generated multiplicities derived from channel demand" — upstream's version of our provider
  recount — and moves `Clean/Air/WitnessGeneration.lean` +261/−136, the direction
  `ToClean/Air/TableBuild.lean` occupies. Re-read `TableBuild.lean`'s "Clean never builds a table"
  premise at the next pin bump; it is true at `0e53b9f2` and #446 is where it stops being true.
- **PR #454** (open, *not* draft) generalises `Component` with a `windowWidth` and adds
  `Clean/Air/Boundary.lean` — explicit first/last-row boundary assertions, **distinct from
  channel-encoded ones**. Directly relevant: our State bus encodes the shard boundary *inside* the
  channel (the verifier pushes init and pulls final), and #454 is upstream deciding that is not the
  only way.

The standing rule holds: a draft on a side branch is not a foundation.

## What this proposal does not solve

- **Byte polarity** (`ConsumersOnlyPull`). No upstream idiom exists; deriving it needs the per-chip
  subcircuit traversal `Proofs/Completeness/Closure.lean:20–32` describes and declines. Program is
  cheap (`supportedChip_programEmissionShape` is proved 25/25); Byte is not, and it should be costed
  on its own.
- **The Memory `hregroup` premise.** Regrouping the emitted ledger into per-location chains is a fact
  about a particular trace, not about any chip. Consolidation does not make it derivable.
- **Anything about `decode`.** The program quantifier's width is a separate decision
  (`Model/SailDecode.lean`'s eighteen witnesses are each one hard-coded 32-bit word).
