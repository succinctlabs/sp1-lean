# Handoff: per-shard completeness + soundness for an honest SP1 model

**Audience: us, on another machine, with no context.** Written 2026-08-24, at the end of the
August provider-closure/hand-off arc (branch `dtumad/provider-closure`, 31 commits).

Read [`overview.md`](../overview.md) for orientation; this file assumes it. What follows is a
decision log: what is proved, what is assumed and why, what is open, and which mistakes cost real
time. The architectural argument that came out of this arc is separate:
[`../proposals/bus-representation-consolidation.md`](../proposals/bus-representation-consolidation.md).

## 1. What the program is

Two theorems about one shard, in opposite directions, and the gap between them.

**Soundness** — `supported_core_native_sound` (`SP1Clean/Soundness/AIR.lean:972`). Closed.

```
WitnessRelation.Sound (SupportedCoreNativeRelation p) (SupportedCoreLocalExecutionRelation model)
```

Any witness the native relation accepts yields a genuine shard-local Sail execution.
`sorryAx`-free; carries the Sail platform hooks and `bv_decide` constants its 25 bridges retain.

**Completeness** — `sp1Ensemble_statement_of_structural_balance`
(`SP1Clean/Soundness/AIRCompleteness.lean:339`). Conditional.

```
(statement) (trace) (wf : WellFormed) (fit : CountsFit) (hsupply : SuppliesDemand)
(hnonpos) (stateKeys memoryKeys) (hstate) (hmemory) (hlen) (publicEq)
  → (sp1Ensemble p).Statement statement.publicValues
```

A well-formed generated trace assembles into a witness whose channels balance, hence into the
ensemble's public statement.

**The gap, stated honestly.** Completeness starts from a *generated trace*, not from an arbitrary
Sail execution. The file says so itself (`AIRCompleteness.lean:8–14`): *"this theorem validates the
AIR assembly performed by a trace generator, but it does not construct that trace from an arbitrary
Sail execution."* The generator side reaches only ALU: `sailRun_addTable_constraints` /
`sailRun_subTable_constraints` (`Proofs/Completeness/AluGeneration.lean`) over
`aluStepsFrom` (`FormalModel/TraceGen/SailAlu.lean`). Two chips of twenty-five.

**"Honest" means:** every premise is either (a) a caller obligation a real prover genuinely owes, or
(b) named as a residue in §2. Not: "the theorem has few hypotheses."

## 2. State of play

### Proved

| Thing | Where |
|---|---|
| Soundness capstone | `Soundness/AIR.lean:972` |
| Two structural bus mechanisms, separated | `Soundness/AIRCompleteness.lean:161` (closure), `:193` (hand-off) |
| Hand-off algebra, `[propext]` only | `Model/InteractionBus.lean` — `chainLedger_perm_handoff`, `multiChainLedger_perm_handoff` |
| Byte+Program closure balance | `Proofs/Completeness/ClosureRealization.lean:677` `byteProgram_balanced` |
| State hand-off from the chip ledger | `Proofs/Completeness/ChipLedger.lean:287` `stateLedger_perm_handoff` |
| Memory hand-off | `ChipLedger.lean:365` `memoryLedger_perm_handoff` |
| Bus ledger = channel ledger (both buses) | `ChipLedger.lean` — `stateLedger_eq_channelLedger`, `memoryLedger_eq_channelLedger` |
| 8 provider tables' Clean accesses | `Proofs/Completeness/ProviderTables.lean` |
| Window-crossing bumps are *events*, spec'd | `FormalModel/TraceGen/Bump.lean` — `stateBump_spec`, `memoryBump_spec` |
| ALU generator + its constraint theorems | `FormalModel/TraceGen/{GenState,AluGenerator,SailAlu}.lean`, `Proofs/Completeness/AluGeneration.lean` |

### Assumed — and legitimately so

These are obligations a real prover owes. Do not treat them as debt.

- **`hlen`** — `∀ channel, (interactionsWith channel).length < p`. The shard-size bound. Clean's own
  `.lake/packages/Clean/Clean/Air/Balance.lean:25` carries the same guard; it is what makes
  field balance imply ℤ balance.
- **`WellFormed`** (36 fields, `Proofs/Completeness/Assembly.lean:172`) — the generator's contract.
  Each field is a promise about the trace it built.
- **`CountsFit`** — provider multiplicities fit the field. Same character as `hlen`.
  `CountsFit.providerMultiplicitiesFit` coerces it to the older predicate; see §4.
- **`publicEq`** — the trace's public input is the statement's. Definitional plumbing.

### Assumed — residues. These *should* be theorems.

| Residue | Where | Why it is open |
|---|---|---|
| `hbinary` (`is_real ∈ {0,1}` on decoded rows) | `ChipLedger.lean:203`, `:288`, `:376` | The seam. Completeness *built* these rows; `RTypeEvent.toAddInputs_is_real` (`FormalModel/TraceGen/Inputs.lean:393`) gives `is_real = 1` by `rfl`. Nothing carries that across `Array (ZMod p)`. |
| `ConsumersOnlyPull` → `hnonpos` | `ChipLedger.lean:419`, discharged by `:427` | Byte-bus polarity. Program's counterpart *is* proved 25/25 (`Soundness/TypedProgram.lean:717`); Byte's is not. Needs a per-chip subcircuit traversal — `Proofs/Completeness/Closure.lean:20–32` describes it and declines. No upstream idiom exists (§3). |
| `hchain` / `hregroup` (Memory) | premise of `memoryLedger_perm_handoff` | Regrouping the emitted ledger into per-location chains is a fact about a *particular trace*, not about any chip. Consolidation will not make it derivable. |
| `hstate` / `hmemory` at the capstone | `AIRCompleteness.lean:345–348` | **Provable today. Not wired.** See §5 item 1. |

### Open

- **23 of 25 chips have no generator.** Only Add and Sub.
- **No completeness-side registry.** `Proofs/Completeness/Assembly.lean:231`'s `tables` is a hand-written 53-element
  literal choosing `Table.build` vs `Table.buildHinted` by hand. Soundness derives everything from
  `supportedChips.map`. They agree by `rfl` (`tables_map_component`, `:309`) — reorder the literal
  and it breaks.
- **The soundness/completeness seam.** `Component.rowInput_buildRow` (`ToClean/Air/TableBuild.lean:214`)
  closes the `Inputs` half generically. **`rowOutput_buildRow` does not exist** — grepped across
  `ToClean/` and `.lake/packages/Clean/` — so nothing characterises the *general* `Cols` after
  `buildRow` except the circuit's own `Spec`. That turns out not to block the seam: the part the bus
  ledger reads is `rfl` via `directOutput_eq`. See next action 6.
- **`decode` width.** `Model/SailDecode.lean`'s eighteen witnesses are each one hard-coded 32-bit
  word. The program quantifier's width is a separate decision.

## 3. Decisions taken, with reasons

Recorded so they are not relitigated.

**`active`, not the raw ledger, in the hand-off obligation.** `stateLedger` includes padding rows'
multiplicity-0 accesses; `handoff` emits only ±1. So `stateLedger.Perm (handoff keys)` is **false for
any padded trace**. Both halves are witnessed, not argued:
`SP1CleanTest/Audit/ActiveTraceNonVacuity.lean` builds `activePaddedTrace` (one JAL padding row) and
proves `activePaddedTrace_stateHandoff_raw_false` *and* `activePaddedTrace_stateHandoff` by
`native_decide`.

**Per-key sums (`SuppliesDemand`), not list equality (`ClosureRealized`).** The first attempt required
the provider list to match the demand list. A JAL shard emits nine unit-multiplicity range-16 rows
where the closure aggregates them into one `⟨0,9⟩`. Both are honest providers. `ClosureRealized` was
replaced by `SuppliesDemand` (`ClosureRealization.lean:644`), which compares per-key sums.

**Two mechanisms, not one.** Byte/Program *close* (providers supply aggregate demand — needs `Nodup`,
nonpositivity, coverage). State/Memory *hand off* (tokens created once, consumed once — needs **no**
side condition). Forcing a uniform treatment is what made the earlier attempts long.

**Bumps are events, not rows.** Phase 2 changed `SupportedCoreTraceWitness`'s bump fields from row
lists to `StateBumpEvent`/`MemoryBumpEvent` (`FormalModel/TraceGen/Bump.lean`), so their `Spec` is a
theorem rather than a generator promise. **`verification-report.md` §7.4 and `roadmap.md` P3 are stale
on this** — they still describe bump rows as assumed input lists.

**`decode` kept abstract.** Widening the program quantifier is orthogonal to bus balance; mixing them
would have made both harder.

**Memory's per-row terms kept folded.** Unfolding them triggers the `whnf`-into-expensive-values
failure mode Clean documents (`doc/performance-problems.md`). See `circuit_output_fold` in memory.

**The ten-family assembly was abandoned.** Three builder-specific State-ledger forms were written
before the row-level one that subsumes them; they were deleted rather than kept as near-duplicates.
Repeatedly, estimated 25-wide sweeps turned out unnecessary because a registry-wide fact already
existed — `supportedChip_stateEmissionShape` (`Soundness/TypedState.lean:703`),
`typedEnsembleStateInteractions_eq` (`TypedState.lean:865`),
`typedEnsembleMemoryInteractions_eq` (`TypedMemoryBalance.lean:174`).
**Look for the registry-wide fact before starting a sweep.**

## 4. Corrections and traps

Each of these cost time. They are recorded so the next reader does not pay again.

**`omega` and the hand-off residue — I was wrong twice.** I reported that `omega` did not close the
residue and recorded it so it would not be retried. That report was worthless in both directions: the
run where `omega` appeared to succeed had a `sorry` from an overlapping edit; the run where it failed
was against an un-normalized goal. **Neither run was evidence.** If you need to know, re-measure on a
clean tree.

**I reproved a lemma that was one import away — `signedVal_neg`.** In `active_stateLedger_eq`
(`ChipLedger.lean:202–276`), lines `:243–271` build a local `hneg` for the *binary-only* case of
`signedVal (-x) = -signedVal x` and then thread it through two hand-written
`rw [show … from List.flatMap_congr …]` blocks. `signedVal_neg`
(`Model/InteractionProjection.lean:80`) already proves it for **every** `x`, no binarity, and the
module is in scope — `signedVal_neg_is_real` is used four lines away. ~28 lines should collapse to
`simp only [signedVal_neg hp]`. Check for the general lemma before writing the special case.

**The composition blocker was `List.map_cons`, not the projection.** The goal held
`List.map (fun x => toAccess x.raw)` over `TypedInteraction` structure literals. The `.raw` projection
could not fire because `List.map` never distributed. Adding `List.map_cons` / `List.map_nil` to the
simp set fixed it. `toAccess_pulledIfValue` / `toAccess_pushedIfValue` are deliberately **not**
`@[simp]` — they fire only where wanted.

**The Clean polarity shortcut does not exist.** I proposed deriving `ConsumersOnlyPull` from "a channel
in `channelsWithGuarantees` but not `channelsWithRequirements` is only pulled." Reading
`Subcircuit.ChannelsLawful` shows those lists record guarantee/requirement *obligations*, not polarity.
More broadly: `grep -rn "IsPush\|IsPull\|Direction\|polarity"` over `.lake/packages/Clean/` returns
**zero hits**, and the one upstream attempt at an explicit direction token (PRs #337/#339,
`Direction::Send`) was **closed unmerged**. There is nothing to adopt.

**`byteSend` is pre-flip.** `Soundness/ByteConsistency.lean:60` uses multiplicity `+is_real` — a
*send*. Circuits emit `byteChannel.pullIf` (`−is_real`) after W11. There is no `byteLookups_eq_emitted`
and at that sign it would be **false**. `Model/Channels.lean:83` nonetheless claims the byte pull "is
discharged from bus balance (`byteAccessValid_of_balance`)" — **that claim is unbacked**; the premise
of `byteAccessValid_of_balance` (`ByteConsistency.lean:123`) is not derivable from the live bus,
because `isConsistentBalanced_map_negMult` (`Model/InteractionBus.lean:308`) needs the *whole* list
negated and only the consumer half is.

**Memory is stale by the same W11 flip as Byte, and that had gone unremarked.**
`memoryLookups` (`MemoryConsistency.lean:55`) emits op_a read-prior at `+ir` and the write at `−ir`
(`:67–75`); the live reader (`Native/Readers/ALUTypeReaderImmutable.lean:69–74`) pulls the read-prior
(`−is_real`) and pushes the read-back (`+is_real`) — exactly inverted. It also gates op_c additively
(`is_real - imm_c`) where `memoryLookups` gates multiplicatively. `MemoryGlobal.lean` and all of
`MemoryIsU64.lean` are built on the stale one. Separately, `MemoryIsU64`'s conclusion is superseded:
`isU64` is now a per-row channel guarantee (`Model/Channels.lean:52`), proved by the pusher and
derived by the puller.

**`SP1Clean/Soundness/MemoryConsistency.lean:165–173` states a falsehood.** It claims `memoryLookups` (`:55`, pre-W11) and
`memoryReadLookups` (`:174`, current) are related by `negMult`-invariance. False three ways: 6 entries
vs 5 (the `rd` write lives in `Readers/RegisterWrite`), different gates (`is_real*(1−imm_b/c)` vs plain
`is_real`), and the provider half is not negated in any of the nine downstream premises. Also the
theorem named `memoryLookups_eq_emitted` (`:210`) is about `memoryReadLookups`. **No unsoundness** —
nothing in a capstone closure consumes any of it.

**`CountsFit` duplicates `ProviderMultiplicitiesFit`.** I introduced it. `CountsFit.providerMultiplicitiesFit`
is the coercion; the relationship is documented at the definition. Do not add a third.

**Naming collisions to know about.** `programAccess` already exists in `SP1Clean.Soundness` as an
unrelated `RowView` notion; the ledger one is `programRowAccess`. Range's `onlyChannel` is stated over
`component n hn` in `Ledger.lean` but `componentFor width` in the trace — `onlyChannel_rangeComponentFor`
restates it at the goal's spelling.

**Lean syntax traps hit this month.** `omit` goes *before* the docstring, not between docstring and
theorem; and `omit` on a variable the statement references fails ("cannot omit referenced section
variable").

**Census discipline.** `scripts/run_audit.sh --update` refuses a dirty tree. Probe counts in
`docs/snapshots/axiom-ledger.md` must match the census (currently 863 main / 70 test / 933 released).
A guardrail hook blocks suppressing stderr on Lean script invocations.

## 5. Next actions, in dependency order

**1. Collapse the redundant `signedVal_neg` block. One file, ~28 lines, no restamp.**
`ChipLedger.lean:243–271` reproves a binary-only `signedVal (-x) = -signedVal x` and threads it by
hand; `Model/InteractionProjection.lean:80` has the general lemma. See §4. Do it first — it is the
cheapest thing here and it confirms the analysis is grounded in the code.

**2. Wire `ChipLedger` into `AIRCompleteness`. Also free.**
`Proofs/Completeness/ChipLedger.lean`'s only importer is `SP1Clean.lean:529`.
`AIRCompleteness.lean` imports `Assembly`, `Ledger`, `ClosureRealization`, `BalanceBridge`, `AIR` —
**not** `ChipLedger`. So `stateLedger_perm_handoff` and `memoryLedger_perm_handoff` are never composed
with `balanced_of_closure_and_handoff`, and `hstate`/`hmemory` stay free hypotheses of a capstone that
can prove them. Add the import (stratum 9 → 10, legal; `scripts/check_layering.sh` is the gate) or move
the two theorems down. **Corrects an earlier report of mine that said both buses "now feed
`balancedOn_of_handoff` directly" — they *can*; nothing wires them.**

**3. Add the orientation bridge (M3).** One lemma:
`tableNativeAccesses = (tableCleanAccesses …).map (negMult on Memory and Program)`. Joins the whole
`Faithful/` + `Composition/` family to `Proofs/Completeness/`. `negMult` and `perm_filter_by_kind`
(`Model/InteractionBus.lean:424`) exist to make it short. Argued in the proposal doc §P3.

**4. Retire the dead stratum.** ~2,400 lines, no re-proving — see the proposal doc §P2 for the list and
the two false claims it removes. Blocked on one decision: six live files cite `docs/bus-model.md`
section numbers for rationale, so either re-home that text or accept a historical doc outliving its
code.

**5. Fix the `kindOf` raw-arm divergence (~10 lines).** `Extracted.Interaction.toAccess`'s `.raw` arm
emits `InteractionKind.State` with a `"SP1Raw/…"` name, but `kindOf`
(`Model/InteractionProjection.lean:25–29`) falls back to `.Byte` for unrecognised names — so
`(keyOf a).1 = kindOf (keyOf a).2.1`, which every `filterKind` argument relies on, is false there.
Unreachable today (four channels only); unsafe because `.Byte` is the *fallback*. Proposal doc §P4a.

**6. Do the mechanical half of the seam (~450 lines).** The `Cols` question is answered: the general
`Cols` is constrained only by `Spec`, but the part the bus ledger reads is free — `rowInput_buildRow`
closes the `Inputs` half generically, and the `is_real`/state/adapter passthrough is `rfl` via the
`directOutput_eq` family (31 files carry one). Only control-flow `next_pc` needs `Spec`, which
`buildRow_spec_requirements` (`ToClean/Air/TableBuild.lean:280`) already delivers at a built row.
Worth doing on its own merits: it restates the hand-off premise over *events* instead of over an
opaque `decodeRow` of a `buildRow`, which is the difference between an auditor being able to read it
and not. Proposal doc §P5.

**7. Then either** extend the generator past Add/Sub, **or** do the `SupportedChip` registry work.
The genuinely hard remainder — discharging `IsHandoffChain` from a `SailChain` over events, and
Memory's `hregroup` — is the deferred mathematics and deserves its own budget (plausibly 1,000–1,700
lines together). Do not fold it into the same pass as item 6.

## Corrections owed to existing docs

Named here, not fixed — each needs its owner's judgement.

| Doc | Correction |
|---|---|
| `docs/verification-report.md` §7.4 | Bump rows described as assumed input-row lists. They are events now; the rows are derived. |
| `docs/roadmap.md` P3 | Same staleness. |
| `SP1Clean/Model/Channels.lean:83` | Claims the byte pull is discharged by `byteAccessValid_of_balance`. Unbacked (§4). |
| `SP1Clean/Soundness/MemoryConsistency.lean:165–173` | Prose states a false relation (§4). |
| `docs/agents/clean-upstream.md` | `ToClean/` resident inventory is missing four files. |
