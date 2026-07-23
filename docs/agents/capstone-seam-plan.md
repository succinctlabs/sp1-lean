# Closing the capstone seam — implementation plan

The headline theorem `supported_core_native_sound` (`SP1Clean/Soundness/AIR.lean`) is axiom-clean except
for one dynamic-grounding **seam** and a handful of per-chip **admissions**. This document is the
dependency-ordered plan to close them, with the exact lemmas, file locations, and the design decisions
behind them. It is a *how-to-do-the-work* reference (in the spirit of [`porting-recipe.md`](porting-recipe.md)
and [`proof-patterns.md`](proof-patterns.md)); for *what the project proves today*, see
[`../release-audit.md`](../release-audit.md) and [`../roadmap.md`](../roadmap.md).

> Line numbers drift as files change — treat them as "look near here", and grep for the named declaration.
> Regenerate the authoritative sorry/axiom inventory with `scripts/run_audit.sh`.

## Goal and closure set

`supported_core_native_sound` becomes axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`)
once **1 seam + 6 chip admissions** close:

- **The seam** — `supportedCore_orderedRows_dynamic` (`Soundness/AIR.lean`), consumed by the capstone.
- **6 chip admissions** —
  - `DivRemChip.evidenceSoundness`, `DivRemChip.main_exposedChannelsLawful`,
    `DivRemChip.requirementsChannelsLawful` (`Proofs/Chips/DivRemChip/Formal.lean`);
  - `{DivRem, Branch, ShiftLeft}Chip.completeness`
    (`Proofs/Chips/{DivRemChip/Completeness/Driver, BranchChip/Formal,
    ShiftLeftChip/Formal}.lean`).

**Not in the set:** `sp1_decoded_rows_sound` (a different capstone chain) and `MulChip.completeness`
(already proved).

Because the seam and the admissions are all quantified over `sp1Ensemble`, and the ensemble transitively
references the DivRem circuit's still-open structural fields, **every** declaration over the ensemble
currently reports `sorryAx`. That residue disappears exactly when the six admissions close — it is not
introduced by any new seam work.

## What is already proved (do not rebuild)

The bulk of the machinery for the seam exists; the remaining work is *assembly*.

- `TimedGrounding.walk` (`Soundness/TimedGrounding.lean`) — the timed grounding engine, and all its input
  structures.
- The full aligned-carrier layer: `AlignsWith`, the three carrier transports
  (`localStepFact_align_of_ordinary`, `frameFact_align_of_ordinary`, `grounded_ordinary_of_aligned` —
  `TimedGrounding.lean`), `rowOK_alignedOf` (`Soundness/AlignedCarrier.lean`), `rowAligned_rtype` and
  `addChip_rowAligned` (`Soundness/GroundingAdapter.lean`).
- `ChipGroundingContracts.engineFacts` and `DecodedInstructionRow.dynamicGrounded_of_contracts`
  (`Soundness/ChipContracts.lean`).
- The State-axis trail: `pcWalk` / `clockCount` / `endpointBalance_of_decodedStateWalk` /
  `statePullTime_of_decodedStateWalk` (`Soundness/AIR.lean`).
- Boundary head-truth (`InitialBoundaryFacts.localStateTruth`) and the genesis `LiveOK`
  (`memoryInit_liveOK`, `Soundness/MemoryFrontier.lean`).
- `memoryFrontierBalance` + `initPure` / `finPure` + the provider-unique boundary fields
  (`Soundness/MemoryFrontier.lean`, `Soundness/ProviderBindings.lean`).
- `addChip_groundingContracts` — the first (of 25) `ChipGroundingContracts` bundle instance
  (`Soundness/ChipContracts.lean`).

## Track E — the seam

`walk` (`TimedGrounding.lean`) consumes, per batch of rows, seven inputs:

1. `LocalStepFact` per row,
2. `FrameFact` per row,
3. `RowOK` per row (an **upfront** input — see the refactor below),
4. head `LocalStateTruth`,
5. `LiveOK` genesis frontier,
6. the State multiset balance,
7. the per-location Memory balance,

and returns `Grounded` for each row. The seam feeds these, then transports each row's `Grounded` back to the
ordinary carrier and into `dynamicGrounded_of_contracts`.

### E1a — the source-register foundation and the `rowAligned` field · done

`rowAligned_rtype` needs the source-operand index bounds `op_b[0], op_c[0] < 32`. These are **not**
range-checked in-circuit anywhere: the Program bus's `ProgramMsg.RowSpec` / `ProgramProviderChip` bounds only
the *write* index `op_a` (`Model/ProgramChip.lean`, `Proofs/Chips/ProgramProviderChip.lean` — the source
indices are explicitly "unconstrained by RowSpec"). The honest provenance of the bound is therefore the
instruction *encoding*: the fields are 5-bit, so `< 32` follows from the decode.

Landed (`op_a/op_b/op_c` all decode-intrinsic):

- `regidxVal_val_lt` (`Model/Semantics/Decode.lean`) — every committed register index is `< 32` because it
  is a `BitVec 5`. Axiom-clean.
- `decodedInROM_rtype_operand_lt` (`Soundness/Decode.lean`) — from `decodedInROM prog row` + the opcode +
  `imm_c = 0`, concludes `op_a.val < 32 ∧ op_b[0].val < 32 ∧ op_c[0].val < 32`, via
  `decodedInROM.decodes` + `instrToProgramRow_inv_rtype` + `regidxVal_val_lt`. It carries only the
  already-disclosed Sail axiom `sys_enable_experimental_extensions` (the same one the capstone's static
  decode layer sits on — see [`../snapshots/axiom-ledger.md`](../snapshots/axiom-ledger.md)), and adds **no**
  boundary premise. This is strictly more faithful than threading the bound through the boundary relation,
  which would assume a fact that is in fact derivable.
- The `rowAligned` field on `ChipGroundingContracts` (`Soundness/ChipContracts.lean`, after `readiness`) — a
  chip-generic `∃ touches, <the 5-conjunct aligned bundle>`, matching `rowOK_alignedOf`'s consumer inputs;
  Add's instance is populated.

**Reuse for the rollout:** every R-type chip reuses `decodedInROM_rtype_operand_lt`; the immediate/U-type
shapes need `decodedInROM_{itype,utype}_*` twins (`instrToProgramRow_inv_itype` already exists in
`Model/Semantics/Decode.lean`).

### E1d — the Memory balance (walk input 7) · done

`memoryFrontierBalance` proves the per-location balance over `memoryFrontierRows` (the *ordinary* carrier in
`realDecodedInstructionRows` order); `walk` wants it over the **aligned** carrier of the exhaustive **ordered**
rows. The bridge is `memoryBalance_of_alignsWith` (`Soundness/ChipContracts.lean`, needs
`import SP1Clean.Soundness.MemoryFrontier`), built from four reusable multiset-invariance lemmas:

- `rowPushesAt_coe_eq_of_alignsWith` / `rowPullsAt_coe_eq_of_alignsWith` — per row, an `AlignsWith`
  push/pull `Perm` yields the same filtered multiset;
- `pushesAt_perm` / `pullsAt_perm` — the batch total is invariant under a permutation of the row list.

`memoryBalance_of_alignsWith` transports `memoryFrontierBalance` across the per-row align
(`List.map_congr_left`) and the exhaustive `Perm` (`exhaustive.map _`). (Gotcha: `memoryChannel` must be
written `Channels.memoryChannel` — `ChipContracts` does not `open SP1Clean.Channels`, and the unqualified
name leaves a stuck `ProvableType` metavariable.)

### The `rowAligned`-upfront refactor · in progress

`walk` takes `RowOK` as an **upfront** input, *not* a grounding output — the D0-design invariant is that
`RowOK` is currency-independent. But E1a's `rowAligned` field, as first written, takes
`DecodedRowOpenSoundnessInputs` and derives the full chip `Spec` via `chipSpec_of_openSoundnessInputs`, whose
memory `isU64` conjunct is **grounding-time** (the pull currency comes from the balance match, not from the
finished channels — `memoryChannelGuarantees_of_pullCurrency` needs the currency as a hypothesis). So the
field as written cannot feed the walk.

The fix is the intended design: `rowAligned`'s *output* (`TouchOK` / `IsChain` / the conditional `slot`) needs
only (a) `op_a/op_b/op_c < 32`, all decode-derivable, and (b) the register-access timestamp
`RegisterAccessCols.Spec`s, which are **Byte-bus derived** and available upfront from `byteG`. So
`addChip_rowAligned` / `rowAligned_rtype` / the field should take `byteG` + `decodedInROM` instead of
`openInputs` / `spec`.

Staged:

- **Stage 1 · done** — `decodedInROM_rtype_operand_lt` extended to `op_a` (= `regidxVal rd`); the
  `ChipContracts` caller destructures `⟨_opa_lt, opb_lt, opc_lt⟩`.
- **Stage 2 leaf · done** — `Readers.RegisterAccessTimestamp.bounds_of_byteGuarantees`
  (`Soundness/TypedTime.lean`, after `CPUState.bounds_of_byteGuarantees`): from the
  `RegisterAccessTimestamp` subcircuit's flat `byteG`, derives its two timestamp bounds
  (= `RegisterAccessCols.Spec`). Axiom-clean; a byteG-only leaf (the reader does only Byte pulls, no Memory).
  Gotchas: `RegisterAccessTimestamp.circuit` is a `FormalAssertion`, so use
  `FormalAssertion.toSubcircuit_interactions` (not `GeneralFormalCircuit.…`); its leading `assertZero` means
  the membership `simp only [circuit, main, circuit_norm, …, List.mem_cons]` closes without a trailing
  `tauto`.
- **Stage 2 navigation · remaining** — reach each of the three nested `RegisterAccessTimestamp` subcircuits'
  `byteG` from the chip row's whole-circuit `byteG`, apply the leaf, and wrap the results as
  `RegisterAccessCols.Spec`s over the row `view`. Two findings shape this:
  - The clean multi-level *structured* descent does **not** chain: `channelGuarantees_subcircuit_of_mem`
    yields `FlatOperation.ChannelGuarantees sub.ops.toFlat`, but a subcircuit's `.ops` is a
    `NestedOperations` (no `.ChannelGuarantees`), and the bridge `channelGuarantees_toFlat`
    (Clean `Circuit/Subcircuit.lean`) is over `Operations`.
  - The working route is a **direct extraction from the recursively-flattened interaction list**:
    `circuit_norm`'s `toFlat_subcircuit` and `interactions_subcircuit` (Clean `Circuit/Operations.lean`)
    flatten recursively, so all six register byte pulls (three columns × two checks) are present in the
    chip's / `RTypeReader`'s flattened interactions. Extract them with the leaf's byte-pull pattern applied
    six times at the flattened level, plus a `CPUStateTimeBinding`-style binding relating
    `view.adapter.op_x_memory` / `view.clk_low` to the `RTypeReader` input columns.
  - Estimated ~150–250 intricate lines. The nesting is `AddChip.main` (RTypeReader is a direct subcircuit) →
    `RTypeReader.main` (three `RegisterAccessCols` subcircuits) → `RegisterAccessCols.main`
    (`RegisterAccessTimestamp` subcircuit); the leaf is the innermost target.
- **Stages 3/4 · remaining** — rewire `addChip_rowAligned` / `rowAligned_rtype` / the field to drop `spec` /
  `openInputs` in favour of `byteG` (for the `hslots` timestamp specs) + `decodedInROM_rtype_operand_lt` (for
  `opa/opb/opc_lt`). After this the field is upfront-derivable and E1c is unblocked.

There is an in-code copy of this refactor status in the doc-comment of
`Readers.RegisterAccessTimestamp.bounds_of_byteGuarantees` (`Soundness/TypedTime.lean`).

### E1b — the `RowOK.align8` producer · remaining

The mod-8 window-alignment fact has no producer; derive it from the State trail — the `+8` epoch of
`statePullTime_of_decodedStateWalk` (`Soundness/AIR.lean`) gives the row's clock position, whose value
mod 8 is the public initial clock mod 8. One focused lemma; feeds `rowOK_alignedOf`'s `halign8` (and the
adjacent `time8`).

### E1c — realize `supportedCore_orderedRows_dynamic_of_contracts` · remaining

Currently a doc-comment shape in `Soundness/ChipContracts.lean`, not yet a declaration. It is the `walk`
invocation: choose the per-row `touches` (`Classical.choose` on the `rowAligned` field's `∃ touches`), build
the aligned row list `orderedRows.map g`, feed the seven walk inputs —

1. + 2. `engineFacts` transported by `localStepFact_align_of_ordinary` / `frameFact_align_of_ordinary`,
3. `rowOK_alignedOf` fed by the `rowAligned` field + E1b's `align8`/`time8`,
4. `boundary.localStateTruth`,
5. `memoryInit_liveOK`,
6. `endpointBalance_of_decodedStateWalk`,
7. `memoryBalance_of_alignsWith` (E1d),

— then transport each `Grounded` back via `grounded_ordinary_of_aligned` into
`dynamicGrounded_of_contracts`. Lands modulo the `contracts` hypothesis plus the two ensemble premises
`memBinary` / `paddingEmpty`.

### E1e — discharge the seam · remaining

Point `supportedCore_orderedRows_dynamic` (`Soundness/AIR.lean`) at `_of_contracts`; thread
`contracts` / `memBinary` / `paddingEmpty` as hypotheses until E2/E3 discharge them, keeping the seam
signature stable (feed `contracts := allChips_groundingContracts` once E3's aggregator exists).

**E1 is the milestone:** after it, the seam reduces to "the 25 `ChipGroundingContracts` instances plus
`memBinary` / `paddingEmpty`" — an enumerable rollout, not an open research seam.

## E2 — `memBinary` / `paddingEmpty`

The two ensemble premises E1 threads. `memBinary` (chip-half selector-binarity) mirrors the proved State
template — `stateInteractions_signed_binary` + `StateEmissionShape` (`Soundness/TypedState.lean`); build the
Memory-emission-shape analogue per chip and fold over the ensemble. `paddingEmpty` (a non-active row emits no
Memory) is per-chip.

## E3 — the 24-chip `ChipGroundingContracts` rollout

Add is the template. Per chip, produce the closed-form family and the bundle instance. Each memory closed-form
is **born folded** — `<chip>_circuit_output_eq` (a `@[circuit_norm]` `rfl` over an opaque input) + a
`simp only [circuit_norm]` closer, no `maxHeartbeats` ceiling — because `scripts/check_heartbeats.sh` forbids
a new override. Extract each chip's `Spec` via `SupportedChip.decodeRow_chipSpec_iff` and destructure in place
(never `exact <lemma> _ _ hyp` at a decoded row — the metavariable landmine). Wiring is shared per
reader-shape family: `rowWiring_rtype` exists (reuse for the register-register chips); the
immediate/jump/U-type/load/store/non-writing/DivRem families each need one new `rowWiring_<shape>` lemma,
amortized over the family. The aggregator `allChips_groundingContracts` (a 25-way `fin_cases`) feeds E1e.

## Tracks A–D — the 6 chip admissions (parallel to the seam)

These touch disjoint files and do not gate the seam; the seam threads `contracts` and closes independently.

- **A — ShiftLeft / Branch completeness.** ShiftRight is closed by the validated folded-core recipe:
  keep the combined flag constraint in the parent, place the 53-assert arithmetic tail behind a
  zero-witness `FormalAssertion`, prove that boundary with ordinary `circuit_proof_start`, and use
  `circuit_proof_start_core` in the parent. Reuse that boundary pattern before trying larger normalization.
- **B — DivRem completeness** (`DivRemChip/Completeness/Driver.lean`): the ~1531-line body already exists,
  `stop`-gated purely for elaboration cost; tame via the fold + a measured, guard-noted ceiling.
- **C — DivRem `evidenceSoundness`** (`DivRemChip/Formal.lean`): the math is proved (`Cases.lean` /
  `Extract.lean` / `Soundness.lean`); the remaining seam is the row→evidence circuit wiring — the heavy whnf,
  the long pole.
- **D — DivRem `main_exposedChannelsLawful` + `requirementsChannelsLawful`** (`DivRemChip/Formal.lean`): the
  smallest items; fold via the Branch `off_gate_vacuous` precedent (`BranchChip/Formal.lean`).

## Ordering, parallelism, and reuse

E1 is the main-thread critical path; then E3 and Tracks A–D run concurrently, E2 needs E3's
`typedMemoryInteractions_eq`, and the E3 aggregator + E1e shut the seam. Reuse the proved walk engine, the
aligned carrier, `memoryFrontierBalance`, the State template for `memBinary`, the R-type wiring, and the Mul
completeness recipe. The timed engine and the SP-6 slot machinery are the genuinely SP1-specific bespoke
parts; new wheels only where faster (the per-family wiring lemmas). Verify each unit with a clean
`lake build SP1Clean`, `#print axioms` on the touched declaration, and `scripts/check_heartbeats.sh`.
