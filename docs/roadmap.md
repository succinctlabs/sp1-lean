# Roadmap — the W-graph to the machine-level VM theorem

The historical W-graph below was organized around `Target.sp1_target_execution`. The current theorem
stack is stricter: `supported_core_native_sound` proves the native ensemble refines a shard-local Sail
segment; `supportedCoreLocalExecution_anchors` lifts it to the canonical boot trajectory only when shard
composition supplies reachability; `supported_core_air_sound` is reserved for extracted/native faithfulness;
`sp1_air_refinement`/`sp1_air_sound` now give the conditional composition boundary for one exact upstream
execution cluster; and `SP1ExecutionRelation` specifies authenticated boot-to-halt shard composition. The
upstream theorem is not closed until its named refinement bundle and temporary commit-row premise are
instantiated. The old walk induction remains a useful lemma, not the headline contract.

**Status convention (2026-07-22).** The “project debt at a glance” section and
[`proposals/consolidation-progress.md`](proposals/consolidation-progress.md) are the live plan. The detailed
W-graph and dated progress snapshots below are retained as implementation history; their old critical path
and theorem names do not override the current stack above.

The open work was originally organized as a dependency graph of work items (`W*`) whose **end state is the target
theorem** `Target.sp1_target_execution` (`SP1Clean/Soundness/TargetVm.lean`): *from a verifying Clean
ensemble over the committed boundary, the official LeanRV64D Sail interpreter, run from any state that
loads the guest program, reaches the halting `ECALL` with the committed exit code.* The theorem is
**stated and its walk induction proved today**; every open gap is a named hypothesis in its
`TargetObligations` bundle (see `targetSeams` in that file). **Done when:** every `TargetObligations`
field is discharged for a concrete `OperandsBound`, and W1 closes the capstone premise — at that point
`sp1_target_soundness` is axiom-clean end-to-end (Sail model + one logUp axiom only).

For what is *already proven* and the full trust boundary, see [`release-audit.md`](release-audit.md).
For the machine-checked axiom inventory, run `scripts/run_audit.sh` (snapshot:
[`snapshots/axiom-ledger.md`](snapshots/axiom-ledger.md)).

Legend: `[ ]` open · `[~]` partial · `[x]` done. Effort: S < M < L < XL.

**Progress snapshot (2026-06-17).** A sweep down the critical path landed (build green throughout, every
new headline theorem axiom-clean modulo the Sail model's own decoder axioms; the 4-`sorry` debt unchanged):
**W3** closed end-to-end on the concrete-program path — the *real* `noncomputable` Sail decoder is reduced
(`Model/SailDecode.lean`), the decode bound is discharged from Program-bus balance, and `decodedInROM` is
proved for a concrete instruction. **W6b** non-vacuity witness done (`FormalModel/Trace/Witness.lean`).
**W4a** MemoryGlobalInit provider constructed (`Soundness/MemoryGlobal.lean`). **W2+W7** exact-replay
keystone done — `RefinesAt`/`RowEffect` strengthened to exact replay / strict write, `chain_to_refines`
re-proved — and the **W2 value-half assembled** (`ValueBound.lean`: `ValueOperandsBound`, the concrete
`OperandsBound = decode ∧ value`, and `targetObligations_full` with `bound` discharged). `SailConfigured`
strengthened to `isInitialized ∧ machine mode`. Remaining on the critical path: discharge the W2 cross-bus
residual `TraceValueBinding`, W5 HALT, W7's `try_step` reduction, glue.

---

## The project debt at a glance

The 4.31 migration re-opened chip-completeness proofs; `Mul` was restored (2026-07-16), leaving **four**
(`Branch`, `ShiftLeft`, `ShiftRight`, `DivRem`). They remain lower priority than fixing the semantic
boundary because completeness can be admitted without changing what a verifying row means. Each is the
"large-composition completeness kernel cliff" case documented in Clean's `doc/performance-problems.md`
§"Kernel size cliffs in completeness proofs"; the idiomatic repair is `circuit_proof_start_core` →
per-component `dsimp only [main, circuit_norm] at h_env` → `.1`/`.2` projection → split into a (virtual,
free) subcircuit where the parent still cliffs, **not** a `maxHeartbeats` bump. The current soundness debt
is more important and more precisely stated:

1. `DivRemChip.evidenceSoundness` is the single whole-chip seam from the generated DivRem circuit to the
   isolated four-family evidence contract in `Proofs/Chips/DivRemChip/Cases.lean`. Public
   `contractSoundness` is proved from it. Two DivRem channel-law packaging fields
   (`main_exposedChannelsLawful` and `requirementsChannelsLawful`) are separately deferred while Clean
   4.31 normalization is unstable.
2. `supportedCore_orderedRows_dynamic` is the timed semantic seam. Exact physical-row decoding,
   exhaustive State ordering, PC chaining, clock accounting, activity, registry membership, and
   committed Program decode are now proved by `supported_core_witness_grounding`. The remaining theorem
   must establish each ordered row's Memory guarantees, circuit assumptions, operands, and readiness
   against its evolving Sail state; `supported_core_native_sound` is the proved consumer. It closes via
   `supportedCore_orderedRows_dynamic_of_contracts` once all 25 `ChipGroundingContracts` land (Add is the
   proved pilot) + the arc-B aligned carrier + assembly-level balances. This engine is the SP1-specific
   realization of Clean's `Balance.lean` "guarantees-to-requirements-reversal" (see `architecture.md`
   §"Relationship to Clean's `Air` layer"). The dependency-ordered implementation plan for this seam and the
   seven chip admissions — the closure set, what is already proved, the in-progress `rowAligned`-upfront
   refactor, the `walk`-assembly steps, and the 24-chip rollout — is
   [`agents/capstone-seam-plan.md`](agents/capstone-seam-plan.md). **Sequencing:** opaqueness-audit the per-chip memory
   closed-form template (`<chip>_memoryInteractionValues_eq`, currently `@ maxHeartbeats 4M`) using the
   folded-`Spec` pattern *before* the 24-chip rollout — that cost multiplies 25×, so a lower floor on the
   template pays off across the whole rollout.
3. `sp1_decoded_rows_sound` is the older structural decode seam used only by the frozen Eulerian-trail
   intermediate.
4. The exact v6.3.1 source relation is now present: generated 34-table execution and 6-table
   memory-boundary profiles, all table/public-value lists, exact natural interaction balance, and an
   explicit preprocessed-commitment binding. `CoreAIRRefinementObligations` remains to be instantiated.
   Its boundary/execution cases must come from the timed grounding proof, not a restatement of the target.
5. `CoreAIRSemanticAssumptions` is the temporary narrow premise that a newly introduced COMMIT or
   COMMIT_DEFERRED flag has all eight corresponding rows. The extracted SyscallInstrs proof must still
   establish each row's operand equality. Resolve the premise with the Rust team or strengthen the AIR.
6. Concrete `SyscallHandler` refinements are separate deliverables. The baseline target handles raw
   syscall rows honestly at 264 ticks; precompile behavior is not claimed until the associated cluster
   proves the handler effect.
7. A future whole-machine `WitnessRelation.Complete` theorem may remain one explicitly
   completeness-only admission; Clean will not be redesigned merely to conceal that fact.

`scripts/run_audit.sh` gates the exact current file set. The obsolete nine DivRem per-op circuit proofs
were deleted during the contract conversion, so they no longer inflate either the source inventory or
the apparent remediation plan.

---

## The W-graph

```
            W10 TargetVm skeleton (DONE)
           /        |            \
    W6a GuestProgram (DONE,       \                     [independent tracks]
        in skeleton)               \
      /         \                   \                   W1  close sp1_gatedExecution_prereqs (XL)
 W6b ELF tool   W3 Decode/Fetch     W7 try_step           ├─ W1a Clean→native balance translation [x]
 (M, off-path)  chips (L)           step-lift (XL)        ├─ W1b 25-table witness ↔ ChipRow decode (L)
                     \                  |                 └─ W1c isU64 recovery from memory bus (M)
            W4a MemoryGlobalInit/       |               W8  logUp axiom packaging (M–L, after W1)
                Final single-shard      |               W9  Clean PR #398 migration [x] (2026-06-10)
                slice (L)               |               W11 re-base GatedVm on upstream VmTables (M–L)
                     \                  |               B1  the 5 completeness sorries (M each)
                     \                  |
                W2 operand binding from memory-bus
                balance (XL) [+W2b load/store data
                addresses into RowView (L)]
                     \                  |
                W5 ECALL/HALT chip (M–L) [clk_inc prereq x 2026-06-10]
                     \                  |
                      glue: discharge TargetObligations
                                |
                 sp1_target_execution UNCONDITIONAL
                                |
                W4b multi-shard ShardComposition (XL) [post-target]
```

**Critical path:** W3 → W4a → W2 → W5 → glue (W3 + W4a substantially done, W2's exact-replay keystone
done — see the progress snapshot; the live front is the **W2 value-half ↔ W5 ↔ W7 `try_step` reduction**).
**W7 runs fully in parallel** and becomes the critical path if the Sail `translateAddr`/fetch reduction in
machine mode is heavier than expected — note its decode stage is already reduced (`Model/SailDecode.lean`),
and its `RowEffect` target shape (strict write) is now fixed by the W2+W7 keystone. **W1 is on the path of
the axiom-clean end-to-end claim but not of the named-hypothesis target theorem** — it merges at the very
end (`sp1_target_soundness` inherits its closure automatically).

**Clean PR #398 exposure: resolved (2026-06-10); merged-`main` re-pin landed (2026-06-26).** W9 first
landed by pinning Clean to the open PR's head SHA (`292b9cc3`, 13 commits ahead / 0 behind the old pin)
rather than waiting for the merge — the custom gating is gone and W1a now works directly against the
upstream primitives. The residual re-pin to the **merge commit** (`2c20f7f0`) is now done: it migrated
`channelsWithRequirements` off `ElaboratedCircuit` onto the formal-circuit structures (the default
`requirementsChannelsLawful` tactic closes once the list is set), renamed the `pushIf`/`pullIf` value
forms to `pushedIf`/`pulledIf`, and dropped the `BalancedChannel` `∧ InteractionsWellFormed` `.1`. Build
green (3628), `lake test` green (3324), axiom-clean. The `cedc171b` "assume constraints for channels with
reqs" obligation (an off-gate pull `Requirements`) is discharged by listing every touched channel in
`channelsWithRequirements`; the soundness off-gate conjuncts are vacuous under the binary gate
(`SP1Clean.off_gate_vacuous`, `Math/Gate.lean`). Padding (`mult = 0`) stays vacuous throughout.

---

## Work items

### W10 — the target-theorem skeleton `[x]` (2026-06-10)

`Soundness/TargetVm.lean`: `GuestProgram`, `IsInitialState` (a load *relation*, with the
`SailConfigured` residue seam), `SailStep`/`SailChain` over the official `try_step`, `SP1Halted`
(observed one step before the halting ECALL), `SP1TargetPublicIO` (+`exit_code`, `toLegacy`),
`RefinesAt`/`RowEffect`, the `TargetObligations` gap bundle, and the **proved** walk induction
`sp1_target_execution` + the balanced-trail-routed corollary `sp1_target_soundness`.

### W6 — the guest program

- [x] **W6a** `GuestProgram` (encoded ROM primary, decode is a theorem target) — in the skeleton.
- [~] **W6b** **non-vacuity witness done (2026-06-17, `FormalModel/Trace/Witness.lean`, axiom-clean):**
  `isInitialState_nonvacuous : ∃ s0, IsInitialState emptyProgram s0`, so the target theorem's hypothesis
  is not vacuous. Reusable machinery: `Fintype Register` (derived), `configuredState pc` +
  `cfgState_init`/`pc`/`priv` (a state with every register present, PC pinned, machine mode). **Remaining
  (deferred, lower value):** ELF → `GuestProgram` byte ingestion (mirror SP1's `Program::from_elf`,
  `../sp1 crates/core/executor/src/program.rs`) + a richer (non-empty) witness ROM (reuses
  `configuredState` + `mem` content + `romLoaded` byte proofs; `BitVec 64` `rom_*` proofs need `bv_decide`).

### W3 — InstructionDecode/InstructionFetch → the decode half of `OperandsBound` `[~]` (closed end-to-end on the concrete-program path, 2026-06-17)

Build the project `decode` on LeanRV64D's own decoder (so fetch-decode coherence with `try_step` is by
construction); the decode component of `OperandsBound` is each real row's operand indices/immediates being
the decode of `prog.fetchWord` at its pc. **Landed:**
- `Soundness/Decode.lean` — `instrToProgramRow` (all opcode families), `DecodeOperandsBound`/`decodedInROM`,
  and `decode_bound_of_balance`/`decode_targetBound_of_balance` (the decode half of `bound` from a
  **constructed** `ProgramProvider (decodedInROM prog)` + Program-bus balance, no threaded `h_link`; the
  generalization `programProvider_of_valid` is in `ProgramProviderSpike.lean`).
- `Model/SailDecode.lean` — the **real `noncomputable` Sail decoder reduced**: `decode_ADD_example` proves
  `(ext_decode 0x003100B3).run s = .ok (RTYPE …) s` via a lazy branch-skip walk (`run_bind_ok_none`/`_some`
  + a clean-stop `refine`-walk), under `SailConfigured` (= `isInitialized ∧ machine mode`).
- `Decode.lean` `decodedInROM_addRow` — composes the two into the W3 obligation for a concrete ADD.

**Remaining:** a symbolic-register `ext_decode_RTYPE` is **out of scope** (would need `bv_decide` per
cascade branch; decode is only ever applied to *concrete* ROM words, so the per-opcode recipe suffices for
the witness program). The general `∀ prog` case keeps `decodedInROM` a trusted decode-chip assumption
(cf. `ProgramRowSpec`).

### W4 — the memory-infrastructure chips

- [~] **W4a (single-shard slice, L):** **MemoryGlobalInit provider constructed (2026-06-17,
  `Soundness/MemoryGlobal.lean`, axiom-clean)** — the Memory-bus analog of `ProgramProviderSpike`.
  `memGenesisContributions` (one entry per address at value 0, genesis timestamp `t0`) +
  `memProviderGenesis_of_contributions` discharges the threaded `MemProviderGenesis`;
  `traceMemoryValid_of_genesis_and_balance` derives `TraceMemoryValid` from the constructed provider +
  ordering side conditions + balance (residual: `t0` below all real clocks). `memBalanceHyps_of_genesis`
  (`MemoryIsU64.lean`) lifts the operand isU64/value facts onto the same provider. **Remaining:**
  `MemoryGlobalFinal` + binding the genesis value / final image to a concrete `prog.memImage` / boundary
  (the per-address *value* — W2's replay precision).
- [ ] **W4b (multi-shard, XL, post-target):** `ShardBoundary` (pc/clk chaining, init/final memory
  boundary, cumulative-sum carry), `MemoryLocal`/`MemoryBump`/`StateBump`, `machineValid_of_shards`.
  SP1's full memory argument is fundamentally multi-shard; the target theorem is single-shard first.

### W2 — operand/register binding from the memory-bus balance (XL; the long pole) `[~]` exact-replay keystone landed (2026-06-17)

Derive, from the memory-bus balance + the register adapters' `prev_value` columns, that each row's
committed operand *value* columns equal the live register/memory values at its walk position — i.e.
prove `TargetObligations.bound` for the concrete `OperandsBound` and strengthen `RefinesAt`'s register
frame to exact replay.

**Keystone DONE (commit, `Soundness/TargetVm.lean`):** the exact-replay surgery on the *proved* capstone —
`replayVal` (most-recent `op_a` write over the path prefix); `RefinesAt.frame` strengthened from a
frame-disjunction to **exact replay**; `RowEffect.regs` strengthened to the **strict write** form
(`s'=rdWrite` at `op_a`, `s'=s` elsewhere — what W7's `wX_bits rd` produces); `chain_to_refines` /
`sp1_target_execution` re-proved green, no new axioms. So W2's exact-replay and W7's `RowEffect` shape land
together as designed.

**Value-half assembled (`Soundness/ValueBound.lean`):** `ValueOperandsBound` (live registers = committed
`op_b`/`op_c` `prev_value` columns); `value_targetBound` proves the value half of `bound` by composing the
exact-replay invariant (`RefinesAt.frame`) with the cross-bus link (axiom-clean); `OperandsBound_full =
decode ∧ value`, `operandsBound_full_targetBound` (full `bound`, both halves), and `targetObligations_full`
(the full `TargetObligations` at the concrete `OperandsBound`, `bound` discharged, `lift`/`halt` the W7/W5
seams — the Phase-7 glue entry point).

**Walk-clk bridge landed (`ValueBound.lean`):** `walk_clk_monotone` — consecutive `WalkOf` rows advance
the state-bus clock (`sndClkOf path[i] = rcvClkOf path[i+1]`), i.e. the walk visits rows in increasing clk
order = the order the Memory-bus value chain reads them (`sndClk_eq_rcvClk` is the clk twin of
`sndPc_eq_rcvPc`; `isWalk_chain` was exposed for it).

**Remaining `TraceValueBinding` discharge:** compose `walk_clk_monotone` with (i) the memory event
timestamps = row clocks (`rowClkLow`), (ii) the Memory-bus value chain (`memEvent_prevValue_eq_writer` /
`traceMemoryValid_of_genesis_and_balance`: a read returns the most-recent earlier write, read-backs
preserving it), and (iii) the genesis alignment (`s0`'s initial registers = 0 = the init chip's genesis) —
the induction relating `replayVal`'s walk recursion to the memory event chain. Sub-item **W2b (L):** thread
real load/store data addresses into `Trace.RowView` (the §8.4 gap) and strengthen `RowEffect`'s ROM clause
to full store-replay memory.

### W5 — the ECALL/HALT chip (M–L)

Model the HALT slice of `SyscallInstrs` (`../sp1 crates/core/machine/src/syscall/instructions/air.rs`:
`is_halt` ⟹ `next_pc = [HALT_PC,0,0]`, syscall id in `t0`/x5, exit code in `a0`/x10). **Hidden
prerequisite — done (2026-06-10):** syscall handling adds 256 ticks to the ordinary `CLK_INC = 8`,
so a syscall row advances by **264** — `StateAccess`
now carries a per-row `clk_inc` (`Soundness/StateConsistency.lean`, projected at 8 by `stateAccess`
for all 25 current chips), `stateLookups`/`sndKey` (`Soundness/GatedVm/StateBridge.lean`) key on
`clk_low + clk_inc`, and the PC-chain layer (`pcChainProp`/`clkStep`/`TraceClkAdvance`/
`state_successor_of_balance`/`balanced_state_bus`) is per-access, so a mixed-increment trace
type-checks. The chip itself remains open. Deliverables: `TargetObligations.halt`/`halt_nonempty`,
`exit_code` bound into the public values (replace `SP1PublicIO` with `SP1TargetPublicIO` in
`SP1Ensemble.lean`), ECALL routing in `Coverage.lean` (today ECALL/EBREAK/UNIMP are the 3 uncovered
opcodes of 53), and pointing `stateAccess`'s `clk_inc` projection at a `RowView`-level increment.

### W7 — the `try_step` step-lift (XL; parallel track) `[~]` decode stage + RowEffect shape landed

Per chip kind: in a state satisfying `RefinesAt` + the concrete `OperandsBound`, reduce
`(try_step 0 false).run s` — interrupt check, fetch (vs `RomLoaded`), decode (vs W3's decoder),
execute (vs the existing `correct_*_native` bridges), PC commit — to `.ok _ s'` with
`RowEffect r s s'`. **Already in place (2026-06-17):** the **decode stage** is reduced
(`Model/SailDecode.lean`: `run_bind_ok_none`/`_some` + the branch-skip walk reduce the real `ext_decode`);
`SailConfigured` is populated to `isInitialized ∧ machine mode` (the two pins the decode reduction needs;
more added as fetch/execute discover them); and the **`RowEffect` target shape is now fixed** (the strict
write form from the W2+W7 keystone — `wX_bits rd` produces exactly it). Remaining: fetch + execute (vs the
per-chip `sailEquiv`/`correct_*_native` bridges, no `Bridge.lean` changes expected) + PC commit, per chip
kind. Risk: the address-translation reduction; if heavy, this becomes the critical path.

### W1 — close `sp1_gatedExecution_prereqs` (§B5 residue; XL, independent track)

`sp1_gatedExecution_prereqs` is no longer a monolithic `sorry` (2026-06-10): it is a **proven**
assembly of the W1b decode seam `sp1_decoded_rows_sound : … → DecodedRowsSound witness`
with the proven W1a balance translation.

- [x] **W1a (2026-06-10):** Clean `Statement.BalancedChannels` → native `isConsistentBalanced`
  State-bus translation, **proven and clean-3** at ensemble scale:
  `sp1_state_balance_of_balancedInteractions` (`Soundness/SP1Ensemble.lean`), riding the generic
  adapter `isConsistentBalanced_of_balancedInteractions` + the per-key cast-sum kernel
  `intCast_multiplicitySum_map_toAccess` (`Model/BalanceBridge.lean`; same-channel `toAccess` keys
  separate exactly on the message by `ZMod.val`/`Array.toList` injectivity, so each `LookupKey` ℤ-sum
  casts to one Clean `balanceOf`), `Interaction.toAccess`/`intCast_signedVal`
  (`Model/InteractionProjection.lean`), the native `{-1, 0, 1}` bound
  `stateLookups_mult_binary` (`Soundness/StateConsistency.lean`), and the landed
  `isConsistentBalanced_of_intCast_zero`. *Notes: upstream's gated counting lemmas
  (`balanceOf_eq_mult_countP_of_mult_or_zero`, `exists_push_of_pull`, `activeInteractions`) turned
  out unnecessary — the per-key cast argument replaces counting; `InteractionsWellFormed` is carried
  by `BalancedChannel` but unconsumed (the multiplicity bound is native, from binary `is_real`).
  Residual (deliberately moved to the seam): the witness ↔ access-list correspondence itself — the
  `state_accesses_perm` field of `DecodedRowsSound` (`stateLookups_eq_emitted` lifted over the
  25-table flatMap + the verifier boundary) — needs the row ↔ table binding and so rides W1b.*
- [ ] **W1b (L, the biggest piece):** the 25-table `witness.tables ↔ List (ChipRow p)` decode
  (`same_circuits` + `valueFromOffset`) + per-table `Component.weakSoundness`, now with a concrete
  target shape: prove the `DecodedRowsSound` facts (`spec_holds` + `is_real_binary` +
  `state_accesses_perm`) about `decodedChipRows`.
- [~] **W1c (M):** each chip's `isU64` operand `Assumptions` recovered from the memory-bus balance.
  Lemma family landed (`operand_{a,b,c}_isU64_of_memBalance` in `Soundness/MemoryIsU64.lean`, riding
  the limb-level bus-key extraction + per-address chain induction `eventsAt_values_isU64`, under the
  `MemBalanceHyps` bundle); wiring into the capstone rides W1b.

### W8 — logUp/GKR packaging (M–L, after W1)

Replace the assumed balance with one named `axiom logupGkrSound` ("a verifying GKR+PCS transcript ⟹
fingerprinted cumulative sum = 0") in `Model/InteractionBus.lean`, and prove the non-crypto half
(fingerprinted-sum-zero ⟹ send/receive multiset equality, LogUp/Schwartz–Zippel). **Done when** the
TCB cites one crypto axiom instead of "balance assumed."

### W9 — Clean PR #398 migration `[x]` (2026-06-10)

Landed by pinning Clean to the **open PR's head SHA**
([Verified-zkEVM/clean#398](https://github.com/Verified-zkEVM/clean/pull/398) =
`292b9cc369be11baf816926a4bd5a697c01b1dcc`, 13 commits ahead / 0 behind the old `main` pin, same 4.28
toolchain) rather than waiting for the merge. Upstream `Channel.toRaw` is now gated on zero
multiplicity and receives owe no `Requirements` at all, so the whole custom layer in
`Model/Channels.lean` (`toRawGated`/`gatedReceive`/`emitGated`/`receivedGated`/`emittedGated` +
projections + `binary_gate_req_vacuous`; the asymmetric family turned out to be dead code) is deleted
in favor of `Channel.pullIf`/`Channel.emit`/gated `toRaw`. Side effect worth knowing: pre-W9,
`sp1GatedVm.busChannels` listed `toRawGated` records while the readers emitted on `toRaw` — records
that differed at `mult = 0` — so the ensemble balance plausibly did not bind the program/memory
emissions; the unification makes the Statement's bus balance genuinely bind them.

**Historical note (superseded 2026-07-22):** the compatibility normalizer described below no longer
exists; the direct-circuit backend and all generated circuit files were deleted. At the time,
extraction reproducibility (release-audit TB-9) was **not** fixed by the pin alone — the compiler at
the SP1 pin emits a `name`/`main`-**field** `ElaboratedCircuit` from a transient window of Clean main
(`60665ed0`, later reworked), which no pinned Clean accepted. At the time, `update_extracted.py`
normalized that emitter output (`_normalize_circuit_api`: parameterized instance + `pullIf`/`toRaw`
names); a full regen at the pin reproduced `Extracted/` + `WitnessTests/` byte-identically and the 14
circuit-form files up to the (accepted, re-committed) emitter formatting of the two `Lt` files.
**Residual: CLOSED
(2026-06-26)** — re-pinned to the merge commit `2c20f7f0` (see the "merged-`main` re-pin" note above;
`_normalize_circuit_api` extended to strip the now-`ElaboratedCircuit`-less `channelsWithRequirements`
field + rfl-lemma). The normalizer and circuit backend were then deleted in the 2026-07-22 list-only
cutover. Upstream `d25bba8d` (now in the pin) deletes Clean's clashing
`Fin.foldl_eq_foldl_finRange`, so the Batteries import-narrowing is no longer forced — kept as the
project's narrow-import compile strategy, documented in `docs/agents/lean-sail-notes.md`.

### W11 — re-base `GatedVm` on upstream Clean ensembles (**Phases 0–5 DONE 2026-07-02**; dependency refactor closed)

**Landed.** The bespoke `GatedVm` data layer is retired: the capstone is `Soundness/SP1Ensemble.lean` —
`sp1Ensemble`, a **plain** Clean `Air.Flat.Ensemble` (25 chips + 11 in-circuit boundary/provider tables
[8 byte + program ROM + memory init/finalize] over the four buses, `sp1StateVerifier` pull-final/
push-init boundary), with `balanced_state_trail_soundness` over its `Statement` and the decode seam
`sp1_decoded_rows_sound` re-anchored to `EnsembleWitness sp1Ensemble`. `GatedVm/{Defs,Formal}.lean` deleted;
`BalanceMod.lean` relocated verbatim to `Model/BalanceBridge.lean` (Clean's `Air/Balance` is field-level
only — the field→ℤ bridge exists nowhere upstream); the Eulerian-trail machinery
(`GatedVm/{Chain,StateBridge,Capstone,SailDispatch,Bridge}.lean`) is unchanged. All 25 chips carry State
`exposedChannels` + `sp1StateVmSpike : VmTables` (`Soundness/StateVm.lean`); byte/program are finished
against in-circuit providers; the memory boundary is closed (init-push + finalize-pull, boolean mults,
`memBalanceHyps_of_boundary`).

**Decision (2026-07-13).** The final object remains a *plain* `Ensemble` because Clean's composition
machinery can't hold it: post-memory-flip every chip's `channelsWithGuarantees` contains
`memoryChannel`, which can never be a *finished* channel (chips pull-then-push it — the circular
VM-channel shape) and `addVm` is single-VM-channel with exactly one `[pulledIf, pushedIf]` pair per
table (chips make 3–4 memory pairs; the memory boundary is a multiset, not one pull+push). Un-parking
`sp1StateVmEnsemble` (`Soundness/StateVm.lean`) and expressing memory as a true second VM channel would
need a large **multi-VM / multi-step / multi-boundary `VmTables` generalization**. We will not perform
that Clean refactor for this capstone. The existing `GeneralFormalCircuit` packages stay intact, and any
whole-machine completeness-only debt is isolated as an explicit top-level admission. P5.4 is **done**:
`sp1_finishedChannel_guarantees` (`Soundness/FinishedChannels.lean`) —
the proven **byte** pull-guarantee grounding over `sp1Ensemble` (every table's byte `ChannelGuarantees`
from `Statement`, via `guarantees_of_requirements_append` on the consumer/provider partition; feeds the
seam's per-chip `FullGuarantees`). Program is again a structural `Channel(RowSpec)` under W12; its
`decodedInROM` half is proved separately from provider balance and program commitment rather than being
installed as a pull guarantee.

### W12 — structural buses + semantic timed grounding (in progress, 2026-07)

The channels communicate field tuples and multiplicities, exactly as SP1's interaction buses do.
Execution meaning is a theorem about the balanced, timestamped records; it is not a row-local channel
guarantee. State therefore carries `True`, Program carries structural `RowSpec`, Memory carries
`isU64 ∧ ClkBound` (value hygiene + a bounded 24-bit access timestamp `clk_low.val < 2^24`),
and Byte carries its lookup predicate. The global engine combines balance, provider/commitment binding,
schedule ordering, and per-chip `advance` lemmas to derive Sail execution truth.

**Landed (2026-07-13 architectural cut).** `Model/VmChannel.lean` was deleted; State and Program use
plain Clean `Channel`s. The Phase-1 walk was promoted to `Soundness/TimedGrounding.lean` and remains
kernel-checked after the cut, demonstrating that its induction did not depend on semantic channel
assumptions. `Model/Machine/{Boot,Schedule,Execution}.lean` now makes loader and timing policy external to
the witness, uses PolyFun's PR-34 `DynSystem.Machine` only for the native Sail run, records ordinary
eight-tick and syscall 264-tick schedules, and removes `/ 8` from the new execution relation.
`FormalModel/{Relations,Execution,Verifier}.lean` and `Contracts/PublicValues.lean` separate AIR
refinement, full upstream public values, semantic execution, and the eventual ArkLib verifier theorem.
The old headline was renamed to `balanced_state_trail_soundness`; `supported_core_native_sound` is the
honest proved local-refinement consumer of the disclosed `supportedCore_orderedRows_dynamic` seam,
`supported_core_air_sound` is reserved for the extracted-faithful supported AIR, and the exact-upstream
`sp1_air_refinement`/`sp1_air_sound` composition boundary is now implemented separately (see below).

**Landed setup continuation (updated 2026-07-22).** `SP1ExecutionStatement`/`SP1ExecutionRelation`
distinguish a single shard segment from boot-to-halt composition. The former opaque `ShardIntegrity`
parameter has been replaced by a concrete `AuthenticatedLedger` transcribing recursion's rolling-field
equalities and endpoints, plus narrow septic-balance and deferred-authentication relations. Full-state
segment stitching is explicit; PC/timestamp continuity is not treated as state identity.
`WitnessRelation.Complete` records the future converse without forcing a Clean redesign.
`Soundness/SupportedMachine.lean` remains the single 25-chip native descriptor used by the registry,
ensemble, and routing surfaces. `Soundness/RankedGrounding.lean` proves that balanced transitions with a
strict clock rank form an exhaustive trail, eliminating the old disconnected-cycle blind spot.

**Landed contract cleanup (2026-07-13).** No chip `ProverAssumptions` contains `StateTruth` or
`ProgTruth`. Circuit completeness now proves only row-local witness, reader, and bus-hygiene facts;
semantic execution enters through `advance` and the global grounding theorems. The sweep also removed
the obsolete CPUState requirement from every affected soundness tail. Lean 4.31 normalization/`whnf`
debt remains in the disclosed completeness proofs and DivRem whole-chip evidence extraction, not in the
channel interface. The old DivRem per-op bodies have since been retired.

**Landed typed Memory bridge.** `Soundness/TypedInteractions.lean` is a proof-carrying adapter over
Clean's exact evaluated interactions, and `TypedMemory.lean` classifies the active Memory pulls/pushes
without constructing a second lookup projection. `ordinaryRowFacts` feeds those exact records into
`TimedGrounding`; grounded prior records recover the circuit's Memory `ChannelGuarantees` and live Sail
register values. `CircuitRegisterOperandPullAt`/`CircuitRegisterOperandPullShape` are the small per-chip
contract: each register operand must identify its exact emitted pull and bind its message to the common
`RowView`. All 24 non-DivRem chips now carry their Clean memory closed forms
(`exposedMemoryInteractions` + `interactionsWith_memory_eq`), and the memory-clock discipline was
consolidated into the readers (`Readers.ClkDiscipline`, `Model/BusMessages.lean`; H2a, −181 lines net),
with ShiftRight deriving its write-push clock bound in-circuit after gaining the `is_real`/flag-sum bind
(H1). No operation-level Rust/Lean bridge is involved.

**Residual dynamic work.** The `GroundingAdapter` advance-adapter, the `ChipGroundingContracts` bundle
(Add instance proved, reducing the seam to `supportedCore_orderedRows_dynamic_of_contracts`), and the
aligned-carrier transports (`AlignedCarrier.lean` + `AlignsWith`) are landed. Remaining: instantiate the
bundle across the supported registry (separately for R-, ALU-, I-, J-, load/store, and no-write reader
shapes), build the memory-channel balance stack, and derive each row's remaining circuit
assumptions and `advanceReady` facts, combined with the proved State position equation. The
grounding engine still needs RAM records and same-location intra-row chaining before loads/stores and
register aliases such as `rd = rs1` are covered. These are the concrete inputs to
`supportedCore_orderedRows_dynamic`; they are independent of the verifier/ArkLib workstream.

**Landed exact-upstream boundary (2026-07-22).** The audited list-only extractor now emits the complete
baseline Core system tables, machine-level public-value block, and a fail-closed runtime manifest at
semantic revision `a630089d9ff484ec6f2feade8d0afbb1447eed11`. `CoreProfile` proves the readable target is
exactly the 34-table execution cluster plus the separate 6-table memory-boundary cluster, with matching
main/preprocessed widths and 160 public cells. `Faithful/CoreAIR.lean` defines the heterogeneous rows,
cluster-specific relation, preprocessed-commitment seam, and exact natural-multiplicity interaction
balance. `Model/Machine/{Syscall,EventExecution}.lean` gives the 8/264-tick eventful target.
`Soundness/CoreAIR.lean` exposes a deterministic decoder and field-by-field
`CoreAIRRefinementObligations`; it proves the ArkLib-ready refinement once those obligations and the
narrow commit-row provenance premise are supplied. The `.execution` guard prevents the memory-boundary
cluster from satisfying the shard theorem.

The Rust-faithfulness boundary is also moving from operations to chips. `AddChip` now owns an independent
native row, a self-contained generated `Extracted/ChipOracle/Add.lean`, and an all-row
`addChip_faithful` proof comparing complete assertions and interactions. Migrate the remaining chips one
at a time; do not add operation anchors or witness batteries, and delete each legacy artifact when its
last chip consumer disappears. Direct Rust-generated circuits are already gone: their definitions are
hand-maintained under `Native/Operations/`. The extraction script hard-fails requested system/public-value/
chip-oracle/trace failures and validates the machine manifest even on focused runs. A complete AIR-only
regeneration against the v6.3.1 overlay reproduced every pre-existing instruction/reader/list artifact
byte-for-byte.

**Open.** Generalize `TimedGrounding` from ordinary register-only windows to RAM, repeated same-location
touches, state bumps, syscalls/precompiles, and `SP1MachineModel.schedule`; derive Program commitment truth
from the provider balance; close `supportedCore_orderedRows_dynamic` and retire the older
`sp1_decoded_rows_sound`/Eulerian path; instantiate the exact upstream table/public-value refinement
bundle, concrete syscall handlers, and recursive ledger relations; then instantiate ArkLib knowledge
soundness as `sp1_verifier_sound` without changing its extraction error. ArkLib must extract exact
non-wrapping natural interaction multiplicities, not merely a field-sum equality.

**Larger-program boundary (not this workstream's critical path).** An executable Lean Core verifier over
structured proof data, its deterministic refinement to a protocol specification, ArkLib knowledge
soundness, and this AIR-to-execution development are separate layers that can proceed in parallel. They
compose in that order at `sp1_verifier_sound`; none should be silently folded into `sp1_air_sound`.
Compressed recursion and the Plonk/Groth16 wrappers are separate verifier targets. The present AIR-side
priority is to close the typed timed-grounding path and then extend the theorem from the supported
25-chip slice to the complete upstream Core AIR.

### B1 — the four 4.31 completeness regressions (M each, independent)

`BranchChip.completeness` remains the intended honest-`ProverHint`/shared-dispatch template for
ShiftLeft and ShiftRight. DivRem should be revisited only after its chip-level contract and generated-row
boundary settle, since another structural refactor would invalidate a large witness proof again. Closing
these also removes structural `sorryAx` propagation through bundled circuit values, even though machine
soundness does not consume their completeness fields.

---

## Coverage-claim hygiene (ongoing)

- Keep `allChipKinds_length` (25), `sp1Tables_length` (25), and the `Coverage.lean` guards
  (`coverage_kinds_eq_registry`, the covered/uncovered partition — 50 of 53 opcodes; ECALL/EBREAK/UNIMP
  open until W5) in sync as chips are added.
- In any external claim, cite the machine-derived surface figure — the 25 modeled chips cover the
  **Supervisor-mode halves of 25 of SP1's 122 `RiscvAir` variants**
  (`v6.3.1-8-ga630089d9`) — and the
  explicit exclusion list (decode/fetch, memory-infra, PageProt, syscalls/traps, Global, Range,
  precompiles, and the User-mode duplicates). `Supervisor/User`: decide whether single-variant coverage
  extends to the User duplicates (same AIR, different bus tags?) or stays a documented gap.
- Checked-in trace anchors and `Extracted/` modules are elaborated by CI. The two-revision provenance,
  checked-in exporter-patch hashes, unconditional runtime manifest, and successful full AIR-only
  byte-identical regeneration make the local process reproducible. CI should still add an isolated
  re-extract-and-diff job so that this does not depend on a developer running the currency check.

---

## Cleanup / polish backlog (non-blocking)

Deferred quality/perf TODOs — none gate the VM theorem; pick up opportunistically. The *how-to-golf-safely*
lessons (heavy-core caution, kernel-safe dedup, the `maxHeartbeats`-is-the-wrong-lever finding, the available
`/cleanup` skills) live in `docs/agents/proof-patterns.md` § "Compile-time / performance landmines" + "Golf &
cleanup discipline".

- **`linter.style.longLine`** — the one remaining syntactic linter not yet enabled (it's the last candidate
  noted in AGENTS.md § Linters). ~1080 lines exceed 100 chars (`Native/` ~817, `FormalModel/` ~263). Enable it
  alone on the core pillar lake libraries, then reflow or per-file-suppress back to 0 warnings. Heavy, mechanical.
- **Shift proof decomposition** — if the repeated `cpuA/msb*/aluA` tail becomes a real bottleneck, extract
  named evidence from it and prove the semantic result in a circuit-independent file, following the new
  DivRem `Cases.lean` boundary. Do not recreate the retired DivRem `SpecObligation`/shared-tail architecture.
- **`/decompose-proof` candidates** — long proof bodies worth splitting into named sub-lemmas:
  `ShiftLeftChip`/`ShiftRightChip` `Formal.lean` `completeness` (~123/~180 lines), `LoadHalfChip`'s 4-way
  `h_sel_lt` offset-selection case-bash (near-verbatim across soundness + completeness), `BranchChip`
  `soundness`/`completeness` (~156/~290 lines of per-column `env.get` plumbing). Several are perf-tuned —
  decompose with care and watch elaboration time.
- **SailState-staging bridge preamble** — the `hpc_get`/`key`/`hsp_config` preamble recurs across ~10
  store/jal/load `Bridge.lean` files → a shared lemma. **Re-examine the shape first** — upstream #101/#102
  rewrote several bridges in the 2026-06-23 merge, so the pre-merge duplication may have shifted.
- **Namespace-isolate the auto-gen (linter hardening, Option B)** — the `sp1Lint` exclusion is a *soft*
  module-path filter. A *hard* boundary would relocate all auto-gen to a separate root namespace
  `SP1Extracted.*` so the stock `runLinter` excludes it by construction (no custom filter). Cost: ~87 module
  renames + import-line edits + `update_extracted.py` writer paths + lakefile globs. Not worth it for linting
  alone; reconsider only if a hard auto-gen/hand-written namespace split is wanted for other reasons.
