# Roadmap — the W-graph to the machine-level VM theorem

The open work, organized as a dependency graph of work items (`W*`) whose **end state is the target
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

## The project debt at a glance — one `sorry`

The chip completeness debts (ShiftLeft/ShiftRight/DivRem) are now **all closed** (axiom-clean); the
**sole** remaining `sorry` is the capstone-packaging premise (item 4 below). Soundness is `sorry`-free.
(Line numbers drift; the declaration names are the stable handles — `scripts/run_audit.sh` gates on
exactly this set.) `MulChip.completeness` was closed 2026-06-10 via `MulOperation.spec_populate` (the
witnessed `populate` columns satisfy the structural `Spec`); items 1–3 below record the now-closed
ShiftLeft/ShiftRight/DivRem completeness work.

1. `ShiftLeftChip.completeness` — `Proofs/Chips/ShiftLeftChip/Formal.lean` — **CLOSED 2026-06-12**
   (axiom-clean), honest `populate`-style witness + `ProverHint` opcode threading (the
   `BranchChip.completeness` recipe).
2. `ShiftRightChip.completeness` — `Proofs/Chips/ShiftRightChip/Formal.lean` — **CLOSED 2026-06-12**
   (axiom-clean), same hint-`populate` recipe as ShiftLeft.
3. `DivRemChip.completeness` — `Proofs/Chips/DivRemChip/Formal.lean` — **CLOSED 2026-06-18** (axiom-clean),
   via `completeness_driver` in `Proofs/Chips/DivRemChip/Completeness/Driver.lean`. The 13 nested
   `IsEqualWord`/`IsZero` cols pins were unblocked by *selective non-decomposition* —
   `attribute [local circuit_norm ↓ 100000] ProvableType.eval_fromElements` keeps those sub-op cols folded
   so `circuit_proof_start` never explodes them into the intractable nested record (see
   `docs/agents/proof-patterns.md`). Heartbeats 256M → 64M.
4. `sp1_witness_decode` — `Soundness/SP1GatedVm.lean` — the single isolated capstone premise: the
   witness → `ChipRow` decode seam (`SP1WitnessDecode`, = **W1b/W1c** below); a packaging premise, not
   a chip debt. (`sp1_gatedExecution_prereqs` itself is now a *proven* assembly of this seam with the
   W1a balance translation `sp1_state_balance_of_balancedInteractions`.)

Note (census fact): because each chip `circuit` *embeds* its completeness proof as a structure field,
items 1–3 also surface as `sorryAx` on `sp1Tables`/`sp1GatedVm`/`sp1_machine_soundness` under
`#print axioms`, even though the soundness proofs never consume those fields. Closing items 1–3 is
therefore also what makes the *capstone chain's* census clean (together with item 4).

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
                     \                  |               B1  the 3 completeness sorries (M each)
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

**Clean PR #398 exposure: resolved (2026-06-10).** W9 landed by pinning Clean to the open PR's head
SHA (`292b9cc3`, 13 commits ahead / 0 behind the old pin) rather than waiting for the merge — the
custom gating is gone and W1a now works directly against the upstream primitives (and gains
`InteractionsWellFormed` + the new `Air/Balance` gated lemmas for free). Residual: a small re-pin to
the merge commit when the PR lands on `main`.

---

## Work items

### W10 — the target-theorem skeleton `[x]` (2026-06-10)

`Soundness/TargetVm.lean`: `GuestProgram`, `IsInitialState` (a load *relation*, with the
`SailConfigured` residue seam), `SailStep`/`SailChain` over the official `try_step`, `SP1Halted`
(observed one step before the halting ECALL), `SP1TargetPublicIO` (+`exit_code`, `toLegacy`),
`RefinesAt`/`RowEffect`, the `TargetObligations` gap bundle, and the **proved** walk induction
`sp1_target_execution` + the `sp1_machine_soundness`-routed corollary `sp1_target_soundness`.

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
prerequisite — done (2026-06-10):** syscall rows advance the clock by **256**, not 8 — `StateAccess`
now carries a per-row `clk_inc` (`Soundness/StateConsistency.lean`, projected at 8 by `stateAccess`
for all 25 current chips), `stateLookups`/`sndKey` (`Soundness/GatedVm/StateBridge.lean`) key on
`clk_low + clk_inc`, and the PC-chain layer (`pcChainProp`/`clkStep`/`TraceClkAdvance`/
`state_successor_of_balance`/`balanced_state_bus`) is per-access, so a mixed-increment trace
type-checks. The chip itself remains open. Deliverables: `TargetObligations.halt`/`halt_nonempty`,
`exit_code` bound into the public values (replace `SP1PublicIO` with `SP1TargetPublicIO` in
`SP1GatedVm.lean`), ECALL routing in `Coverage.lean` (today ECALL/EBREAK/UNIMP are the 3 uncovered
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
assembly of the W1b decode seam `sp1_witness_decode : … → SP1WitnessDecode witness` (the sole
remaining `sorry` in `Soundness/SP1GatedVm.lean`) with the proven W1a balance translation.

- [x] **W1a (2026-06-10):** Clean `Statement.BalancedChannels` → native `isConsistentBalanced`
  State-bus translation, **proven and clean-3** at ensemble scale:
  `sp1_state_balance_of_balancedInteractions` (`Soundness/SP1GatedVm.lean`), riding the generic
  adapter `isConsistentBalanced_of_balancedInteractions` + the per-key cast-sum kernel
  `intCast_multiplicitySum_map_toAccess` (`GatedVm/BalanceMod.lean`; same-channel `toAccess` keys
  separate exactly on the message by `ZMod.val`/`Array.toList` injectivity, so each `LookupKey` ℤ-sum
  casts to one Clean `balanceOf`), `Interaction.toAccess`/`intCast_signedVal`
  (`Model/InteractionProjection.lean`), the native `{-1, 0, 1}` bound
  `stateLookups_mult_binary` (`Soundness/StateConsistency.lean`), and the landed
  `isConsistentBalanced_of_intCast_zero`. *Notes: upstream's gated counting lemmas
  (`balanceOf_eq_mult_countP_of_mult_or_zero`, `exists_push_of_pull`, `activeInteractions`) turned
  out unnecessary — the per-key cast argument replaces counting; `InteractionsWellFormed` is carried
  by `BalancedChannel` but unconsumed (the multiplicity bound is native, from binary `is_real`).
  Residual (deliberately moved to the seam): the witness ↔ access-list correspondence itself — the
  `state_accesses_perm` field of `SP1WitnessDecode` (`stateLookups_eq_emitted` lifted over the
  25-table flatMap + the verifier boundary) — needs the row ↔ table binding and so rides W1b.*
- [ ] **W1b (L, the biggest piece):** the 25-table `witness.tables ↔ List (ChipRow p)` decode
  (`same_circuits` + `valueFromOffset`) + per-table `Component.weakSoundness`, now with a concrete
  target shape: produce the `SP1WitnessDecode` bundle (rows/data + `spec_holds` + `is_real_binary` +
  `state_accesses_perm`) demanded by `sp1_witness_decode`.
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

Extraction reproducibility (release-audit TB-9) was **not** fixed by the pin alone — the compiler at
the SP1 pin emits a `name`/`main`-**field** `ElaboratedCircuit` from a transient window of Clean main
(`60665ed0`, later reworked), which no pinned Clean accepts. `update_extracted.py` now normalizes the
emitter output (`_normalize_circuit_api`: parameterized instance + `pullIf`/`toRaw` names); a full
regen at the pin reproduces `Extracted/` + `WitnessTests/` byte-identical and the 14 circuit-form
files up to the (accepted, re-committed) emitter formatting of the two `Lt` files. **Residual:**
re-pin to the merge commit when the PR lands on `main`; upstream `d25bba8d` (post-pin, not in the PR
branch) likely retires the Batteries import-narrowing workaround (`docs/agents/lean-sail-notes.md`).

### W11 — re-base `GatedVm` on upstream `VmTables` (M–L; new, post-W9)

`GatedVm/` exists only because pre-#398 upstream `VmTables` hardwired `±1` multiplicities. Post-#398
it natively supports gated VMs (`VmStep`, `tables_channel` over `pullIf`/`pushIf` with enabledness
derived from constraints, `stepOfAllTables`, the gated
`verifier_guarantees_of_requirements_of_requirements_of_guarantees`,
`addVm_soundVmChannel_of_soundChannels`). Re-basing would inherit the upstream VM-channel soundness
engine for the State bus. Cost: every chip exposes `[pullIf is_real cur, pushIf is_real next]` on the
State channel (the state *receive* switches from `emit (-is_real)` to a true `pullIf` — harmless,
`StateMsg.Spec = True`) plus enabledness booleanity from the existing `is_real` gate. Adjacent to
W1a; not coupled to it.

### B1 — the three completeness `sorry`s (M each, independent)

Debt items 1–3 above (`MulChip.completeness` closed 2026-06-10 via `MulOperation.spec_populate` +
the `LtChip` witnessed-columns `convert`/`getElem_toElements_eval_varFromOffset` recipe); the
`BranchChip.completeness` recipe (honest `ProverHint` flag witnesses + shared dispatch) is the
template for the rest. Closing them also cleans the capstone chain's axiom census (see the debt note)
and retires the K6 sampled-conformance reliance for those chips.

---

## Coverage-claim hygiene (ongoing)

- Keep `allChipKinds_length` (25), `sp1Tables_length` (25), and the `Coverage.lean` guards
  (`coverage_kinds_eq_registry`, the covered/uncovered partition — 50 of 53 opcodes; ECALL/EBREAK/UNIMP
  open until W5) in sync as chips are added.
- In any external claim, cite the machine-derived surface figure — the 25 modeled chips cover the
  **Supervisor-mode halves of 25 of SP1's 122 `RiscvAir` variants** (v6.2.2-20-g9d249b8d4) — and the
  explicit exclusion list (decode/fetch, memory-infra, PageProt, syscalls/traps, Global, Range,
  precompiles, and the User-mode duplicates). `Supervisor/User`: decide whether single-variant coverage
  extends to the User duplicates (same AIR, different bus tags?) or stays a documented gap.
- The witness-vector battery and `Extracted/` currency are re-checked by `scripts/run_audit.sh` §A4 +
  CI `lake build`; the `SP1_PINNED_COMMIT` assertion in `update_extracted.py` keeps extraction
  provenance explicit. Remaining: a CI job that re-extracts and diffs per-PR.

---

## Cleanup / polish backlog (non-blocking)

Deferred quality/perf TODOs — none gate the VM theorem; pick up opportunistically. The *how-to-golf-safely*
lessons (heavy-core caution, kernel-safe dedup, the `maxHeartbeats`-is-the-wrong-lever finding, the available
`/cleanup` skills) live in `docs/agents/proof-patterns.md` § "Compile-time / performance landmines" + "Golf &
cleanup discipline".

- **`linter.style.longLine`** — the one remaining syntactic linter not yet enabled (it's the last candidate
  noted in AGENTS.md § Linters). ~1080 lines exceed 100 chars (`Native/` ~817, `FormalModel/` ~263). Enable it
  alone on the core pillar lake libraries, then reflow or per-file-suppress back to 0 warnings. Heavy, mechanical.
- **Shift soundness tail-dedup** — the real build-time prize. Extract the byte-identical `cpuA/msb*/aluA`
  requirements tail shared across the 6 Shift soundness conjuncts into a `requirements_holds`/`SpecObligation`
  helper, mirroring `Proofs/Chips/DivRemChip/Soundness/Tail.lean` (recipe: proof-patterns § "Shared-tail
  dedup"). Structural, multi-hour, overlaps the recently-golfed Shift soundness files — do it as a dedicated
  pass, not a drive-by.
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
