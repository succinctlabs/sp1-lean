# W11 ensemble re-base — status & what's left (hand-off 2026-06-26; **Phases 4–5 landed 2026-07-02**)

Re-basing the whole-machine capstone onto canonical Clean `SoundEnsemble`/`VmTables` with
`StaticLookupChannel` providers, replacing the bespoke `GatedVm`. Full plan:
`~/.claude/plans/make-a-plan-to-valiant-wozniak.md`. Design + faithful-provider details + the validated
Phase-0 techniques: `docs/agents/bytechip-provider-design.md`. Branch `dtumad/clean-upgrade`; everything
below is committed and **green** (guards pass, one known `sp1_witness_decode` sorry).

**2026-07-02 update — items 6–7 below are DONE.** The capstone is now `Soundness/SP1Ensemble.lean`:
`sp1Ensemble` (a **plain** Clean `Ensemble` — 25 chips + 11 boundary/provider tables, four buses,
`sp1StateVerifier` pull-final/push-init boundary), with `sp1_machine_soundness` restated over its
`Statement` and the decode seam re-anchored to `EnsembleWitness sp1Ensemble`.
`GatedVm/{Defs,Formal}.lean` deleted; `GatedVm/BalanceMod.lean` **relocated verbatim** to
`Model/BalanceBridge.lean` (⚠ the item-7 claim "Clean `Air/Balance` ⊇ `BalanceMod`" was wrong on
inspection — Clean's balance layer is field-level only; the field→ℤ bridge exists nowhere upstream, so
it moved rather than dissolved). `GatedVm/{Chain,StateBridge,Capstone,SailDispatch,Bridge}.lean` (the
Eulerian-trail machinery, the `GatedVm` *namespace*) are unchanged. Why a plain `Ensemble`, not
`SoundEnsemble`/`addVm`: post-memory-flip every chip's `channelsWithGuarantees` contains
`memoryChannel`, which can never be finished (pull-then-push) and `addVm` is single-VM-channel — see
the module doc of `SP1Clean/Soundness/SP1Ensemble.lean` and the parked `sp1StateVmEnsemble` note in
`Soundness/StateVm.lean` (un-parking = roadmap W11 path A, the multi-VM `VmTables` generalization).
Memory boundary (Phase 4): `MemoryProviderChip` (init-push, boolean mult) + `MemoryFinalizeChip`
(finalize-pull, new) + the native finalize twin in `Soundness/MemoryGlobal.lean`
(`memFinalizeContributions`, `memProviderGenesis_of_boundary`) + `memBalanceHyps_of_boundary`
(`Soundness/MemoryIsU64.lean`). Remaining in-flight: the byte/program finished-channel grounding lemma
`sp1_finishedChannel_guarantees` (P5.4, separable — the capstone is green without it; it feeds the
seam's per-chip `FullGuarantees`).

## Commits so far
- `07597ba` — Clean→main migration baseline + the in-circuit byte/range providers (superseded, see below).
- `af0a115` — Phase 0 feasibility findings (faithfulness + scale gates, both favorable).
- `51801c3` — **Phase 0c cwr sweep**: every byte-touching consumer drops `byteChannel` from
  `channelsWithRequirements`, discharging the off-gate pull-`Requirements` via a local **shallow**
  `assertZero (is_real*(is_real-1))` gate (faithful — SP1 `assert_bool`s locally everywhere). `byteChannel`
  is now FINISHABLE.

## DONE
- **Phase 0a/0b** — feasibility validated: the cwr reconciliation is faithful (SP1 local `assert_bool`);
  `mapFinRange` providers scale (Clean reasons symbolically, constant ~1.8s to N=65536).
- **Phase 0c (cwr sweep)** — the load-bearing unblocker, COMPLETE across all 49 consumers (3 leaf readers,
  13 ops, 7 composed readers, 25 chips + 1 op AddOperation pilot). Validated templates A/B/C are in
  `docs/agents/bytechip-provider-design.md` and the scratch `CWR_SWEEP_SPEC.md` (in the session scratchpad).

## LEFT (in order)
1. **Generator reproducibility follow-up (do first — small).** `update_extracted.py` must emit the
   `is_real` boolean gate (first assert, `x*(x-1)` shape) as `assertZero <expr>` instead of `<expr> === 0`,
   AND **add** that gate for byte-pulling ops whose SP1 eval emits none (BitwiseOperation, MulOperation;
   the Native `U16toU8OperationSafe` is hand-written). Otherwise a regen reverts Phase 0c on those. Verify
   a regen reproduces `Extracted/` byte-identical modulo the gate.
2. **Phase 0c remainder — byteChannel as `StaticLookupChannel`.** Define `byteStaticTable :
   StaticLookupChannel (ZMod p) ByteRow` (`name "SP1Byte"`, `Guarantees := ByteRowSpec`, `table` = the
   enumerated valid byte rows, `guarantees_iff : ∀ msg, ByteRowSpec msg ↔ msg ∈ table`) and
   `byteChannel := Channel.fromStatic _ _ byteStaticTable` in `Model/Channels.lean`. `byteChannel` stays
   definitionally identical (same name + Guarantees), so downstream is unaffected; the new `table` +
   `guarantees_iff` feed the provider. The `guarantees_iff` over the enumerated table (≈460k rows across
   opcodes 0–6, built via `List.range`/`flatMap`, characterized — NOT enumerated in the proof) is the work;
   reuse `Model/ByteTable.lean`'s `byteRowSpec_*` lemmas + `Proofs/Chips/ByteChip/Provider.lean`'s split.
3. **Phase 1 — byte provider table.** `pushBytes`-style `GeneralFormalCircuit` (template:
   Clean `Examples/FibonacciWithChannels.lean:43`) pushing the static rows with witnessed multiplicities
   over the `(b,c)` byte-op + `(a,bits)` range domains; wrap as a `Table`/`Component`; soundness via
   `byteStaticTable.guarantees_iff`. **REMOVE the in-circuit `Proofs/Chips/ByteChip/{ByteChip,RangeChip}.lean`**
   (built in `07597ba`, superseded by this) — they're the 2 files still keeping `byteChannel` in cwr.
4. **Phase 2 — 25 chips as a State `VmTables`.** Add `exposedChannels` to each chip `circuit`
   (`expose stateChannel [pulledIf is_real cur, pushedIf is_real next]` + `exposedChannels_eq`; idiom
   `FibonacciWithChannels.lean:152`); switch CPUState's State receive `emit (-is_real)` → `pullIf is_real`;
   define `sp1StateVm : VmTables` (`tables_channel`/`verifier_channel`/`verifier_requirements`).
5. **Phase 3 — Program ROM provider** (`StaticLookupChannel` over the loaded `GuestProgram`;
   `Proofs/Chips/ProgramChip.lean` has the predicates, no circuit).
6. **Phase 4 — Memory closed bus** (hardest; NOT a static table — init/finalize boundary tables;
   `Proofs/Chips/MemoryProvider.lean` has predicates, no circuit; keep `MemoryConsistency`/`MemoryIsU64`).
7. **Phase 5 — capstone replacement.** Assemble `sp1SoundEnsemble` (`SoundEnsemble.empty |>.addTable
   ⟨byteProvider⟩ |>.addFinishedChannel byteChannel |> … |>.addVm sp1StateVm |>.toFormal`); delete
   `Soundness/GatedVm/{Defs,Formal,BalanceMod}.lean` (generic plumbing now upstream), KEEP
   `Chain/StateBridge/Capstone/SailDispatch` (the SP1 Eulerian trail); rebuild `sp1_machine_soundness`
   sourcing bus balances from the finished channels (Clean `Air/Balance` ⊇ `BalanceMod`'s W1a), discharge
   `TraceByteLink`/`TraceProgramLink`/`TraceMemoryLink` via the existing `*_of_balance` theorems, and
   restructure the `sp1_witness_decode` seam for the new `SoundEnsemble` witness shape (the sorry stays).

## Key learnings / gotchas (don't relearn these)
- **Shallow vs deep gate:** `X === 0` composes the Equality SUBCIRCUIT (deep), invisible to
  `ConstraintsHold.Shallow` → `requirementsChannelsLawful` can't use it. Use inline `assertZero X`. This is
  why the ops' extracted `E1 === 0` gate had to become `assertZero E1`. (Clean's `fib8` has the same caveat
  in-source.)
- **Gate-only, not all-asserts:** converting carry/product asserts (with `65536⁻¹`/inverses) to `assertZero`
  clogs `grind`'s ring solver. Convert ONLY the `is_real` boolean gate.
- **`requirementsChannelsLawful` recipes:** leaf/with-gate → `simp only [circuit_norm, main, byteChannel,
  <other cwr channels>]; grind`. Composed (cwr `[]`) → default re-closes (omit). Many-pull / subcircuit
  cases → `refine ⟨List.nil_subset _, fun env hgate => ?_⟩; have hbool := bool_of_mul_pred hgate;
  and_intros <;> exact fun h1 h0 => off_gate_vacuous hbool h1 h0` (`bool_of_mul_pred` `Math/Word.lean`,
  `off_gate_vacuous` `Math/Gate.lean`). Non-empty residual cwr → split the subset conjunct, don't use
  `List.nil_subset`.
- **Provider modeling decision (user):** `StaticLookupChannel` (faithful to SP1's preprocessed tables),
  FULL replacement of `GatedVm` (not additive). Keep the four-bus model, gated multiplicities, the trail.
- **`addVm_soundVmChannel_of_soundChannels`** (Clean `Air/Vm.lean:703`) is the soundness engine; it needs
  every finished channel `Consistent` (free for typed channels) + `SoundChannels` (the providers).
