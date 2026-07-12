# Consolidation progress — live status board

**This is the single source of truth for migration progress.** Task *detail* lives in
[`2026-07-architecture-consolidation.md`](2026-07-architecture-consolidation.md) (§5 steps, §3.x
designs, §9 spike results); this file is the live index of *what is done*. The acceptance test is
[`../overview.md`](../overview.md): each `[PENDING: step N]` marker there is a task's finish line —
when a task lands, its claim moves verbatim from [`../goal-overview.md`](../goal-overview.md) into
`overview.md` and the marker is deleted.

## Update protocol (so parallel work doesn't collide)

- To **claim** a task: set its Status to `WIP (sid:<short session/agent id>)`.
- On **completion**: set `DONE (<commit sha>)`.
- On a **blocker**: set `BLOCKED (<one-line reason>)`.
- One task = one row. Keep rows in ID order; **never renumber** (subagents/sessions cite IDs).
- Every Lean-touching task ends with a green `lake build SP1Clean` (0 errors / 0 warnings / no stray
  `info:`) + `#print axioms` clean + `check_no_native_decide.sh`/`check_no_skipkerneltc.sh` before DONE.

## Track legend

**F** foundations (step 0) · **X** faithfulness (∥) · **D** docs (∥) · **K** Clean/deps (∥, merge gated) ·
**P** remaining spikes (∥) · **S** sequential spine (steps 1–7). `∥` = parallel with other tracks.

---

## Track F — Foundations (proposal step 0)

| ID | Task | Status | Depends | ∥ | § |
|----|------|--------|---------|---|---|
| F1 | Delete `Soundness/StateVm.lean` + scrub 3 stale comments | DONE (uncommitted; build-pending via F3) | — | ✅ | §2.8, §4 |
| F2 | FROZEN banners on 9 legacy-path module docstrings (GatedVm ×5, TargetVm, RowEffectDefs, ValueBound, InstructionTrace) | DONE (uncommitted; 4.28 build green) | — | ✅ | §5.0 |
| F3 | Shared `Fact (2^24<p)→Fact (2^17<p)` in `Math/Word.lean` + sweep local sites / 39 files (no `omit` breakage) | DONE (uncommitted; 4.28 build green) | — | ✅ | §2.8, §3.3 |
| F4 | SP-3 field bounds: dormant `Fact (2^25<p)→Fact (2^24<p)` derivation infra in `Math/Word.lean` (machine-level bump deferred to S4) | DONE (uncommitted; 4.28 build green) | F3 | ✅ | §3.3, §9/SP-3 |
| F5 | `timeOfStep`/`clkInc` in `MicroTime.lean`; restate `StateTruth`+`microValue` off the hardcoded 8 | NOT STARTED | — | ⚠ | §3.5, §2.8 |

## Track X — Faithfulness macro sweep (SP-5 done)

| ID | Task | Status | Depends | ∥ | § |
|----|------|--------|---------|---|---|
| X1 | Four `faithful_syntactic_<bus>` macros + `vecN_eq_iff` infra in `Faithful/ChipTactics.lean` | NOT STARTED | — | ✅ | §3.6, §9/SP-5 |
| X2 | Convert ~15 chips to syntactic anchors, by class batch | NOT STARTED | X1 | ✅ | §3.6 |
| X3 | Exception — Mul byte anchor (chunked list-equality) | NOT STARTED | X1 | ✅ | §9/SP-5 |
| X4 | Exception — DivRem fragment anchors (deferrable) | NOT STARTED | X1 | ✅ | §9/SP-5 |
| X5 | Delete `Interaction.toProp` + `forall_append_*` + semantic anchors + `faithful_chip_interact` | NOT STARTED | X2,X3,X4 | — | §3.6 |

## Track D — Docs convergence

| ID | Task | Status | Depends | ∥ | § |
|----|------|--------|---------|---|---|
| D1 | HISTORICAL banner on `docs/bus-model.md` | DONE (uncommitted) | — | ✅ | §8 |
| D2 | Ongoing: move claims `goal-overview.md`→`overview.md`, delete PENDING markers as steps land | ONGOING | per-step | ✅ | §8 |

## Track K — Clean / deps (prepare in parallel; merge gated to post-cutover)

| ID | Task | Status | Depends | ∥ | § |
|----|------|--------|---------|---|---|
| K1 | Document the 3-line Sail fork delta as a re-appliable patch (`docs/agents/sail-fork-delta.md`) | DONE (uncommitted) | — | ✅ | §7.5 |
| K2 | PR `riscv-lean` chores to opencompl → drop that fork | NOT STARTED | — | ✅ | §7.5 |
| K3 | Ask/PR opencompl `sail-riscv-lean` for build-time platform-config parameterization → drop that fork | NOT STARTED | — | ✅ | §7.5 |
| K4 | Local Lean 4.30 bump (Clean + Sail deps) — **brought forward** per user (shift-left the breakage) | WIP (in place) | — | — | §7.5 |

## Track P — Remaining de-risk spikes

| ID | Task | Status | Depends | ∥ | § |
|----|------|--------|---------|---|---|
| P6 | SP-6: intra-row same-location touches preserve layer-B induction? | NOT STARTED | — | ✅ | §9/SP-6 |
| P8 | SP-8: channel-reversion dry-run + hygiene guarantees | NOT STARTED | — | ✅ | §9/SP-8 |

## Track S — Sequential spine (steps 1–7)

| ID | Task | Status | Depends | § |
|----|------|--------|---------|---|
| S1 | Decode Moves 1+2 + seam-chip advances → advance 25/25 | NOT STARTED | F-track | §3.4 |
| S2 | Structured `Ready` + total `advance`; delete dual contract/dispatchers | NOT STARTED | S1 | §3.3 |
| S3 | `stepFact_of_advance` adapter + `RowWiring` + shape lemmas | NOT STARTED | S2 | §3.2 |
| S4 | Productionize `TimedGrounding` engine (MemLoc, clk_inc, RamWriteReassembly, field→ℕ time) | NOT STARTED | S3, P6 | §3.2 |
| S5 | Seam swap `sp1_row_facts_decode` + typed-multiset bridge (SP-4) | NOT STARTED | S4 | §3.2 |
| S6 | Cutover deletion series + channel reversion (P8) | NOT STARTED | S5, P8 | §5.6 |
| S7 | Fused `sp1_soundness` + `SP1Boot` + program-parameterized ensemble + axiom gate; fix TB-10 | NOT STARTED | S6 | §3.1, §6 |

---

## What's safe to run autonomously right now — Batch 1

- **Zero-build, fully autonomous**: F1, F2, D1, K1.
- **Mechanical, one verifying build**: F3+F4 (together), then F5; X1 on disjoint `Faithful/` files.
- After Batch 1: one green `lake build SP1Clean`, then update every row's Status here.

**Clean update timing** (REVISED 2026-07-09 per user): the 4.30 bump is **brought forward to now**,
done in place against local editable copies, to surface Clean-API + Sail-generation breakage early.
Proper published dep pins get restored before the PR merges (user handles).

### 4.30 migration state (K4) — live
- `lean-toolchain` → **v4.30.0**; `lakefile.toml` mathlib → **v4.30.0**; Clean/LeanRV64D/RISCV → **local path deps**
  (`../clean` 4.30, `../sail-riscv-lean` 4.30 + platform delta, `../riscv-lean` 4.30).
- External prep DONE: 3-line SP1 platform delta applied to `../sail-riscv-lean`
  (`plat_have_clint`/`plat_have_sig`→false, `sys_pmp_count`→0); `../riscv-lean` toolchain→4.30.
- Sail stack builds on 4.30 (user-verified `sail-riscv-lean`; ⇒ `lean-sail` v4 source is 4.30-clean).
- The 4.28-green baseline (Wave A + Batch 1) is recoverable by reverting `lakefile.toml` + `lean-toolchain`.
- DONE: mathlib-4.30 cache present (no source build); Clean 4.30 builds from source; manifest coherent
  (single `Lean_RV64D` path dep after the name fix).
- **Pass-1 build finding (KEY):** 62 errors, and **~51 of the ~57 SP1Clean errors are in just two files —
  `Model/VmChannel.lean` (~37) + `Model/InteractionRecovery.lean` (~14) — exactly the Clean-fork clone +
  ℤ-stack the consolidation DELETES** (§3.5/§3.2). The 4.30 pain validates the proposal's thesis. Decision:
  **port to 4.30-green now, delete in the consolidation later** (compounding the 25-chip channel-reversion
  into an unspiked toolchain migration is the "two migrations at once" hazard). Foundational fixes:
  `IntRange` (lean-sail, 2 errs) + one `omit` 4.30-change (DONE — `DivRemChip/Soundness.lean:537`).
- **ROOT CAUSE (great news):** the entire Clean 4.30 breaking change is **`[Field F]` → `[FiniteField F]`**
  (`FiniteField extends Field`; `F p`/`ZMod p` with `[Fact p.Prime]` auto-synthesizes it). NO renames, NO
  Witgen-IR surface, NO semantic changes. Only files *generic over `[Field F]`* break — and there are just
  **three** in all of SP1Clean: `VmChannel`, `InteractionRecovery` (DONE — subagent, 0/0, axiom-clean),
  and `Channels.lean` (DONE — 2 lemma binders strengthened). 266 files over `Fact p.Prime` are unaffected.
- Fixed: `VmChannel`+`InteractionRecovery` (Field→FiniteField, 0/0 axiom-clean) · `Channels.lean` binders
  · the one `omit` (`DivRemChip/Soundness:537`).
- **PASS 2 RESULT: all of SP1Clean builds on 4.30** — 62 → **7 errors, all in `lean-sail`'s
  `Sail/IntRange.lean`** (+ 8 warnings, also all in IntRange, same root cause). NO generation drift, NO
  chip breakage, NO `Extracted/` regen. The whole SP1Clean-side 4.30 migration was 3 binder strengthenings
  + 1 `omit`. Spectacular for a 4.28→4.30 + 105-Clean-commit jump.
- IN FLIGHT (last blocker): subagent setting up editable `../lean-sail` + fixing `IntRange` (4.30 changed
  `simp [instMemIntRange]`'s membership unfold → breaks the `Decidable` instance + 4 `omega` termination
  proofs; fix = a `mem_def` simp lemma). Same root cause clears all 7 errs + 8 warns.
- **REMAINING BLOCKER = dep-version skew (user-reserved "deps" call).** The SP1Clean-side migration is
  DONE (3 binders + 1 omit). `lean-sail` red herring resolved (correct copy is `79b4d08`, cloned to
  `../lean-sail`, builds clean at 4.30 as-is). But `../riscv-lean@e65c352` pins `sail-riscv-lean@1c5153dd`,
  while `../sail-riscv-lean` is the newer `793034f3`; the Sail generator reorganized namespaces AND changed
  definitions between them. Namespace part fixed (`open LeanRV64D.Defs` added to riscv-lean's
  `SailPure.lean`+`Skeleton.lean`), but `SailToRV64`/`SailPureToInstructions` (the `mul_eq`/`RV64.*_eq`/
  `rtypew_sraw_eq` lemmas SP1Clean's Mul/AluX0/ShiftRight bridges import) now have ~99 PROOF breakages
  vs `793034f3`. Pass-2's "SP1Clean green @793034f3" was on INCONSISTENT oleans (stale riscv-lean built
  for `1c5153dd`), so it doesn't validate `793034f3` for the full Sail surface.
  - **Option A (recommended):** standardize on `sail@1c5153dd` (riscv-lean's pin; likely what SP1Clean's
    original succinctlabs generation matched) — reset `../sail-riscv-lean`→`1c5153dd`, re-apply the 3-line
    platform delta + 4.30 toolchain; riscv-lean builds unpatched; then fix any SP1Clean direct-LeanRV64D
    breakage (likely small). Discards the `793034f3` checkout state.
  - **Option B:** keep `793034f3`, re-port riscv-lean's ~99 proof breakages (risks changing riscv-lean's
    public API → SP1Clean bridge breakage). Bigger, uncertain.
  - **DECISION (user): Option B — keep `sail@793034f3`, port riscv-lean up to it** (as a potential upstream
    riscv-lean→newer-sail contribution, ties into K2). In progress:
    - Namespace sweep DONE: `open LeanRV64D.Defs` added to riscv-lean `SailPure`/`Skeleton`/`SailToRV64`/
      `SailPureToInstructions` (the moved names — `xlenbits`/`zero_extend`/`Signedness`/`VectorHalf`/the
      `rop`/`iop`/`uop`/`sop` AST enums + `SailM` — all live in `LeanRV64D.Defs` now). **205 → 25 errors.**
    - Residual (subagent in flight): `shift_right_arith` removed → `shift_bits_right_arith` (Prelude:410);
      ~20 genuine proof breakages (simp/rewrite/rfl/omega) from generation drift, in `SailPureToInstructions`
      + `SailToRV64`. Public lemma statements SP1Clean imports (`mul_eq`/`mulw_eq`/`RV64.*_eq`/`rtypew_sraw_eq`)
      held FROZEN — proofs only.
- **riscv-lean port DONE** (0/0, 140 jobs; public lemmas `mul_eq`/`RV64.*_eq`/`rtypew_sraw_eq` frozen;
  `shift_right_arith`→`shift_bits_right_arith`; ~20 proof repairs for Int-typed-shift generation drift).
- **NEXT LAYER surfaced (was masked by stale oleans): SP1Clean-side generation drift.** Full build now
  fails at `Model/Register.lean` — `RegisterType`/`nextPC`/`arch_pc` moved to `LeanRV64D.Defs` in 793034f3;
  **34 SP1Clean files** (26 chip `Bridge.lean` Sail bridges + `Register`/`Advance`/`TryStepReduction`/
  `SailMemory`/`Witness`) use them unqualified. Same `open LeanRV64D.Defs` fix as riscv-lean.
  - Namespace sweep DONE (all 34 files, `open LeanRV64D.Defs`; the earlier 2 sweep failures were a zsh
    no-word-split quirk). `Register.lean` cleared. But the build now stops at `SailWrap.lean` (maxErrors)
    on REMOVED/renamed symbols (`Sail.readReg`/`writeReg`, `SailME.run`) + ~56 cascade `rfl`/proof fails —
    i.e. B's real cost is a **generation-drift port of SP1Clean's whole Sail layer** (`SailWrap`/`SailDecode`/
    `SailMemory`/`GuestProgram` + 26 bridges + `Advance`), uncertain depth.
  - **DECISION (user, informed): continue on sail@793034f3 — port SP1Clean's Sail layer to the newer gen.**
    Wave plan: (Wave 1) foundational `Model/` Sail files; (Wave 2) the 26 chip `Bridge.lean` files. All
    STATEMENTS frozen (specs/soundness/`correct_<op>_native` anchors); proofs + refs only.
  - **WAVE 1 STATUS (partial, PAUSED for direction):** `SailWrap`/`SailDecode`/`GuestProgram`/`Advance`/
    `TryStepReduction` reconciled (no `sorry`; `Sail.readReg`/`writeReg`→`PreSail.*`, monad-shape).
    `SailMemory.lean` NOT converged — **17 errors** (build clean-errors, no hang), mostly
    `unfold ext_data_get_addr failed` (the fn still exists at `AddrChecks.lean:227` — likely a namespace
    ambiguity introduced by the broad `open LeanRV64D.Defs` sweep + real memory-model drift) + `unsolved
    goals`/`rewrite pattern` cascades. `SailMemory` rewritten +481/−138 lines by the port agents.
  - **PROCESS NOTE / CAUTION:** the SailMemory port spiraled into NESTED subagents (~700K+ tokens), one
    STALLED/failed; do NOT re-delegate blindly — finish `SailMemory` under direct control (17 errors), and
    handle the 26 bridges with tightly-scoped single agents (no nesting).
  - **OPEN RECOMMENDATION (main agent):** the empirical cost of B is now extreme (SailMemory alone unfinished
    after ~700K tokens; 26 bridges ahead). Option A (reset `../sail-riscv-lean`→`1c5153dd`, the generation
    SP1Clean was written for) would likely dissolve the whole SailMemory/bridge port for near-zero work — a
    local-dev version choice, revertible. Flagged to user; awaiting their call (continue B under control, or
    switch to A, or revert to the 4.28-green baseline and defer 4.30).
- **PLAN APPROVED (`finish the Sail-update port`): staged, NO nested agents.** Stage 1 = SailMemory 17 errs
  (precisely diagnosed: 8 `unfold` sites need the new `get_transformed_data_addr`/`transform_effective_address`
  wrappers + `pm_transform_*`/`get_pmlen` simp; 3 `checked_mem_write` narrow-width double-`zero_extend` shape;
  4 fetch-path simp refresh). Stage 2 = 26 bridges, dominated by the `Sail.readReg`/`writeReg`→`LeanRV64D.*`
  rename (Tier A 8 ALU trivial / Tier B Jal/Branch/AluX0/DivRem / Tier C shift+mul+10 memory).
  - **Stage 1 (SailMemory):** 7/15 lemmas fixed (fetch path + narrow `checked_mem_write`). The other 8
    (`run_vmem_read/write_of_width_*`) hit a **genuine semantic addition in sail@793034f3: pointer masking
    (PMM)**. `transform_effective_address` now masks the addr by `mseccfg[33:32]` (0b01 → *throws*), so the
    lemmas are false unless PMM is pinned. No fork toggle exists (`is_pmm_applicable` is unconditional for
    M-mode data). **FIX (user-approved): add `h_mseccfg_pmm` (`mseccfg[33:32]=0` = PMM disabled) to
    `SailState.isValidMemConfig`** — a NEW platform assumption in the trust base, faithful (SP1 has no
    pointer masking; consistent with the existing MPRV-off/`mseccfg[10]=0`/CLINT-off assumptions). NO
    init-grounding (isValidMemConfig is the assumed initial platform config, a bridge-level hypothesis;
    per user we just need the bridging). IN FLIGHT: single non-nesting agent adds the field, fixes the 8
    lemmas (PMM=Disabled → transform=identity → existing proof closes), threads it through the 10
    memory-bridge transfer sites. **TODO on landing: disclose the PMM assumption in the trust-base docs
    (`lean-sail-notes.md` / audit) alongside the CLINT/MPRV/PMP platform assumptions.**
  - **NEW WAVE exposed (pass 7, after Model layer went green): Clean-4.30 circuit-drift** in the
    Proofs/Operations + byte/provider layer (~124 errs), HIDDEN in pass 2 by inconsistent oleans (wrong
    lean-sail). So "Field→FiniteField was the whole SP1Clean breakage" was too optimistic. Kinds/known fixes:
    (a) the `x + -1*y → x - y` `circuit_norm` normal-form change (proposal §7.5) → the 8 operation `Formal`
    proofs' `rw` patterns use the old `+ -` form (Add/Sub/AddrAdd/U16MSB/U16Compare/UNtoUN/UNMSB/UNCompare);
    (b) Clean channel-API drift `requirementsChannelsLawful` synth-fail + LCNF/Function-expected cascades in
    `ByteChip`/`RangeChip`/`Memory{Provider,Finalize}Chip`/`ProgramProviderChip` (per clean-main-migration.md);
    (c) `InteractionProjection` reduction drift + `TryStepReduction:161` monad-shape. IN FLIGHT: one
    non-nesting agent. Then the bridges (Stage 2b) once these clear.
  - **Missed-open stragglers caught (mechanical):** `Decode.lean` ×2 (AST symbols) + Truth/ChipRow/
    AdvanceDispatch/AddRow/RowEffectDefs (Register.<Ctor>) — my keyed sweeps missed them; all now have
    `open LeanRV64D.Defs`. Model layer now GREEN.
  - **SailMemory DONE: 0/0 (3093 jobs), axiom-clean** (PMM fix added NO new axiom — it's a hypothesis in the
    assumed config, not a Sail hook). All 8 vmem lemmas proved via transform-identity helpers. `h_mseccfg_pmm`
    threaded through the 10 bridge transfer sites + the consequential `SailConfigured`/`toValidMemConfig`
    construction sites (`GuestProgram`/`Advance`/`Witness`/`TryStepReduction`). Residual Model-layer stragglers
    from the earlier partial Wave 1 (NOT from this fix): `Decode.lean` (dotted-identifier drift),
    `TryStepReduction.lean:161` (`run_readReg` rw) — cleared in the full-build pass next. Then Stage 2b bridge tiers.
  - **Stage 2a DONE:** global `Sail.readReg`/`writeReg`→`LeanRV64D.readReg`/`writeReg` rename applied across
    all 25 bridge files (218 sites; `Sail.run_readReg_bind` untouched) — verifies once Stage 1 unblocks builds.
- **CHECKPOINT COMMITTED: `a5f900fe`** (115 files) — WIP 4.30 migration + consolidation-audit docs. Recoverable.
- **Current tree state: RED, 46 errors** — all in the HARD CORE (the easy/mechanical layers are done):
  (1) Witgen-IR `witnessVector` closure→VExpr rewrite (`Native/Operations/AddressOperation.lean` + the 3
  readers `CPUState`/`MemoryAccess`/`RegisterAccessTimestamp` + `MulOperation/RawSpec` residual);
  (2) 4.30 Vector-reduction regression (`InteractionProjection`, `LtOperationSigned/RawSpec` — `#v`/`toElements`
  getElem/append won't reduce, element-wise workaround whnf-explodes — maybe wants an UPSTREAM Clean helper);
  (3) DivRem kernel-recursion blowup (`Euclid`/`Extract` — `2^80+`% terms; needs the abstract-BitVec-helper
  refactor); (4) the 26 chip bridges (Stage 2b, gated behind the above; rename applied).
- **USER DECISION: checkpoint + commit (done: a5f900fe), then PLAN the hard core.** SCOPED (3 Explore agents) —
  **all 4 items are bounded LOCAL fixes, no framework rewrite / whnf explosion / upstream Clean:**
  1. **Witgen-IR** (AddressOperation 2 sites): `witnessVector`→`witnessVectorNative` escape hatch (0 proof edits). S.
  2. **Vector regression** (InteractionProjection ×7, LtOperationSigned ×1): add `Vector.toList_map` to the simp
     sets (not `@[simp]` in 4.30 → `.toList` won't distribute over `Vector.map`); `simp only`→`simp` for the
     `ite`-`Decidable`-arg case. ~1 line each, LOCAL. S.
  3. **DivRem** (Euclid ×3): literal-mask `2^80/96/112` before `omega` (4.30 `Nat.pow` norm change). Extract ×1:
     unrelated `circuit_norm` simp drift (`simp?`-fix). S.
  4. **Readers ×3 + MulOperation/RawSpec**: NOT witnessVector (readers have none) — different 4.30 error, 1-min
     diagnose (likely same Vector/simp class). S.
  5. **Bridges (25)** Stage 2b, gated behind 1-4: Tier A 8 trivial rebuild · Tier B 17 medium by family
     (shift 2 / mul-div 3 [RISCV.SailToRV64 importers] / memory 9 / control 2). M.
  - **Operations/Model batch: 7/8 DONE** (AddressOperation [rename + 3 extra normal-form fixes],
    LtOperationSigned, DivRem Euclid [`fill_digit` helpers] + Extract [`fromStruct` unfold], 3 readers
    [normal-form], MulOperation [no-op] — build green together, 3214 jobs).
  - **1/8 harder than scoped: `InteractionProjection.lean` (7 kernel lemmas).** 4.30 changed
    `ProvableStruct.combinedSize'` → `List.sum ∘ List.map size`, so the `toElements`-flattened vector's
    `toList`/`getElem` size index no longer presents as `m+n` → `Vector.{toList,map,getElem}_append`/`_cast`/
    `_mk` don't fire; brute `ext` closes 4/5-field kernels (~2-8M hb) but 9/16-field memory/program exceed 8M.
    IN FLIGHT: focused non-nesting agent on the proper per-index reduction (`getElem_eval_toElements`), with a
    big-heartbeat fallback since this is ℤ-bus-stack code the consolidation DELETES (§3.2) — won't over-invest.
  - **InteractionProjection DONE (elegant, not fallback): MODEL LAYER FULLY GREEN** (`lake build SP1Model`,
    3144 jobs, default heartbeats, axiom-clean). Fix: per-message `toList` helpers using `change` to
    re-elaborate `toElements` as explicit right-nested appends (defeq-cheap, syntactic `+`-index so
    `Vector.toList_append` distributes in O(#fields)). Added reusable `{state,memory,program}Msg_toList`/
    `byteRow_toList` helpers.
  - **NEXT (revealed): more `(a + -b)` vs `(a - b)` normal-form drift** in the layer below the bridges —
    `Native/Readers/{ALUTypeReader[Immutable],ITypeReader[Immutable],RTypeReader,JTypeReader}` +
    `Faithful/{CPUState,U16toU8OperationSafe}` + `Proofs/{DivRemChip/Assembly,Operations/LtOperationSigned/Formal}`.
    SAME known mechanical `sub_eq_add_neg` pattern (the normal-form wave keeps surfacing as the build advances).
  - **Layer-by-layer grind (the 4.30 drift is pervasive but bounded; each green layer reveals the next):**
    Model ✅ · Native/Readers + Operations ✅ · 14 chip `Defs` `witnessVector`→`Native` ✅. NEXT (in flight):
    Faithful anchors (pattern #1) + remaining chip `Defs` (2 more renames: `ProvableType.witness`→`witnessNative`,
    `witnessField`→native). THEN the chip `Formal`/`Soundness` tier — this one has **genuinely-new proof-repair**
    (`rw` `motive is not type correct` from 4.30 dependent-motive strictness → known remedy `have h:=…; simp only
    [...] at h`; + simp/type-mismatch/instance-synth in `Soundness/{Program,Memory}Consistency`). THEN the 25
    bridges (Stage 2b). No NEW mystery classes — all known/known-remedy; it's a multi-batch grind, converging.
- AFTER SP1Clean green: migration done (modulo known `sp1_witness_decode` sorry) → resume consolidation on
  4.30 (F5/X1/spine); K1–K3; refresh AGENTS.md/lean-sail-notes off the stale 4.28 pins.

## 2026-07-10 — near-green: only the 5 ALU/control Sail bridges remain

Drove the layer-grind to the finish. Error trajectory across authoritative full builds: **167 → 40 → 97 → 15
→ 49 → (in flight)**. Root causes were exactly two mechanical classes plus Sail-model drift:

- **Class 1 — circuit_norm normal-form flip `x + -1` → `x - 1` (Clean 4.30).** Fixed uniformly: the shared
  `Word.bool_of_mul_pred` + `Faithful.ChipTactics.bool_iff` now take the `x*(x-1)=0` form; deleted the many
  now-counterproductive `simp only [sub_eq_add_neg] at <hyp>` (un-normalizes) and `simp only
  [← sub_eq_add_neg]` (now no-op → "made no progress") lines; flipped internal booleanity `have`/lemma
  statements `+ -1`→`- 1`; closed the residual seams with `linear_combination` where the producer form is
  genuinely `+ -1` (e.g. LoadX0). Landed: all 6 readers, ~10 Operations (Add/Sub/Addw/Subw/AddrAdd/Lt*/U16*),
  Faithful/ChipTactics, and — via 3 parallel non-nesting proof-repair agents — the chip `Formal`/`Soundness`
  tier (UType/AluX0/Sub/Addi, Jal/Jalr, ShiftLeft Sll/Sllw, ShiftRight Defs) + the memory chip `Formal`
  (LoadX0/LoadWord/LoadByte/LoadDouble).
- **Class 2 — stricter dependent-motive `rw`.** `rw [h1,h2]` under `Vector`/`populate` binders → `simp only
  [h1,h2]` (Add/Addi/Sub/Addw/Jal/Jalr completeness).
- **Sail-model drift (`Proofs/Sail/Advance.lean`, memory bridges).** `Sail.assert`→`PreSail.assert` (all load/
  store bridges); the load-path assert `if (1≤b8)=true …` reduces with `Nat.reduceLeDiff, decide_true` (the old
  `show ((1:ℕ)≤b8)=true` didn't match `decide (1≤8)`); the `wX` write-back `if rd_idx=0#5` is a non-`ite` split
  → `split <;> first | rfl | exact absurd ‹rd_idx=0#5› hrd`; `get_reg?_writeBack` cast cancel → `grind
  [reg_idx_must_64]`; reflexive `X=X` after the final `simp` → trailing `rfl`. **Advance.lean fully green.**
  Also fixed a mangled `PreLeanRV64D.readReg`/`writeReg` token (bad prior rename) → `LeanRV64D.*` across 13
  bridge files.

**Remaining (IN FLIGHT, 1 non-nesting agent):** the 5 ALU/control Sail bridges — `AddChip`/`AddiChip`/`AddwChip`/
`JalChip`/`AluX0Chip` `Bridge.lean`. Root cause: the flat `simp` relied on the old Sail-execute defeq shape;
the new model leaves `EStateM.run (readReg …) s` / `SailState.get_reg? s rs_idx` / the `wX` write-back unthreaded.
Fix = mirror the GREEN memory bridges (LoadX0Chip/LoadDoubleChip Bridge) using the `Model/SailWrap.lean`
run-lemmas (don't unfold `LeanRV64D.readReg`, let `@[simp] run_readReg`/`run_writeReg` fire) + trailing `rfl`.
Warnings sweep (~40, mostly `id_eq`/unused-simp from 4.30) pending after errors hit zero.

## 2026-07-11 — 4.30 migration at ~31 errors; ONE hard root cause remains (the completeness Witgen-IR blowup)

Full-build trajectory across authoritative builds: **167 → 40 → 97 → 15 → 49 → 106 → 35 → ~31**. Everything
green EXCEPT the complex-chip **completeness** proofs (Bitwise/Lt/Branch/Mul/DivRem) + `DivRemChip/Soundness/
Tail.lean`. This wave landed: ShiftRight Formal (54) + Soundness Srl/Sra/Srlw/Sraw (56), ShiftLeft Formal,
StoreByte, all Sail bridges incl. Shift (readReg-unfold template), Lt/Branch/Bitwise concrete type-errors,
the warning sweep (48 unused simp args), the `cannot omit referenced section variable` class (Load bridges),
and the `MulOperation/RawSpec` `omit [Fact (2^24<p)]`.

### The remaining blocker (well-characterized, hard, verification-bottlenecked)

**Symptom:** `(deterministic) timeout at whnf, 32M heartbeats` in the per-cell equality of the complex-chip
completeness proofs. Pattern (BitwiseChip/Formal.lean ~283-288, mirrored in Lt/Branch/Mul/DivRem):
```
refine (ProvableType.ext_iff _ _).mpr (fun i hi => ?_)
refine Eq.trans ?_ ((getElem_toElements_eval_varFromOffset env.toEnvironment (i₀+3) i hi).trans (h_env_cols ⟨i,hi⟩))
simp [circuit_norm]
```
**Root cause:** Clean 4.30 changed `ProvableStruct.combinedSize'` to `List.sum ∘ List.map size`, so the
`toElements (populate …)` Vector tower no longer structurally reduces. `h_env_cols i` is
`env.get (i₀+3+i) = ((WitgenIR.nativeValue fun env ↦ populate (Vector.map (eval env) op_b_var) …).eval env)[i]`
— an **unreduced native closure** where the operands are `map (eval env) op_var`, which equal `populate`'s
`op_prev` operands only **propositionally** (via `hpvb`/`hpvc`), NOT definitionally. So `Eq.trans`'s inferred
composite RHS `(nativeValue f).eval env [i]` is left to `isDefEq` against the goal's `(toElements (populate
op_prev …))[i]`, and unfolding `nativeValue.eval = toElements (f env)` then trying `toElements (map eval …) ≡
toElements (op_prev)` exhausts the 32M budget (they're not defeq).

**Fix direction (correct in principle, but simp won't apply it):** reduce `h_env_cols`'s RHS to the plain
`toElements (populate op_prev …)[i]` form BEFORE the `Eq.trans`, so the composite RHS matches the goal RHS
**syntactically** (cheap). `WitgenIR.nativeValue compute := .native (fun env ↦ toElements (compute env))`
(Clean `WitnessIR.lean:301`) and `WitgenIR.eval_native_apply : (native f).eval env = f env := rfl`
(`:275`, `@[circuit_norm]`). So conceptually `simp only [WitgenIR.nativeValue, WitgenIR.eval_native_apply,
hpvb, hpvc] at hc` should give `hc : env.get(i₀+3+i) = (toElements (populate op_b_prev op_c_prev opcode))[i]`.

**What was tried (3 deterministic builds, ~20 min each) — ALL failed to transform `hc`:**
1. `rw [Witgen.WitgenIR.eval_nativeValue] at hc` → "did not find pattern `(nativeValue ?compute).eval ?env`"
   (HO `[ProvableType value]` matching fails).
2. `simp only [Witgen.WitgenIR.eval_nativeValue, hpvb, hpvc] at hc` → all three flagged **unused** (no fire).
3. `simp only [Witgen.WitgenIR.nativeValue, Witgen.WitgenIR.eval_native_apply, hpvb, hpvc] at hc` → only
   `nativeValue` fires; `eval_native_apply`/`hpvb`/`hpvc` flagged **unused**; the `Eq.trans` still times out.
   (Hypothesis: after `nativeValue` unfolds, the `(fun env ↦ toElements …) env` is not beta-reduced by
   `simp only` in a way that lets `eval_native_apply`/`hpvb` reach inside — the operands stay shielded.)

**Why I couldn't iterate further:** these proofs are so heavy that `lean_multi_attempt`/`lean_diagnostic_
messages` time out at the 300s LSP wall-clock (the file's *baseline* re-elaboration alone exceeds it), and a
single-file `lake build` is ~20 min with **no intermediate-goal visibility**. So each candidate is a ~20-min
blind shot. This is not tractable to grind blind.

**Leads for the next session (needs interactive inspection on a fast box, or a Clean-side change):**
- Try `dsimp only [Witgen.WitgenIR.nativeValue, Witgen.WitgenIR.eval] at hc` (definitional unfold incl. the
  `WitgenIR.eval` match arm on `.native`) + `beta_reduce`/`simp only [] at hc` to force the beta, THEN
  `rw [hpvb, hpvc] at hc`. The blocker is getting the beta + operand-fold to land inside the closure.
- Or `conv at hc => rw [show (nativeValue f).eval env = toElements (f env) from rfl]` then fold.
- Or bypass `h_env_cols`'s IR form entirely: derive the per-cell equation from the witness hint in the
  `toElements`-of-`populate` form directly (may need a new Clean-side `getElem_eval` lemma matching the 4.30
  `nativeValue` witness shape — cf. `WitgenIR.getElem_eval_ir`/`evalStructLiteralSimproc` in `WitnessIR.lean`).
- Or (cleanest if upstreamable): a Clean fix making `combinedSize'`/`toElements (populate …)` reduce
  structurally again (the 4.28 behavior), which would fix all 6 proofs with zero SP1-side churn.
- DivRem `Tail.lean` is the same root cause surfacing in *soundness*: `comp_limb_isU16 … e54 …` expects the
  unreduced `{a:=…, cols:={msb:=…}}` nativeValue struct where `e54` is the reduced `env.get·65535` — same
  `nativeValue`-vs-reduced mismatch; the same reduction fix should unblock it.

**Interim options for the branch** (user decision): (a) land the migration with these 6 completeness proofs
carrying a temporary `sorry` (clearly tagged, tracked here) so the rest is usable/CI-green-modulo-known-debt;
(b) hold the branch red pending the reduction fix; (c) escalate the `combinedSize'` reduction regression to
Clean. Everything else (soundness, bridges, the whole Sail layer) is genuinely green and axiom-clean.

### BREAKTHROUGH (2026-07-11): the completeness blowup is SOLVED — the type-ascription defeq pattern

The fix that killed the 32M-heartbeat blowup in BitwiseChip completeness (LSP now returns; only tractable
residuals left, all fixed): **ascribe `h_env_cols`'s IR-native RHS into the plain `toElements (populate …)`
form via a definitional `have`, then fold the prev-value operands.** The `have hc : <explicit toElements
type> := h_env_cols ⟨i,hi⟩` makes Lean check `h_env_cols` against the target type by *definitional* equality,
which takes the CHEAP path (`(nativeValue f).eval env = toElements (f env)` is `WitgenIR.eval` on the
`.native` constructor — structural), instead of the expensive eager `Eq.trans` isDefEq that tried to bridge
the *propositional* `map eval ≡ op_prev` gap and burned all heartbeats.

**Pattern (replace the old `refine Eq.trans ?_ ((getElem_toElements_eval_varFromOffset …).trans (h_env_cols
⟨i,hi⟩)); simp [circuit_norm]`):**
```lean
refine (ProvableType.ext_iff _ _).mpr (fun i hi => ?_)
have hc : env.toEnvironment.get (OFF + i)
    = (toElements (<OP>.populate <Vector.map (Expression.eval env.toEnvironment) op_b_var>
        <…op_c_var…> <opcode-expr>))[i]'hi := h_env_cols ⟨i, hi⟩
rw [hpvb, hpvc] at hc          -- fold map-eval operands → the actual prev-value words
refine Eq.trans ?_ ((getElem_toElements_eval_varFromOffset env.toEnvironment OFF i hi).trans hc)
simp [circuit_norm]
```
- Read the exact `<OP>.populate …` term + the `OFF` + the fold-hyps (`hpvb`/`hpvc`/analogues) straight off the
  LSP goal for `h_env_cols` in each file (LSP DOES return the goal on these files, just slowly ~240s — the
  timeout error still carries the goal state).
- The **result-bytes bullet** (`key : ∀ k, env.get … = (…).result[k]`) needs the same ascription with index
  `[8 + (k:ℕ)]'(by have : size <OpCols> = 16 := rfl; have := k.isLt; omega)`, then `exact
  toElements_result_byte _ k`.
- `DivRemChip/Soundness/Tail.lean` (the `comp_limb_isU16 … e54 …` type-mismatches at 95/97/111/113) is the
  same nativeValue-vs-reduced gap in *soundness*: ascribe the relevant `env.get`/witness hyp into the
  reduced `env.get·65535` form (or feed `comp_limb_isU16` the nativeValue-form arg) via the same `have :
  <explicit> := …` defeq trick.

**Remaining to propagate (each ~240s LSP inspect + apply, then a build to confirm):** LtChip / BranchChip /
MulChip / DivRemChip *completeness* + DivRem Tail. LSP works on each once the ascription lands (the blowup was
what broke it). This is now tractable, not research-blocked.

### PATTERN FULLY PROVEN on BitwiseChip (LSP-confirmed closers) — two refinements to the pattern above:
- The cell-equality closer is **`simp only [circuit_norm]; rfl`** (NOT `simp [circuit_norm]`): the simp
  normalises `eval (varFromOffset)` → the witnessed struct leaving a reflexive goal that simp alone won't
  auto-`rfl` in 4.30, so the explicit `rfl` (or `congr 1`) is required.
- Drop the now-redundant `hpvb, hpvc` from the earlier `simp only [Inputs.op_b_val, Inputs.op_c_val,
  vec4_eval, hpvb, hpvc] at h_env_cols` (they no longer fire there — the fold now happens in `hc`).
Remaining to propagate (proven pattern, LSP works once applied): LtChip / BranchChip / MulChip / DivRemChip
completeness (+ Driver) + DivRem Tail.

## 2026-07-11 (late) — core SOLVED + widely applied; ~11 heaviest files hit a VERIFICATION wall

**Green & verified this session (on top of everything above):** BitwiseChip/LtChip/BranchChip **completeness**
(the proven type-ascription pattern), LtChip/BitwiseChip **Bridge** (readReg-unfold template), ShiftRight
Bridge. The completeness `combinedSize'`/nativeValue blowup is genuinely SOLVED — BitwiseChip/Formal builds
0/0 in **5.5s** (was a 32M-heartbeat timeout).

**Remaining (proven pattern applies; blocked only by verification speed + LSP loss):**
- `MulChip/Formal.lean` — completeness cell fix applied (`dsimp only [Witgen.WitgenIR.nativeValue,
  eval_native_apply] at hc; simp only [hob, hoc] at hc; …; simp only [circuit_norm]; rfl`) BUT the single-file
  `lake build` exceeds 20 min even on an idle CPU → **UNVERIFIED**; the unbounded-ish `dsimp` may be reducing
  `toElements` internals. Safer: the BitwiseChip **type-ascription** (`have hc : <explicit toElements type> :=
  h_env_cols ⟨i,hi⟩`) — but MulChip's operands are the `#v[Expression.eval env.toEnvironment <op_b_var>[0], …]`
  form (like DivRem Driver), and the exact `<op_b_var>` name needs an LSP goal read (currently unavailable).
- `DivRemChip/Completeness/Driver.lean` — agent applied the ascription with an explicit `#v[eval[0],…]` form
  that doesn't defeq-match `h_env_mullo`/`h_env_mulhi`'s `Vector.map eval` closure → still times out. Same fix
  needed with the exactly-matching operand form (or the bounded `dsimp`).
- `DivRemChip/Soundness/{Div,Rem}.lean` — partially edited by agents (LSP died mid-run); {Divu,Divw,Divuw,Remu,
  Remw,Remuw,Reader}.lean untouched. All have the `rw [show env.get X = env.get Y from …, h]` failing on
  `Expression.eval env (match ProvableStruct…)` (nativeValue-form `h`) → same bridge fix; `Reader.lean:50` is a
  separate `maximum recursion depth` (needs `set_option maxRecDepth`).

**Root blocker now = TOOLING, not proof:** these ~11 files are the heaviest in the project; a single-file
`lake build` is 20–47 min, the `lean-lsp` MCP became unstable then disconnected (its churning workers also
caused CPU contention inflating build times), and `lean_multi_attempt`/`lean_diagnostic_messages` time out at
the 300s wall-clock on these files (their *baseline* elaboration exceeds it). So each fix attempt is a ~20-min
blind shot with no intermediate-goal visibility.

**Recommended next step:** an overnight / fast-box full `lake build SP1Clean`, then apply the proven
type-ascription pattern (reading each file's exact operands from a *working* LSP goal) to the ~11 files one
at a time. The pattern is validated and documented above; this is mechanical-with-care, not research.

## 2026-07-11 (session: 4.30 finish to green checkpoint) — MulChip+DivRem bridges fixed; DivRem soundness stop-deferred

Drove the 4.30 migration to a **committed green checkpoint** (soundness green *modulo* a disclosed
DivRem-soundness deferral; completeness deferred). Net result: `lake build SP1Clean` = 0 errors, 0 warnings.

**Fixed (genuinely green):**
- **`MulChip/Bridge.lean`** (5 Mul-family Sail lemmas) + **`DivRemChip/Bridge.lean`** (8 div/rem lemmas):
  the sail@`793034f3` monad-shape drift. The 4.28 one-shot `simp [..., LeanRV64D.readReg, LeanRV64D.writeReg,
  ...]` unfolds `readReg`→`PreSail.readReg` *before* `run_readReg` can fire, so the PC read never reduces.
  Fix = the **LtChip staged template**: `simp only [spec_*, sp1_*]` → `have hpcrun : (readReg PC).run s = .ok
  pc s := by rw [run_readReg, h_pc]` → `rw [run_bind_of_run s _ pc hpcrun]` → `simp [..., run_writeReg_bind,
  get_reg?_insert_nextPC, h_rs1, h_rs2, h_op]`; the DivRem side then needs a trailing **`rfl`** (simp reduces
  both sides to the identical `ite … writeReg …` but doesn't apply the final defeq-`ite` rfl). MulChip/Bridge
  also needed `import SP1Clean.Proofs.Sail.Advance` (for `run_bind_of_run`); DivRem already had it.
- `MemoryConsistency.lean:473` `List.Sublist.cons₂` → `cons_cons` (4.30 deprecation).

**Deferred with `stop` (disclosed, MUST RESTORE before consolidation PR):**
- **DivRem *soundness*** — the 9 files `Soundness/{Reader,Div,Divu,Divw,Divuw,Rem,Remu,Remw,Remuw}.lean`
  now **hit a `whnf` deterministic-timeout at 100M heartbeats** (Reader alone: 48min → timeout, uncontended).
  This is a genuine **4.30 regression of the same class** as the completeness `nativeValue`/`combinedSize'`
  blowup — the files *do not elaborate at all* on 4.30 (timeout = build failure). Bisection isolated it:
  `spec_proof_start` is cheap (11s); the cost is the post-`spec_proof_start` `obtain h_holds` (63) /
  `simp [ownAsserts]` / `obtain h_own` (121) destructure. **Obtain-chunking** (the compile_bottlenecks
  "split the big obtain" fix) was applied (63→2×32, 121→3×41 blocks; all names preserved) and *helps
  structurally but does NOT clear the whnf wall* — so per the user's "optimize-first-else-stop-stub" steer,
  all 9 are `stop`-stubbed (bodies + the split preserved). Restore via the **type-ascription pattern**
  (this doc, 2026-07-11 completeness breakthrough) applied to soundness, or the `DivRemOperation` structural
  extract (compile_bottlenecks "paths forward"). Each stub builds in ~4s.
- **DivRem `Completeness/Driver.lean`** (`stop`; timed out ~line 505) and **`MulChip/Formal.lean`
  completeness** (`sorry`) — the honest-prover direction, unchanged deferral.

**Note (build hygiene / gotchas learned):** the `-j` flag is not accepted by this lake; a lake build that
errors early **stops launching jobs** so downstream heavy files' errors stay hidden (the MulChip/Bridge error
masked the DivRem bridge + soundness); and orphaned un-`--worker` `lean` builds survive `pkill -f "lean
--worker"` and thrash CPU for 20+ min (kill by the module path). `stop` is Lean-core, closes via `sorryAx`,
and **discards the following tactic block unelaborated** — ideal non-destructive deferral (see the
`build-timeout-smell-test` memory).

**Docs updated this session:** `goal-overview.md` §0/§2 rewritten to the **deps-aware audit standard** (explicit
global Lean config verbatim; the exact platform-config constants as the auditable Sail seam incl. the new
**PMM** `mseccfg[33:32]=0` assumption; `SailStep`/`SailChain` framed as local notions over `try_step`);
`lean-sail-notes.md` PMM disclosure added.
