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
- **Current tree state: RED** (SailMemory in-progress). Recoverable to 4.28-green by reverting `lakefile.toml` +
  `lean-toolchain` (+ `git checkout` the Sail-layer edits if ever switching to A). Wave A + Batch 1 stay.
- AFTER SP1Clean green: migration done (modulo known `sp1_witness_decode` sorry) → resume consolidation on
  4.30 (F5/X1/spine); K1–K3; refresh AGENTS.md/lean-sail-notes off the stale 4.28 pins.
