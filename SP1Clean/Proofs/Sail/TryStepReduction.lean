import SP1Clean.Model.SailWrap
import SP1Clean.Model.Semantics.GuestProgram

/-! # Phase 3 — the `try_step` reduction (the W7 `lift` seam)

Reduces the official Sail `try_step 0 false` step function, over a straight-line-ready machine-mode state,
to the execute-stage dispatch — so a chip's `advance` obligation (`∃ s', SailStep s s' ∧ RowEffect …`,
`Soundness/TargetVm.lean`) factors as `tryStepReduction ∘ opcode-inversion ∘ correct_<op>_native`.

`try_step` (`LeanRV64D/…/Step.lean:400`) is a large `SailM` body: pre-hook → `writeReg minstret_increment`
→ `readReg hart_state` dispatch → `run_hart_active` (`:315`: `dispatchInterrupt` → `fetch` → `ext_decode`
→ `execute`) → result-dispatch → `tick_pc` + minstret/rvfi bookkeeping. The reduction reuses the
state-tracking `.run s` toolkit already proven in `Model/SailWrap.lean` (`run_readReg_bind_of_isInitialized`,
`run_writeReg_bind`, `run_wX_bits`/`run_rX_bits`, `run_dite`, `tick_pc_eq`, `execute_RTYPE_eq_…`,
`jump_to_of_mod4_eq_zero`) and the memory-read reductions in `Model/SailMemory.lean`, plus the
concrete-decode walk technique in `Model/SailDecode.lean`.

This file is built bottom-up, one verified stage lemma at a time. -/

namespace SP1Clean.TryStepReduction

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean

set_option maxHeartbeats 4000000
-- The `SailME`/`ExceptT`/`EStateM` monad-stack unfold `simp only` sets use situational subsets per peel
-- (cf. `Model/SailWrap.lean`), so different lemmas leave different args unused.
set_option linter.unusedSimpArgs false

/-! ## Stage 0 — the pure config / hook flags (constants in the Sail model) -/

/-- The instruction-print config flag is compile-time `false` (`Prelude.lean:219`), so the fetch/step
print branches are dead. -/
@[simp] theorem get_config_print_instr_eq : get_config_print_instr () = false := rfl

/-- The RVFI config flag is compile-time `false` (`Prelude.lean:237`), so `fetch` takes its non-RVFI
branch and the step's `rvfi_pc_data` write is dead. -/
@[simp] theorem get_config_rvfi_eq : get_config_rvfi () = false := rfl

/-- The fetch hook is the identity (`StepExt.lean:207`). -/
@[simp] theorem ext_fetch_hook_eq (f : FetchResult) : ext_fetch_hook f = f := rfl

/-- The pre-step hook is a no-op (`StepExt.lean:210`). -/
@[simp] theorem ext_pre_step_hook_eq : ext_pre_step_hook () = () := rfl

/-- `hart_is_active` on the active hart is `true` (`StepCommon.lean:207`). -/
@[simp] theorem hart_is_active_active : hart_is_active (HartState.HART_ACTIVE ()) = true := rfl

/-! ## Stage 1 — the `readReg`-then-`pure` aux stages -/

/-- `is_landing_pad_expected () = pure (readReg elp == LP_EXPECTED_bits)` (`ZicfilpRegs.lean:252`) reduces,
under `isInitialized`, to the boolean comparison of the state's `elp` against the landing-pad-expected
encoding — no state change. The straight-line path wants this `false` (`elp = NO_LP_EXPECTED`). -/
theorem run_is_landing_pad_expected (s : SailState) (hs : SailState.isInitialized s) :
    (is_landing_pad_expected ()).run s
      = .ok (s.regs.get Register.elp (hs _)
          == landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED) s := by
  unfold is_landing_pad_expected
  rw [Sail.run_readReg_bind_of_isInitialized s Register.elp hs]
  simp only [EStateM.run_pure]

/-- `should_inc_minstret priv` (`Platform.lean:537`) reads `mcountinhibit` + `minstretcfg` and returns a
boolean, no state change. Whatever the boolean is, `try_step`'s `writeReg minstret_increment (← should_…)`
only touches the (unobservable) `minstret_increment` register — the frame fact the reduction needs. -/
theorem run_should_inc_minstret (s : SailState) (hs : SailState.isInitialized s) (priv : Privilege) :
    (should_inc_minstret priv).run s
      = .ok (((_get_Counterin_IR (s.regs.get Register.mcountinhibit (hs _))) == 0#1)
          && ((counter_priv_filter_bit (s.regs.get Register.minstretcfg (hs _)) priv) == 0#1)) s := by
  unfold should_inc_minstret
  rw [Sail.run_readReg_bind_of_isInitialized s Register.mcountinhibit hs,
    Sail.run_readReg_bind_of_isInitialized s Register.minstretcfg hs]
  simp only [EStateM.run_pure]

/-! ## Stage 2 — the straight-line readiness predicate

The state facts a real ROM-loaded, quiescent, machine-mode SP1 execution state carries, bundling the two
*deep* Sail-side facts (interrupt-quiescence and ROM-fetch) as fields so the `run_hart_active`/`try_step`
composition can thread them; each is discharged separately from the Sail model (Stages 2'/3' — the
`dispatchInterrupt`/`fetch` reductions, which spiral through `getPendingSet`/`read_mip`/`currentlyEnabled`
and `fetch_bytes`/`translateAddr`/`mem_read`). `w` is the fetched instruction word. -/
structure StraightLineReady (s : SailState) (w : BitVec 32) : Prop where
  /-- CSRs present (the Sail-model reduction residue). -/
  init : s.isInitialized
  /-- Machine mode. -/
  priv : s.regs.get? Register.cur_privilege = some Privilege.Machine
  /-- The hart is active (not waiting). -/
  active : s.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())
  /-- No interrupt is dispatched — the interior of `run_hart_active`'s first stage runs to `none` (Stage
  2'; holds when machine interrupts are disabled, `mstatus.MIE = 0`, since `getPendingSet` short-circuits
  on `mIE`). -/
  no_interrupt : (dispatchInterrupt Privilege.Machine).run s = .ok none s
  /-- The fetch yields the base (32-bit) ROM word `w` (Stage 3'; from `RomLoaded` + PC-aligned + no
  translation fault). -/
  fetched : (fetch ()).run s = .ok (FetchResult.F_Base w) s
  /-- No landing pad is expected (`elp ≠ LP_EXPECTED`), so the CFI trap branch is dead. -/
  no_landing_pad :
    s.regs.get? Register.elp ≠ some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED)

/-! ## Stage 2b — the `SailME`-peeling machinery (reduce `liftM`-prefixed `SailME.run` do-blocks) -/

/-- **The lift-bind law** (the master peel): a `liftM m`-prefixed `SailME.run` do-block runs `m` first
(threading its state change), then continues with `SailME.run ∘ k` on the value — for ANY `SailM` action
`m`, state-preserving or not (so it peels the state-changing `writeReg`/`execute` tail too). -/
theorem run_SailME_liftM_bind {β : Type} (m : SailM β) (k : β → SailME Step Step) :
    SailME.run (liftM m >>= k) = (m >>= fun a => SailME.run (k a) : SailM Step) := by
  funext s
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk, ExceptT.bindCont,
    ExceptT.bind, ExceptT.lift, ExceptT.map, Functor.map, Except.map, MonadLift.monadLift,
    liftM, monadLift, bind, EStateM.bind, EStateM.run, EStateM.map]
  cases m s <;> rfl

/-- Peel a trailing `SailME.run (pure a)` to the `SailM` `pure a` (no throw, no state change). -/
theorem run_SailME_pure {β : Type} (a : β) :
    SailME.run (pure a : SailME β β) = (pure a : SailM β) := rfl

/-- Peel a `liftM (readReg reg)` from the front of a `SailME.run` do-block: under `isInitialized`, it
resolves to the state's register value with no state change. The `SailME`/`ExceptT`/`EStateM` monad-stack
unfold (the `SailWrap.SailME_run_readReg_map_writeReg` recipe). -/
theorem run_SailME_liftM_readReg_bind (s : SailState) (reg : Register)
    (hs : SailState.isInitialized s) (k : RegisterType reg → SailME Step Step) :
    EStateM.run (SailME.run (liftM (Sail.readReg reg) >>= k)) s
      = EStateM.run (SailME.run (k (s.regs.get reg (hs reg)))) s := by
  simp only [SailME.run, PreSail.PreSailME.run, Sail.readReg, PreSail.readReg,
    ExceptT.run, ExceptT.mk, ExceptT.bindCont, ExceptT.bind, ExceptT.lift, ExceptT.map,
    Functor.map, Except.map, MonadLift.monadLift, liftM, monadLift, pure, bind,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.map, EStateM.get,
    getThe, MonadStateOf.get, MonadState.get, get,
    Std.ExtDHashMap.get?_eq_some_get (hs _)]

/-- Peel a `liftM m` from the front of a `SailME.run` do-block for any **state-preserving** `SailM` action
`m` (given `m.run s = .ok a s`): it resolves to its value `a` with no state change. The generic peel that
threads the `StraightLineReady` `dispatchInterrupt`/`fetch` facts. -/
theorem run_SailME_liftM_bind_of_run {β : Type} (s : SailState) (m : SailM β) (a : β)
    (hm : EStateM.run m s = .ok a s) (k : β → SailME Step Step) :
    EStateM.run (SailME.run (liftM m >>= k)) s = EStateM.run (SailME.run (k a)) s := by
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk, ExceptT.bindCont,
    ExceptT.bind, ExceptT.lift, ExceptT.map, Functor.map, Except.map, MonadLift.monadLift,
    liftM, monadLift, bind, EStateM.bind, EStateM.run, EStateM.map]
  rw [show m s = EStateM.Result.ok a s from hm]

/-! ## Stage 3 — `run_hart_active` reduces to the execute stage -/

set_option linter.unusedVariables false in
theorem run_hart_active_eq_of_ready (s : SailState) (w : BitVec 32) (I : instruction) (step_no : Nat)
    (h : StraightLineReady s w) (hdec : (ext_decode w).run s = .ok I s) :
    (run_hart_active step_no).run s
      = (do
          Sail.writeReg Register.nextPC (BitVec.addInt (← Sail.readReg Register.PC) 4)
          let result ← (match (← execute I) with
            | .ExecuteAs other_inst => execute other_inst
            | result => pure result)
          pure (Step.Step_Execute (result, zero_extend (m := 32) w))).run s := by
  have hcp : (Sail.readReg Register.cur_privilege).run s = .ok Privilege.Machine s := by
    rw [Sail.run_readReg, h.priv]
  unfold run_hart_active
  rw [run_SailME_liftM_bind_of_run _ _ _ hcp]
  rw [run_SailME_liftM_bind_of_run _ _ _ h.no_interrupt]
  simp only [pure_bind]
  rw [run_SailME_liftM_bind_of_run _ _ _ h.fetched]
  simp only [ext_fetch_hook_eq]
  rw [run_SailME_liftM_bind_of_run _ _ _ hdec]
  simp only [get_config_print_instr_eq, Bool.false_eq_true, if_false, pure_bind]
  -- the landing-pad guard is false (`elp ≠ LP_EXPECTED`), so the CFI trap arm is dead.
  have hlp : (is_landing_pad_expected ()).run s = .ok false s := by
    rw [run_is_landing_pad_expected s h.init]
    congr 1
    rw [beq_eq_false_iff_ne]
    exact fun heq =>
      h.no_landing_pad (by rw [Std.ExtDHashMap.get?_eq_some_get (h.init _), heq])
  rw [run_SailME_liftM_bind_of_run _ _ _ hlp]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  -- the state-changing execute tail: peel `readReg PC`, `writeReg nextPC`, `execute I` with the general
  -- lift-bind law (threading the state), then strip `EStateM.run` and the three binders with `bind_congr`
  -- so the `ExecuteAs` redirect match's scrutinee `a` becomes free — `cases a` collapses both arms (of the
  -- compiled matcher, without needing to name it), each closing under the lift-bind/pure laws.
  simp only [run_SailME_liftM_bind, run_SailME_pure, bind_assoc, pure_bind]
  refine congrArg (EStateM.run · s) (bind_congr fun _ => bind_congr fun _ => bind_congr fun a => ?_)
  cases a <;> simp only [run_SailME_liftM_bind, run_SailME_pure, pure_bind, bind_assoc]

/-! ## Remaining ladder (the composition + the two substantive stages)

Stage 3 (`run_hart_active_eq_of_ready`, above) is **landed** — the reduction of `run_hart_active` to the
execute stage `writeReg nextPC (PC+4); execute I; Step_Execute (…)`, threading all five
`StraightLineReady` fields (`priv`/`no_interrupt`/`fetched`/`no_landing_pad`/`init`) + `hdec` for
`ext_decode w = I`, is axiom-clean (only the accepted Sail platform trust base). The rest of
`tryStep_eq_of_ready` (the ADD-family `try_step 0 false → spec_add`-shaped reduction) still needs:

- **Stage 4 — the `try_step` wrapper** (`Step.lean:400`): compose Stage 3 with the outer frame —
  `ext_pre_step_hook` (no-op, `@[simp]` above); the `minstret_increment := should_inc_minstret (←
  readReg cur_privilege)` write (an unobservable-frame `writeReg`, mirror the spike's `FrameFact`); the
  `hart_state = HART_ACTIVE ()` dispatch (`h.active`); the result-dispatch (the `Step_Execute
  (Retire_Success (), _)` case is `assert (hart_is_active …)`, true by `hart_is_active_active`); and
  `tick_pc ()` (`tick_pc_eq`) committing `PC ← nextPC`, with the minstret/rvfi bookkeeping dead
  (`get_config_rvfi = false`) or unobservable. Composes Stage 3 — no new deep Sail reduction.
- **Stages 2'/3' — discharge the two deep `StraightLineReady` fields** (currently assumptions, so the
  named-hypothesis fallback holds with no sorry):
  - **`no_interrupt`** (`dispatchInterrupt Machine = none`, `SysControl.lean:593`): deeper than a bare
    `mip &&& mie` check — it calls `getPendingSet` (an `assert (currentlyEnabled Ext_S || mideleg = 0)` +
    `read_mip IncludePlatformInterrupts` + `pending_{m,s} := mip_bits &&& mie &&& (~)mideleg` + the
    `mstatus` MIE/SIE bits), then `findPendingInterrupt`. `= none` needs the state fact that `read_mip`
    (register mip PLUS platform interrupt sources MTIP/MSIP/MEIP) masked by `mie` is `0` — a genuine
    no-pending-interrupt precondition, discharged by reducing `read_mip`/`getPendingSet` under a
    quiescent-interrupt state. Bounded but a real sub-lemma (readReg toolkit + the `read_mip` reduction).
  - **`fetched`** (`fetch () = F_Base w`, `Fetch.lean:227`, THE wall): with `get_config_rvfi = false`
    (done), `ext_fetch_check_pc = none`, PC 4-aligned (bit0 = bit1 = 0), `Ext_Ziccif`/`Ext_Zca` enabled,
    `fetch` reduces to `fetch_bytes PC PC 4` → `translateAddr` (identity under Bare/machine-mode) +
    `mem_read (InstructionFetch …)` → `F_Base w` where `w` is the `RomLoaded` word. Reuse
    `Model/SailMemory.lean`'s `run_mem_read_*`/`run_vmem_read_of_width_4'` (built for the Load path —
    adapt to `InstructionFetch`).

The `hdec : ext_decode w = I` argument is caller-supplied by `decodedInROM.decodes` (NOT computed) — the
per-family (3b) application threads it from `ProgTruth`; the execute stage then composes with the already-
proven `execute_<FAM>` bridges (`correct_<op>_native`).

`StraightLineReady s` bundles the state facts: `hart_state = HART_ACTIVE ()`, `mip &&& mie = 0`,
`elp ≠ LP_EXPECTED`, `ext_fetch_check_pc = none`, PC 4-aligned, `Ext_Ziccif`/`Ext_Zca` — threaded from
`RefinesAt` + `SailConfigured` (which is strengthened to entail them). The composition
`tryStep_eq_of_ready : StraightLineReady s → RomLoaded prog s → fetchWord (PC) = some w → decodes w I →
(try_step 0 false).run s = (writeReg nextPC (PC+4) >>= fun _ => execute I >>= fun _ => tick_pc ()).run s`
is the Phase-3a deliverable that Phase-4 `advance` composes with `correct_<op>_native`. -/

end SP1Clean.TryStepReduction
