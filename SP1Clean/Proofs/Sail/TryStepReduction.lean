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

/-! ## Remaining ladder (the composition + the two substantive stages)

Stages 0-1 above are the trivial/`readReg`-then-`pure` pieces. The rest of `tryStep_eq_of_ready`
(the ADD-family `try_step 0 false → spec_add`-shaped reduction) still needs:

- **Stage 2 — `dispatchInterrupt_none`** (`SysControl.lean:593`): deeper than a bare `mip &&& mie` check
  — it calls `getPendingSet` (an `assert (currentlyEnabled Ext_S || mideleg = 0)` + `read_mip
  IncludePlatformInterrupts` + `pending_{m,s} := mip_bits &&& mie &&& (~)mideleg` + the `mstatus`
  MIE/SIE bits), then `findPendingInterrupt`. `= none` needs the state fact that `read_mip` (register mip
  PLUS platform interrupt sources MTIP/MSIP/MEIP) masked by `mie` is `0` — i.e. a genuine
  no-pending-interrupt precondition, discharged by reducing `read_mip`/`getPendingSet` under an initial
  quiescent-interrupt state. Bounded but a real sub-lemma (readReg toolkit + the `read_mip` reduction).
- **Stage 3 — `fetch_eq_F_Base`** (`Fetch.lean:227`, THE wall): with `get_config_rvfi = false` (done),
  `ext_fetch_check_pc = none`, PC 4-aligned (bit0 = bit1 = 0), `Ext_Ziccif`/`Ext_Zca` enabled, `fetch`
  reduces to `fetch_bytes PC PC 4` → `translateAddr` (identity under Bare/machine-mode) + `mem_read
  (InstructionFetch …)` → `F_Base w` where `w` is the `RomLoaded` word. Reuse `Model/SailMemory.lean`'s
  `run_mem_read_*`/`run_vmem_read_of_width_4'` (built for the Load path — adapt to `InstructionFetch`).
- **Stage 4 — decode-thread**: `ext_decode w = instruction` supplied by `decodedInROM.decodes` (NOT
  computed) — the `run_bind` congruence, not the SailDecode concrete walk.
- **Stage 5 — execute wrapper + result-dispatch + `tick_pc`**: `writeReg nextPC (PC+4); execute I`
  (`execute_RTYPE_eq_execute_RTYPE'` + `run_wX_bits`/`run_rX_bits`) → `Step_Execute (Retire_Success (),
  instbits)` → the `try_step` result-dispatch (the `Retire_Success` case is an `assert (hart_is_active
  …)`, true here) → `tick_pc` (`tick_pc_eq`) commits `PC ← nextPC`; the minstret/rvfi bookkeeping is
  dead (`get_config_rvfi = false`) or unobservable (`minstret_increment`).

`StraightLineReady s` bundles the state facts: `hart_state = HART_ACTIVE ()`, `mip &&& mie = 0`,
`elp ≠ LP_EXPECTED`, `ext_fetch_check_pc = none`, PC 4-aligned, `Ext_Ziccif`/`Ext_Zca` — threaded from
`RefinesAt` + `SailConfigured` (which is strengthened to entail them). The composition
`tryStep_eq_of_ready : StraightLineReady s → RomLoaded prog s → fetchWord (PC) = some w → decodes w I →
(try_step 0 false).run s = (writeReg nextPC (PC+4) >>= fun _ => execute I >>= fun _ => tick_pc ()).run s`
is the Phase-3a deliverable that Phase-4 `advance` composes with `correct_<op>_native`. -/

end SP1Clean.TryStepReduction
