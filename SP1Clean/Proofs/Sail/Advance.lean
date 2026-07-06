import SP1Clean.Proofs.Sail.TryStepReduction
import SP1Clean.Soundness.ValueBound

/-! # Phase 4 — the uniform per-chip `advance` (Sail-step obligation)

The generic composition wiring the Phase-3 `try_step` reduction ladder (`Proofs/Sail/TryStepReduction.lean`)
into each chip's Sail-step obligation (`TargetObligations.lift`, `Soundness/TargetVm.lean`):
`RefinesAt → OperandsBound → ∃ s', SailStep s s' ∧ RowEffect prog row s s'`.

The load-bearing goal is **uniformity**: one `sp1Effect` (a function of the committed `RowView`), one
generic `advance_of_regWrite` proof, and thin per-chip adapters — replacing the 25 bespoke per-chip
`ChipKind.sailEquiv` predicates so the audit surface is a single statement. -/

namespace SP1Clean.Advance

open SP1Clean Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace
open SP1Clean.TryStepReduction

set_option maxHeartbeats 4000000

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The row's committed next-pc as a 64-bit value — data-dependent (straight-line `pc+4` or the control-flow
target), read uniformly off the RowView's `next_pc` limbs via `sndPcOf (stateAccess v)`. -/
def sndPcBV (v : Trace.RowView (ZMod p)) : BitVec 64 := sndPcOf (stateAccess v)

/-- The row's `rd` register index, inverting the committed `op_a = (rd.toNat : ZMod p)` (canonical for a
real row where `rd.toNat < 32 < p`). -/
def rdOf (v : Trace.RowView (ZMod p)) : regidx := .Regidx (BitVec.ofNat 5 v.adapter.op_a.val)

/-- **The single uniform SP1 chip effect** (a function of the committed `RowView`): commit the next-pc, then
write `rd = op_a` with the committed `rdWrite`. Every register-writing family's `sp1_<op>` equals
`sp1Effect (view inp cols)` (x0-destination is a definitional no-op via `wX_bits x0 = pure ()`). -/
def sp1Effect (v : Trace.RowView (ZMod p)) : SailM Unit := do
  set_next_pc (sndPcBV v)
  wX_bits (rdOf v) (Word.toBitVec64 v.rdWrite)

/-- The control-flow effect (branches): commit the next-pc only, no register write. -/
def sp1Effect_ctrl (v : Trace.RowView (ZMod p)) : SailM Unit := set_next_pc (sndPcBV v)

/-! ## The generic composition -/

/-- **`run_hart_active` reaches the `Retire_Success` step**, given the execute stage lands there: from the
Phase-3 ladder (`run_hart_active_eq_of_ready`) + a `hstage` fact that `writeReg nextPC (PC+4); execute I`
runs to `Retire_Success` at `s''`, `run_hart_active` yields `Step_Execute (Retire_Success, …)` at `s''`.
The `ExecuteAs` redirect is dead (`execute I` returned `Retire_Success`, not `ExecuteAs`). -/
theorem run_hart_active_reaches (s' s_a s'' : SailState) (w : BitVec 32) (I : instruction) (step_no : Nat)
    (hslr : StraightLineReady s' w)
    (hdec : (ext_decode w).run s' = .ok I s')
    (hsa : (Sail.writeReg Register.nextPC
        (BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4)).run s' = .ok () s_a)
    (hexec : (execute I).run s_a = .ok (ExecutionResult.Retire_Success ()) s'') :
    (run_hart_active step_no).run s'
      = .ok (Step.Step_Execute (ExecutionResult.Retire_Success (), zero_extend (m := 32) w)) s'' := by
  rw [run_hart_active_eq_of_ready s' w I step_no hslr hdec]
  rw [run_bind_of_run s' _ _ (Sail.run_readReg_of_isInitialized s' Register.PC hslr.init),
    run_bind_of_run' s' s_a _ () hsa,
    run_bind_of_run' s_a s'' (execute I) (ExecutionResult.Retire_Success ()) hexec]
  rfl

/-- **`try_step` reaches the row's execute effect** — the full outer-frame composition. On the
post-minstret-write state `s' = {s with regs.insert minstret_increment b}` (with `StraightLineReady s'`),
`try_step 0 false` reduces to its `tick_pc` + minstret tail on `s''` (= the post-`execute I` state), via
`run_hart_active_reaches` (into `h_ha`) + `tryStep_eq_of_hart_active`. -/
theorem tryStep_reaches (s s_a s'' : SailState) (w : BitVec 32) (I : instruction) (b : Bool)
    (hb : (should_inc_minstret Privilege.Machine).run s = .ok b s)
    (hcp : (Sail.readReg Register.cur_privilege).run s = .ok Privilege.Machine s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b}) w)
    (hdec : (ext_decode w).run ({s with regs := s.regs.insert Register.minstret_increment b})
      = .ok I ({s with regs := s.regs.insert Register.minstret_increment b}))
    (hsa : (Sail.writeReg Register.nextPC (BitVec.addInt
        ((s.regs.insert Register.minstret_increment b).get Register.PC (hslr.init Register.PC)) 4)).run
        ({s with regs := s.regs.insert Register.minstret_increment b}) = .ok () s_a)
    (hexec : (execute I).run s_a = .ok (ExecutionResult.Retire_Success ()) s'')
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())) :
    (try_step 0 false).run s
      = (do
          tick_pc ()
          let mi ← Sail.readReg Register.minstret_increment
          if (true && mi) = true then do
              let m ← Sail.readReg Register.minstret
              Sail.writeReg Register.minstret (BitVec.addInt m 1)
              (pure false : SailM Bool)
            else (pure false : SailM Bool)).run s'' :=
  tryStep_eq_of_hart_active s 0 b (zero_extend (m := 32) w) s'' hactive hb hcp
    (run_hart_active_reaches _ s_a s'' w I 0 hslr hdec hsa hexec) h_active''

end SP1Clean.Advance
