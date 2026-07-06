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

/-! ## The execute-stage bridge (per family) -/

/-- **The RTYPE execute stage reaches `Retire_Success`.** `execute (.RTYPE …)` on a state whose `rs1`/`rs2`
register reads are known runs to `Retire_Success` and writes only `rd` (via `wX_bits`, x0-uniform). This is
the `hexec` the ladder needs, for the whole R-type family (Add/Sub/Bitwise/Lt/Shift/… — one `op`). The
committed write value is `execute_RTYPE_pure op_b op_c op`; a chip's semantic `Spec` ties that to `rdWrite`. -/
theorem rtype_execute_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (op : rop)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b)
    (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.RTYPE (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_RTYPE_pure op_b op_c op)))}) := by
  simp only [execute, execute_RTYPE_eq_execute_RTYPE', execute_RTYPE']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-! ## The `StraightLineReady` producer (the `toStraightLineReady` body) -/

/-- **`StraightLineReady` on the post-`minstret_increment`-write state.** From the quiescent machine-mode
config facts on `s` — initialized, machine privilege, active hart, `mstatus.MIE = 0`, `mideleg = 0`, no
landing-pad expectation, valid memory config, PC 4-aligned, and the ROM word present in memory — the
`try_step` post-write state `{s with regs.insert minstret_increment b}` is `StraightLineReady` for the
fetched word `data₃ ++ … ++ data₀`. Pure assembly: the two deep fields come from the `_writeMinstret`
frame lemmas (`run_dispatchInterrupt_machine_none_writeMinstret` / `run_fetch_eq_F_Base_writeMinstret`);
the three register-read fields frame through the disjoint `minstret_increment` insert. This is the body of
the eventual `SailConfigured.toStraightLineReady` (its hypotheses are the strengthened config's fields). -/
theorem straightLineReady_writeMinstret
    (s : SailState) (b : Bool) (pc : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (hinit : s.isInitialized)
    (hconfig : SailMem.SailState.isValidMemConfig s hinit)
    (hmie : _get_Mstatus_MIE (s.regs.get Register.mstatus (hinit _)) = 0#1)
    (hmideleg : s.regs.get Register.mideleg (hinit _) = zeros)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_active : s.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (h_elp : s.regs.get? Register.elp
      ≠ some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED))
    (h_pc : s.regs.get Register.PC (hinit _) = pc)
    (h_access0 : BitVec.ofBool pc[0] = 0#1) (h_access1 : BitVec.ofBool pc[1] = 0#1)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr pc) 4 = true)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (pc + 0) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_align : Int.tmod (↑(zero_extend (BitVec.addInt (pc + 0) 0) : BitVec 64).toNat) 4 = 0)
    (h_not_rvc : isRVC (Sail.BitVec.extractLsb (data₃ ++ data₂ ++ data₁ ++ data₀) 15 0) = false)
    (hmem₀ : s.mem[(pc + 0).toNat]? = some data₀) (hmem₁ : s.mem[(pc + 0).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(pc + 0).toNat + 2]? = some data₂) (hmem₃ : s.mem[(pc + 0).toNat + 3]? = some data₃) :
    StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) where
  init := SailState.isInitialized_insert s hinit _ _
  priv := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact h_priv
  active := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact h_active
  no_interrupt := run_dispatchInterrupt_machine_none_writeMinstret s hinit b hmie hmideleg
  fetched := run_fetch_eq_F_Base_writeMinstret pc data₀ data₁ data₂ data₃ s hinit b hconfig h_pc
    h_access0 h_access1 h_aligned h_in_range h_align h_not_rvc hmem₀ hmem₁ hmem₂ hmem₃
  no_landing_pad := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact h_elp

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

/-- **The minstret-bump tail is a register-file frame**: run on any initialized state `t`, the
`minstret_increment`-gated `minstret ← minstret+1` bump yields `.ok false t'` with `t'` agreeing with `t`
on `PC` and on the whole `BitVec 5` register file — the bump touches only the `minstret` CSR. -/
theorem minstret_tail_frame (t : SailState) (hinit : t.isInitialized) :
    ∃ t' : SailState,
      (do
        let mi ← Sail.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← Sail.readReg Register.minstret
            Sail.writeReg Register.minstret (BitVec.addInt m 1)
            (pure false : SailM Bool)
          else (pure false : SailM Bool)).run t = .ok false t'
      ∧ t'.regs.get? Register.PC = t.regs.get? Register.PC
      ∧ (∀ idx : BitVec 5, t'.get_reg? idx = t.get_reg? idx) := by
  rw [run_bind_of_run t _ _ (Sail.run_readReg_of_isInitialized t Register.minstret_increment hinit)]
  split
  · rw [run_bind_of_run t _ _ (Sail.run_readReg_of_isInitialized t Register.minstret hinit),
      run_writeReg_bind]
    refine ⟨_, rfl, ?_, fun idx => ?_⟩
    · rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
    · exact SailState.get_reg?_insert_of_ne (by unfold reg_idx_to_Register; split <;> decide)
  · exact ⟨_, rfl, rfl, fun _ => rfl⟩

/-- **The `tick_pc` + minstret tail's effect** on the observables: it commits `PC ← nextPC` and leaves every
`BitVec 5` register file entry fixed (the minstret bump touches only the `minstret` CSR, `tick_pc` only
`PC` — both outside the register file). -/
theorem tail_effect (s'' : SailState) (hinit'' : s''.isInitialized) :
    ∃ s_final : SailState,
      (do
        tick_pc ()
        let mi ← Sail.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← Sail.readReg Register.minstret
            Sail.writeReg Register.minstret (BitVec.addInt m 1)
            (pure false : SailM Bool)
          else (pure false : SailM Bool)).run s'' = .ok false s_final
      ∧ s_final.regs.get? Register.PC = s''.regs.get? Register.nextPC
      ∧ (∀ idx : BitVec 5, s_final.get_reg? idx = s''.get_reg? idx) := by
  simp only [tick_pc_eq, bind_assoc]
  rw [run_bind_of_run s'' _ _ (Sail.run_readReg_of_isInitialized s'' Register.nextPC hinit''),
    run_writeReg_bind]
  obtain ⟨t', hrun, hPC', hxreg'⟩ := minstret_tail_frame
    {s'' with regs := s''.regs.insert Register.PC (s''.regs.get Register.nextPC (hinit'' _))}
    (SailState.isInitialized_insert s'' hinit'' _ _)
  refine ⟨t', hrun, ?_, fun idx => ?_⟩
  · rw [hPC', Std.ExtDHashMap.get?_insert_self, Std.ExtDHashMap.get?_eq_some_get (hinit'' _)]
  · rw [hxreg' idx]; exact SailState.get_reg?_insert_PC

/-- **The core `SailStep` composition** — joins the landed ladder (`tryStep_reaches`) with the tail's
observable effect (`tail_effect`). Given the ladder inputs on the post-minstret-write state, `try_step`
takes one real step to some `s_final` whose `PC` is the post-execute `nextPC` and whose `BitVec 5`
register file agrees with the post-execute state `s''`. This is the whole `try_step`-side content of a
register-writing chip's `advance`; per-chip work is only characterizing `s''` (via the execute bridge)
and building the ladder inputs from `RefinesAt`/`OperandsBound`. -/
theorem sailStep_of_ladder (s s_a s'' : SailState) (w : BitVec 32) (I : instruction) (b : Bool)
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
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (hinit'' : s''.isInitialized) :
    ∃ s_final : SailState, (try_step 0 false).run s = .ok false s_final
      ∧ s_final.regs.get? Register.PC = s''.regs.get? Register.nextPC
      ∧ (∀ idx : BitVec 5, s_final.get_reg? idx = s''.get_reg? idx) := by
  obtain ⟨s_final, hrun, hPC, hxreg⟩ := tail_effect s'' hinit''
  refine ⟨s_final, ?_, hPC, hxreg⟩
  rw [tryStep_reaches s s_a s'' w I b hb hcp hactive hslr hdec hsa hexec h_active'']
  exact hrun

end SP1Clean.Advance
