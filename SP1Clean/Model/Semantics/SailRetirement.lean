import SP1Clean.Model.Semantics.SailFetch

/-! # Normal retirement and its complete Sail bookkeeping effects

These circuit-independent lemmas compose an actual execute-stage result with official `try_step`.
They preserve initialization and expose PC, GPR, memory, other-register, runtime, and retirement
observations. Instruction-family frame laws supply the execute-stage result separately.
-/

open LeanRV64D.Defs
namespace SP1Clean.Advance

open SP1Clean Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction SP1Clean.SailMem

/-! ## The generic composition -/

/-- **`run_hart_active` reaches the `Retire_Success` step**, given the execute stage lands there: from the
Phase-3 ladder (`run_hart_active_eq_of_ready`) + a `hstage` fact that `writeReg nextPC (PC+4); execute I`
runs to `Retire_Success` at `s''`, `run_hart_active` yields `Step_Execute (Retire_Success, …)` at `s''`.
The `ExecuteAs` redirect is dead (`execute I` returned `Retire_Success`, not `ExecuteAs`). -/
theorem run_hart_active_reaches (s' s_a s'' : SailState) (w : BitVec 32) (I : instruction) (step_no : Nat)
    (hslr : StraightLineReady s' w)
    (hdec : (ext_decode w).run s' = .ok I s')
    (hsa : (LeanRV64D.writeReg Register.nextPC
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
    (hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b}) w)
    (hdec : (ext_decode w).run ({s with regs := s.regs.insert Register.minstret_increment b})
      = .ok I ({s with regs := s.regs.insert Register.minstret_increment b}))
    (hsa : (LeanRV64D.writeReg Register.nextPC (BitVec.addInt
        ((s.regs.insert Register.minstret_increment b).get Register.PC (hslr.init Register.PC)) 4)).run
        ({s with regs := s.regs.insert Register.minstret_increment b}) = .ok () s_a)
    (hexec : (execute I).run s_a = .ok (ExecutionResult.Retire_Success ()) s'')
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())) :
    (try_step 0 false).run s
      = (do
          tick_pc ()
          let mi ← LeanRV64D.readReg Register.minstret_increment
          if (true && mi) = true then do
              let m ← LeanRV64D.readReg Register.minstret
              LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
              (pure false : SailM Bool)
            else (pure false : SailM Bool)).run s'' :=
  tryStep_eq_of_hart_active s 0 b (zero_extend (m := 32) w) s'' hactive hb hcp
    (run_hart_active_reaches _ s_a s'' w I 0 hslr hdec hsa hexec) h_active''

/-- **The minstret-bump tail is a register-file frame**: run on any initialized state `t`, the
`minstret_increment`-gated `minstret ← minstret+1` bump yields `.ok false t'` with `t'` agreeing with `t`
on `PC` and on the whole `BitVec 5` register file — the bump touches only the `minstret` CSR. -/
theorem minstret_tail_effect (t : SailState) (hinit : t.isInitialized) :
    ∃ t' : SailState,
      (do
        let mi ← LeanRV64D.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← LeanRV64D.readReg Register.minstret
            LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
            (pure false : SailM Bool)
          else (pure false : SailM Bool)).run t = .ok false t'
      ∧ t'.regs.get? Register.PC = t.regs.get? Register.PC
      ∧ (∀ idx : BitVec 5, t'.get_reg? idx = t.get_reg? idx)
      ∧ t'.mem = t.mem
      ∧ (∀ R : Register, R ≠ Register.minstret → t'.regs.get? R = t.regs.get? R)
      ∧ t'.isInitialized
      ∧ t'.cycleCount = t.cycleCount ∧ t'.sailOutput = t.sailOutput
      ∧ t'.regs.get? Register.minstret =
        (t.regs.get? Register.minstret).map (fun value =>
          if (true && t.regs.get Register.minstret_increment (hinit _)) = true
          then BitVec.addInt value 1 else value) := by
  rw [run_bind_of_run t _ _ (Sail.run_readReg_of_isInitialized t Register.minstret_increment hinit)]
  split
  · rw [run_bind_of_run t _ _ (Sail.run_readReg_of_isInitialized t Register.minstret hinit),
      run_writeReg_bind]
    refine ⟨_, rfl, ?_, (fun idx => ?_), rfl, (fun R hR => ?_), SailState.isInitialized_insert t hinit _ _, rfl, rfl, ?_⟩
    · rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
    · exact SailState.get_reg?_insert_of_ne (by unfold reg_idx_to_Register; split <;> decide)
    · rw [Std.ExtDHashMap.get?_insert, dif_neg (fun hc => hR (beq_iff_eq.mp hc).symm)]
    · rw [Std.ExtDHashMap.get?_insert_self, Std.ExtDHashMap.get?_eq_some_get (hinit _)]
      simp only [Option.map_some]
  · refine ⟨_, rfl, rfl, fun _ => rfl, rfl, (fun _ _ => rfl), hinit, rfl, rfl, ?_⟩
    rw [Std.ExtDHashMap.get?_eq_some_get (hinit _)]
    simp only [Option.map_some]

/-- The architectural projection of the complete retirement tail. -/
theorem minstret_tail_frame (t : SailState) (hinit : t.isInitialized) :
    ∃ t' : SailState,
      (do
        let mi ← LeanRV64D.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← LeanRV64D.readReg Register.minstret
            LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
            (pure false : SailM Bool)
          else (pure false : SailM Bool)).run t = .ok false t'
      ∧ t'.regs.get? Register.PC = t.regs.get? Register.PC
      ∧ (∀ idx : BitVec 5, t'.get_reg? idx = t.get_reg? idx)
      ∧ t'.mem = t.mem
      ∧ (∀ R : Register, R ≠ Register.minstret → t'.regs.get? R = t.regs.get? R)
      ∧ t'.isInitialized := by
  obtain ⟨next, ran, pc, regs, memory, frame, initialized, _⟩ := minstret_tail_effect t hinit
  exact ⟨next, ran, pc, regs, memory, frame, initialized⟩

/-- **The `tick_pc` + minstret tail's effect** on the observables: it commits `PC ← nextPC` and leaves every
`BitVec 5` register file entry fixed (the minstret bump touches only the `minstret` CSR, `tick_pc` only
`PC` — both outside the register file). -/
theorem tail_bookkeeping (s'' : SailState) (hinit'' : s''.isInitialized) :
    ∃ s_final : SailState,
      (do
        tick_pc ()
        let mi ← LeanRV64D.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← LeanRV64D.readReg Register.minstret
            LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
            (pure false : SailM Bool)
          else (pure false : SailM Bool)).run s'' = .ok false s_final
      ∧ s_final.regs.get? Register.PC = s''.regs.get? Register.nextPC
      ∧ (∀ idx : BitVec 5, s_final.get_reg? idx = s''.get_reg? idx)
      ∧ s_final.mem = s''.mem
      ∧ (∀ R : Register, R ≠ Register.PC → R ≠ Register.minstret →
          s_final.regs.get? R = s''.regs.get? R)
      ∧ s_final.isInitialized
      ∧ s_final.cycleCount = s''.cycleCount ∧ s_final.sailOutput = s''.sailOutput
      ∧ s_final.regs.get? Register.minstret =
        (s''.regs.get? Register.minstret).map (fun value =>
          if (true && s''.regs.get Register.minstret_increment (hinit'' _)) = true
          then BitVec.addInt value 1 else value) := by
  simp only [tick_pc_eq, bind_assoc]
  rw [run_bind_of_run s'' _ _ (Sail.run_readReg_of_isInitialized s'' Register.nextPC hinit''),
    run_writeReg_bind]
  obtain ⟨t', hrun, hPC', hxreg', hmem', hframe', hinit', cycles, output, retired⟩ := minstret_tail_effect
    {s'' with regs := s''.regs.insert Register.PC (s''.regs.get Register.nextPC (hinit'' _))}
    (SailState.isInitialized_insert s'' hinit'' _ _)
  refine ⟨t', hrun, ?_, (fun idx => ?_), hmem', (fun R hRpc hRm => ?_), hinit', cycles, output, ?_⟩
  · rw [hPC', Std.ExtDHashMap.get?_insert_self, Std.ExtDHashMap.get?_eq_some_get (hinit'' _)]
  · rw [hxreg' idx]; exact SailState.get_reg?_insert_PC
  · rw [hframe' R hRm, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => hRpc (beq_iff_eq.mp hc).symm)]
  · simpa only [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get_insert,
      show (Register.PC == Register.minstret_increment) = false from rfl,
      show (Register.PC == Register.minstret) = false from rfl,
      Bool.false_eq_true, ↓reduceDIte] using retired

/-- The architectural projection retains the original tail interface. -/
theorem tail_effect (s'' : SailState) (hinit'' : s''.isInitialized) :
    ∃ s_final : SailState,
      (do
        tick_pc ()
        let mi ← LeanRV64D.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← LeanRV64D.readReg Register.minstret
            LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
            (pure false : SailM Bool)
          else (pure false : SailM Bool)).run s'' = .ok false s_final
      ∧ s_final.regs.get? Register.PC = s''.regs.get? Register.nextPC
      ∧ (∀ idx : BitVec 5, s_final.get_reg? idx = s''.get_reg? idx)
      ∧ s_final.mem = s''.mem
      ∧ (∀ R : Register, R ≠ Register.PC → R ≠ Register.minstret →
          s_final.regs.get? R = s''.regs.get? R)
      ∧ s_final.isInitialized := by
  obtain ⟨next, ran, pc, regs, memory, frame, initialized, _⟩ := tail_bookkeeping s'' hinit''
  exact ⟨next, ran, pc, regs, memory, frame, initialized⟩

/-- **The core `SailStep` composition** — joins the landed ladder (`tryStep_reaches`) with the tail's
observable effect (`tail_effect`). Given the ladder inputs on the post-minstret-write state, `try_step`
takes one real step to some `s_final` whose `PC` is the post-execute `nextPC` and whose `BitVec 5`
register file agrees with the post-execute state `s''`. This is the whole `try_step`-side content of a
register-writing chip's `advance`; per-chip work is only characterizing `s''` (via the execute bridge)
and building the ladder inputs from `RefinesAt`/`OperandsBound`. -/
theorem sailStep_of_ladder_bookkeeping (s s_a s'' : SailState) (w : BitVec 32) (I : instruction) (b : Bool)
    (hb : (should_inc_minstret Privilege.Machine).run s = .ok b s)
    (hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b}) w)
    (hdec : (ext_decode w).run ({s with regs := s.regs.insert Register.minstret_increment b})
      = .ok I ({s with regs := s.regs.insert Register.minstret_increment b}))
    (hsa : (LeanRV64D.writeReg Register.nextPC (BitVec.addInt
        ((s.regs.insert Register.minstret_increment b).get Register.PC (hslr.init Register.PC)) 4)).run
        ({s with regs := s.regs.insert Register.minstret_increment b}) = .ok () s_a)
    (hexec : (execute I).run s_a = .ok (ExecutionResult.Retire_Success ()) s'')
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (hinit'' : s''.isInitialized) :
    ∃ s_final : SailState, (try_step 0 false).run s = .ok false s_final
      ∧ SailRetiresNormally s s_final
      ∧ s_final.regs.get? Register.PC = s''.regs.get? Register.nextPC
      ∧ (∀ idx : BitVec 5, s_final.get_reg? idx = s''.get_reg? idx)
      ∧ s_final.mem = s''.mem
      ∧ (∀ R : Register, R ≠ Register.PC → R ≠ Register.minstret →
          s_final.regs.get? R = s''.regs.get? R)
      ∧ s_final.isInitialized
      ∧ s_final.cycleCount = s''.cycleCount ∧ s_final.sailOutput = s''.sailOutput
      ∧ s_final.regs.get? Register.minstret =
        (s''.regs.get? Register.minstret).map (fun value =>
          if (true && s''.regs.get Register.minstret_increment (hinit'' _)) = true
          then BitVec.addInt value 1 else value) := by
  obtain ⟨s_final, hrun, hPC, hxreg, hmem, hframe, hinitf, cycles, output, retired⟩ := tail_bookkeeping s'' hinit''
  have hstep : (try_step 0 false).run s = .ok false s_final := by
    rw [tryStep_reaches s s_a s'' w I b hb hcp hactive hslr hdec hsa hexec h_active'']
    exact hrun
  refine ⟨s_final, hstep, ?_, hPC, hxreg, hmem, hframe, hinitf, cycles, output, retired⟩
  exact ⟨b, zero_extend (m := 32) w, s'', hb,
    run_hart_active_reaches _ s_a s'' w I 0 hslr hdec hsa hexec, hstep⟩

/-- The existing ladder statement projects from the complete bookkeeping result. -/
theorem sailStep_of_ladder (s s_a s'' : SailState) (w : BitVec 32) (I : instruction) (b : Bool)
    (hb : (should_inc_minstret Privilege.Machine).run s = .ok b s)
    (hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b}) w)
    (hdec : (ext_decode w).run ({s with regs := s.regs.insert Register.minstret_increment b})
      = .ok I ({s with regs := s.regs.insert Register.minstret_increment b}))
    (hsa : (LeanRV64D.writeReg Register.nextPC (BitVec.addInt
        ((s.regs.insert Register.minstret_increment b).get Register.PC (hslr.init Register.PC)) 4)).run
        ({s with regs := s.regs.insert Register.minstret_increment b}) = .ok () s_a)
    (hexec : (execute I).run s_a = .ok (ExecutionResult.Retire_Success ()) s'')
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (hinit'' : s''.isInitialized) :
    ∃ s_final : SailState, (try_step 0 false).run s = .ok false s_final
      ∧ SailRetiresNormally s s_final
      ∧ s_final.regs.get? Register.PC = s''.regs.get? Register.nextPC
      ∧ (∀ idx : BitVec 5, s_final.get_reg? idx = s''.get_reg? idx)
      ∧ s_final.mem = s''.mem
      ∧ (∀ R : Register, R ≠ Register.PC → R ≠ Register.minstret →
          s_final.regs.get? R = s''.regs.get? R)
      ∧ s_final.isInitialized := by
  obtain ⟨next, ran, normal, pc, regs, memory, frame, initialized, _⟩ :=
    sailStep_of_ladder_bookkeeping s s_a s'' w I b hb hcp hactive hslr hdec hsa hexec h_active'' hinit''
  exact ⟨next, ran, normal, pc, regs, memory, frame, initialized⟩

end SP1Clean.Advance
