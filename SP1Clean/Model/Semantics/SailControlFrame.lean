import SP1Clean.Model.Semantics.SailExecuteFrame

/-! # Circuit-independent control-flow preservation

JAL, JALR and all six branch conditions preserve the configured platform and full memory map.
The proof recovers the actual execute stage of a normal retirement; jump alignment and successful
execution are not additional premises. Trap outcomes cannot masquerade as normal retirement.
-/

namespace SP1Clean.Advance
open SP1Clean Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction

/-- A jump either traps or stages its destination, preserving configuration and all memory. -/
theorem jump_to_frame (source : SailState) (cfg : SailConfigured source) (destination : BitVec 64)
    (result : ExecutionResult) (target : SailState)
    (ran : (jump_to destination).run source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem := by
  simp only [jump_to, ext_control_check_pc, SailME.run, run_SailME_liftM_bind] at ran
  by_cases low : (BitVec.access destination 0 == 0#1) = true
  · simp only [PreSail.assert, low, ↓reduceIte, pure_bind] at ran
    rw [run_bind_of_run source _ _ (currentlyEnabled_zca_eq_false source cfg)] at ran
    simp only [LeanRV64D.Functions.not, Bool.not_false, Bool.and_true] at ran
    split at ran
    · rw [run_SailME_liftM] at ran
      simp only [memory_exception, trap] at ran
      rw [run_readReg_bind_of_isInitialized source Register.cur_privilege cfg.init,
        run_readReg_bind_of_isInitialized source Register.PC cfg.init] at ran
      cases ran
      exact ⟨(fun _ h => nomatch h), cfg, rfl⟩
    · rw [run_SailME_liftM_bind, run_SailME_pure] at ran
      simp only [set_next_pc] at ran
      cases ran
      exact ⟨(fun _ h => nomatch h), SailConfigured.writeNextPC cfg _, rfl⟩
  · simp only [PreSail.assert, low, bind, EStateM.bind, EStateM.run, throw] at ran
    cases ran

private theorem jump_and_link_frame (source : SailState) (cfg : SailConfigured source)
    (destination link : BitVec 64) (rd : BitVec 5) (result : ExecutionResult) (target : SailState)
    (ran : (do
      match ← jump_to destination with
      | .Retire_Success () => wX_bits (.Regidx rd) link; pure (ExecutionResult.Retire_Success ())
      | failure => pure failure).run source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem := by
  obtain ⟨middle, outcome, jumpRun, suffix⟩ := run_bind_success _ _ source target result ran
  obtain ⟨direct, configured, memory⟩ := jump_to_frame source cfg destination outcome middle jumpRun
  by_cases success : outcome = .Retire_Success ()
  · subst outcome
    rw [run_bind_of_run' middle _ _ () (run_wX_bits (.Regidx rd) link)] at suffix
    cases suffix
    exact ⟨(fun _ h => nomatch h), SailConfigured.writeGPR configured rd link, by
      by_cases zero : rd = 0#5 <;> simpa only [zero, ↓reduceIte] using memory⟩
  · cases outcome <;> first | contradiction | (cases suffix; exact ⟨direct, configured, memory⟩)

/-- JAL preserves configuration and every byte for every successful execute result. -/
theorem jal_execute_frame (source : SailState) (cfg : SailConfigured source)
    (imm : BitVec 21) (rd : BitVec 5) (result : ExecutionResult) (target : SailState)
    (ran : (execute (.JAL (imm, .Regidx rd))).run source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem := by
  simp only [execute, execute_JAL, get_next_pc] at ran
  rw [run_readReg_bind_of_isInitialized source Register.nextPC cfg.init,
    run_readReg_bind_of_isInitialized source Register.PC cfg.init] at ran
  exact jump_and_link_frame source cfg _ _ rd result target ran

/-- JALR preserves configuration and every byte, using Sail’s masked target and ELP handling. -/
theorem jalr_execute_frame (source : SailState) (cfg : SailConfigured source)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (result : ExecutionResult) (target : SailState)
    (ran : (execute (.JALR (imm, .Regidx rs1, .Regidx rd))).run source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem := by
  obtain ⟨value, read⟩ := initialized_gpr source cfg.init rs1
  simp only [execute, execute_JALR, get_next_pc] at ran
  rw [run_bind_of_run source _ () (SailMem.update_elp_state_of_isInitialized _ source cfg.init cfg.toValidMemConfig),
    run_readReg_bind_of_isInitialized source Register.nextPC cfg.init,
    run_bind_of_run source _ value (by rw [run_rX_bits, read])] at ran
  simp only [pure_bind] at ran
  exact jump_and_link_frame source cfg _ _ rd result target ran

/-- Every branch condition preserves configuration and every byte, taken or not taken. -/
theorem branch_execute_frame (source : SailState) (cfg : SailConfigured source)
    (imm : BitVec 13) (rs1 rs2 : BitVec 5) (op : bop) (result : ExecutionResult) (target : SailState)
    (ran : (execute (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op))).run source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem := by
  obtain ⟨left, leftRead⟩ := initialized_gpr source cfg.init rs1
  obtain ⟨right, rightRead⟩ := initialized_gpr source cfg.init rs2
  have leftRun : (rX_bits (.Regidx rs1)).run source = .ok left source := by rw [run_rX_bits, leftRead]
  have rightRun : (rX_bits (.Regidx rs2)).run source = .ok right source := by rw [run_rX_bits, rightRead]
  cases op <;>
    simp only [execute, execute_BTYPE, bind_assoc,
      run_bind_of_run source _ left leftRun, run_bind_of_run source _ right rightRun, pure_bind] at ran
  all_goals
    split at ran
    · rw [run_readReg_bind_of_isInitialized source Register.PC cfg.init] at ran
      exact jump_to_frame source cfg _ result target ran
    · cases ran
      exact ⟨(fun _ h => nomatch h), cfg, rfl⟩

/-- The control-flow families covered here; this classification does not redefine native support. -/
def ControlFlowInstruction : instruction → Prop
  | .JAL _ => True
  | .JALR _ => True
  | .BTYPE _ => True
  | _ => False

/-- Normally retiring control flow preserves the platform and every byte without a target-fetch
or target-alignment premise. This includes discarded links to x0 and the JALR low-bit mask. -/
theorem control_normal_frame {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (control : ControlFlowInstruction decoded) (normal : SailRetiresNormally source target) :
    SailConfigured target ∧ target.mem = source.mem := by
  apply normal_frame_of_direct_execute configured loaded atPc fetched decode ?_ normal
  intro state cfg result next executed
  unfold ControlFlowInstruction at control
  split at control
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rd⟩⟩
    exact jal_execute_frame state cfg imm rd result next executed
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rs1⟩, ⟨rd⟩⟩
    exact jalr_execute_frame state cfg imm rs1 rd result next executed
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rs2⟩, ⟨rs1⟩, op⟩
    exact branch_execute_frame state cfg imm rs1 rs2 op result next executed
  next => contradiction

end SP1Clean.Advance
