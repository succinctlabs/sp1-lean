import SP1Clean.Model.Semantics.SailMemoryRead

/-! # Independent load preservation

The actual Sail load path preserves configuration and memory. Physical split accesses and faults
are included; normal retirement, rather than an alignment or address-readiness premise, selects
the successful instruction result.
-/

namespace SP1Clean.Advance
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.SailMem SP1Clean.SailFrame SP1Clean.Soundness.Target SP1Clean.TryStepReduction

private theorem translate_read_frame (source : SailState) (cfg : SailConfigured source)
    (address : BitVec 64) (width : ℕ) (result : Result (physaddr × BitVec (8 * width)) ExecutionResult)
    (target : SailState)
    (ran : (translate_and_read_value (.Virtaddr address) width (.Load .Data)
      false false false).run source = .ok result target) :
    target = source ∧ ∀ other, result ≠ .Err (.ExecuteAs other) := by
  unfold translate_and_read_value at ran
  rw [run_bind_of_run source _ _
    (run_translateAddr_load_of_isInitialized address source cfg.init cfg.toValidMemConfig)] at ran
  obtain ⟨middle, value, readRun, rest⟩ := run_bind_success _ _ source target result ran
  have same := readOnly_mem_read source cfg _ _ value middle readRun
  subst middle
  cases value with
  | Ok value =>
    cases rest
    exact ⟨rfl, fun _ h => nomatch h⟩
  | Err error =>
    rcases error with ⟨faultAddress, error⟩
    rw [run_bind_of_run source _ _ (run_memory_exception source cfg _ error)] at rest
    cases rest
    exact ⟨rfl, fun _ h => nomatch h⟩

/-- A virtual load either returns bytes or reports a trap, leaving the entire state unchanged. -/
theorem vmem_read_addr_frame (source : SailState) (cfg : SailConfigured source)
    (address : BitVec 64) (width : ℕ) (result : Result (BitVec (8 * width)) ExecutionResult)
    (target : SailState)
    (ran : (vmem_read_addr (.Virtaddr address) width (.Load .Data)
      false false false).run source = .ok result target) :
    target = source ∧ ∀ other, result ≠ .Err (.ExecuteAs other) := by
  simp only [vmem_read_addr, plat_misaligned_exception, is_amo_access, is_vector_access,
    plat_misaligned_access, Bool.false_eq_true, ↓reduceIte, ite_self, pure_bind,
    SailME.run, run_SailME_liftM_bind] at ran
  obtain ⟨middle, pages, pageRun, rest⟩ := run_bind_success _ _ source target result ran
  have same := readOnly_split_on_page_boundary source address width pages middle pageRun
  subst middle
  rcases pages with ⟨inPage, nextPage⟩
  rw [run_readReg_bind_of_isInitialized source Register.mstatus cfg.init,
    run_readReg_bind_of_isInitialized source Register.cur_privilege cfg.init,
    run_bind_of_run source _ _ (run_effectivePrivilege_configured source cfg _),
    run_bind_of_run source _ _ (run_translationMode_machine source)] at rest
  simp only [show (SATPMode.Bare != SATPMode.Bare) = false from rfl,
    Bool.false_and, pure_bind, sys_misaligned_order_decreasing,
    Bool.false_eq_true, ↓reduceIte, LeanRV64D.Functions.not, Bool.not_false, Bool.true_and,
    bind_assoc, run_SailME_liftM_bind] at rest
  obtain ⟨middle, value, readRun, suffix⟩ := run_bind_success _ _ source target result rest
  obtain ⟨same, direct⟩ := translate_read_frame source cfg address width value middle readRun
  subst middle
  cases value with
  | Ok value =>
    rcases value with ⟨physical, bytes⟩
    cases suffix
    exact ⟨rfl, fun _ h => nomatch h⟩
  | Err error =>
    cases suffix
    refine ⟨rfl, fun other same => direct other ?_⟩
    cases same
    rfl

/-- A register-relative load uses the actual wrapped base-plus-offset address and preserves state. -/
theorem vmem_read_frame (source : SailState) (cfg : SailConfigured source)
    (rs1 : BitVec 5) (offset : BitVec 64) (width : ℕ)
    (result : Result (BitVec (8 * width)) ExecutionResult) (target : SailState)
    (ran : (vmem_read (.Regidx rs1) offset width (.Load .Data)
      false false false).run source = .ok result target) :
    target = source ∧ ∀ other, result ≠ .Err (.ExecuteAs other) := by
  obtain ⟨base, observed⟩ := initialized_gpr source cfg.init rs1
  simp only [vmem_read, bind_assoc, SailME.run, run_SailME_liftM_bind] at ran
  rw [run_bind_of_run source _ _ (run_get_transformed_data_addr_load rs1 base offset width
    (.Load .Data) (by decide) (by decide) (by decide) source cfg.init observed cfg.toValidMemConfig)] at ran
  simp only [pure_bind, run_SailME_liftM] at ran
  exact vmem_read_addr_frame source cfg _ width result target ran

/-- Loads preserve configuration and memory for every actual execute result, including x0. -/
theorem load_execute_frame (source : SailState) (cfg : SailConfigured source)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (unsigned : Bool) (width : word_width)
    (result : ExecutionResult) (target : SailState)
    (ran : (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, unsigned, width))).run source =
      .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem := by
  simp only [execute, execute_LOAD, PreSail.assert] at ran
  split at ran
  · simp only [pure_bind] at ran
    obtain ⟨middle, value, readRun, rest⟩ := run_bind_success _ _ source target result ran
    obtain ⟨same, direct⟩ := vmem_read_frame source cfg rs1 _ _ value middle readRun
    subst middle
    cases value with
    | Ok bytes =>
      rw [run_bind_of_run' source _ _ () (run_wX_bits (.Regidx rd) (extend_value unsigned bytes))] at rest
      cases rest
      exact ⟨(fun _ h => nomatch h), SailConfigured.writeGPR cfg rd _, by
        by_cases zero : rd = 0#5 <;> simp only [zero, ↓reduceIte]⟩
    | Err error =>
      cases rest
      exact ⟨fun other same => direct other (congrArg Result.Err same), cfg, rfl⟩
  · cases ran

/-- Normal load retirement preserves the configured platform and the complete memory map. -/
theorem load_normal_frame {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {imm : BitVec 12} {rs1 rd : BitVec 5}
    {unsigned : Bool} {width : word_width}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc) (fetched : program.fetchWord pc = some word)
    (decode : ConfiguredDecode word (.LOAD (imm, .Regidx rs1, .Regidx rd, unsigned, width)))
    (normal : SailRetiresNormally source target) :
    SailConfigured target ∧ target.mem = source.mem :=
  normal_frame_of_direct_execute configured loaded atPc fetched decode
    (fun state cfg result next => load_execute_frame state cfg imm rs1 rd unsigned width result next) normal

end SP1Clean.Advance
