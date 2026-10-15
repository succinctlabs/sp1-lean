import SP1Clean.Model.Semantics.SailMemoryWrite
import SP1Clean.Model.Core.InstructionWrite

/-! # Independent store preservation

Ordinary stores use the exact decoded byte permissions at their incoming registers. The proof
follows actual virtual/physical checks and split writes through normal Sail retirement.
-/

namespace SP1Clean.Advance
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.SailMem SP1Clean.Soundness.Target SP1Clean.TryStepReduction

/-- Virtual stores preserve registers and protected bytes, including fault outcomes. -/
theorem vmem_write_addr_frame (readOnly : ℕ → Bool) (source : SailState) (cfg : SailConfigured source)
    (address : BitVec 64) (width : ℕ) (positive : 0 < width) (small : width ≤ 8)
    (data : BitVec (8 * width)) (allowed : ∀ index < width, readOnly (address.toNat + index) = false)
    (result : Result Bool ExecutionResult) (target : SailState)
    (ran : (vmem_write_addr (.Virtaddr address) width data (.Store .Data)
      false false false).run source = .ok result target) :
    ProtectedMemoryFrame readOnly source target ∧ ∀ other, result ≠ .Err (.ExecuteAs other) := by
  simp only [vmem_write_addr, plat_misaligned_exception, is_amo_access, is_vector_access,
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
    Bool.false_and, pure_bind, sys_misaligned_order_decreasing, Bool.false_eq_true,
    ↓reduceIte, LeanRV64D.Functions.not, Bool.not_false, Bool.true_and,
    bind_assoc, run_SailME_liftM_bind] at rest
  rw [run_bind_of_run source _ _
    (run_translateAddr_store_of_isInitialized address source cfg.init cfg.toValidMemConfig)] at rest
  simp only [is_store_conditional, beq_self_eq_true, PreSail.assert, ↓reduceIte, pure_bind,
    bind_assoc, run_SailME_liftM_bind] at rest
  obtain ⟨middle, validated, checked, suffix⟩ := run_bind_success _ _ source target result rest
  have same := readOnly_mem_write_ea source cfg _ _ validated middle checked
  subst middle
  cases validated with
  | Err error =>
    rcases error with ⟨faultAddress, error⟩
    simp only [bind_assoc, run_SailME_liftM_bind] at suffix
    rw [run_bind_of_run source _ _ (run_memory_exception source cfg _ error)] at suffix
    cases suffix
    exact ⟨.refl readOnly source, fun _ h => nomatch h⟩
  | Ok value =>
    cases value
    simp only [bind_assoc, run_SailME_liftM_bind] at suffix
    obtain ⟨middle, written, writeRun, tail⟩ := run_bind_success _ _ source target result suffix
    have frame := mem_write_value_frame readOnly source cfg _ width positive small _
      (by simpa [zero_extend, Sail.BitVec.zeroExtend] using allowed) written middle writeRun
    cases written with
    | Ok value =>
      cases tail
      exact ⟨frame, fun _ h => nomatch h⟩
    | Err error =>
      rcases error with ⟨faultAddress, error⟩
      simp only [bind_assoc, run_SailME_liftM_bind] at tail
      rw [run_bind_of_run middle _ _ (run_memory_exception middle (frame.configured cfg) _ error)] at tail
      cases tail
      exact ⟨frame, fun _ h => nomatch h⟩

/-- A register-relative store frames its actual wrapped effective-address interval. -/
theorem vmem_write_frame (readOnly : ℕ → Bool) (source : SailState) (cfg : SailConfigured source)
    (rs1 : BitVec 5) (base offset : BitVec 64) (observed : source.get_reg? rs1 = some base)
    (width : ℕ) (positive : 0 < width) (small : width ≤ 8) (data : BitVec (8 * width))
    (allowed : ∀ index < width, readOnly ((base + offset).toNat + index) = false)
    (result : Result Bool ExecutionResult) (target : SailState)
    (ran : (vmem_write (.Regidx rs1) offset width data (.Store .Data)
      false false false).run source = .ok result target) :
    ProtectedMemoryFrame readOnly source target ∧ ∀ other, result ≠ .Err (.ExecuteAs other) := by
  simp only [vmem_write, bind_assoc, SailME.run, run_SailME_liftM_bind] at ran
  rw [run_bind_of_run source _ _ (run_get_transformed_data_addr_load rs1 base offset width
    (.Store .Data) (by decide) (by decide) (by decide) source cfg.init observed cfg.toValidMemConfig)] at ran
  simp only [pure_bind, run_SailME_liftM] at ran
  exact vmem_write_addr_frame readOnly source cfg _ width positive small data allowed result target ran

private theorem store_width_bounds (width : word_width) (valid : storeWidthOK width = true) :
    0 < width.toNat ∧ width.toNat ≤ 8 := by
  simp only [storeWidthOK, Bool.or_eq_true, beq_iff_eq] at valid
  rcases valid with ((rfl | rfl) | rfl) | rfl <;> decide

/-- Actual store execution retains the complete write frame, including byte presence. -/
theorem store_execute_memory_frame (readOnly : ℕ → Bool) (source : SailState) (cfg : SailConfigured source)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (width : word_width)
    (permission : Model.Core.InstructionWrite.check readOnly source.get_reg?
      (.STORE (imm, .Regidx rs2, .Regidx rs1, width)) = true)
    (result : ExecutionResult) (target : SailState)
    (ran : (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, width))).run source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ ProtectedMemoryFrame readOnly source target := by
  have valid := (Model.Core.InstructionWrite.check_supported readOnly source.get_reg? _ permission).1
  change storeWidthOK width = true at valid
  obtain ⟨positive, small⟩ := store_width_bounds width valid
  obtain ⟨base, observed, allowed⟩ := (Model.Core.InstructionWrite.check_store_iff
    readOnly source.get_reg? imm (.Regidx rs2) (.Regidx rs1) width valid).mp permission
  obtain ⟨data, dataRead⟩ := initialized_gpr source cfg.init rs2
  simp only [execute, execute_STORE, PreSail.assert] at ran
  split at ran
  · simp only [pure_bind] at ran
    rw [run_bind_of_run source _ data (by rw [run_rX_bits, dataRead])] at ran
    obtain ⟨middle, value, written, rest⟩ := run_bind_success _ _ source target result ran
    obtain ⟨frame, direct⟩ := vmem_write_frame readOnly source cfg rs1 base _ observed
      width.toNat positive small _ allowed value middle written
    cases value with
    | Ok value =>
      cases rest
      exact ⟨(fun _ h => nomatch h), frame⟩
    | Err error =>
      cases rest
      exact ⟨fun other same => direct other (congrArg Result.Err same), frame⟩
  · cases ran

/-- A permitted decoded store preserves configuration and every protected byte. -/
theorem store_execute_frame (readOnly : ℕ → Bool) (source : SailState) (cfg : SailConfigured source)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (width : word_width)
    (permission : Model.Core.InstructionWrite.check readOnly source.get_reg?
      (.STORE (imm, .Regidx rs2, .Regidx rs1, width)) = true)
    (result : ExecutionResult) (target : SailState)
    (ran : (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, width))).run source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧
      ∀ address, readOnly address = true → target.mem.get? address = source.mem.get? address := by
  obtain ⟨direct, frame⟩ := store_execute_memory_frame readOnly source cfg imm rs2 rs1 width permission result target ran
  exact ⟨direct, frame.configured cfg, frame.memory⟩

/-- Normally retiring SB/SH/SW/SD preserve configuration and every byte protected by their actual
decoded write permission. Existing byte presence is retained as well; no alignment or compiler-readiness premise is added. -/
theorem store_normal_memory_frame {readOnly : ℕ → Bool} {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {imm : BitVec 12} {rs2 rs1 : BitVec 5} {width : word_width}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc) (fetched : program.fetchWord pc = some word)
    (decode : ConfiguredDecode word (.STORE (imm, .Regidx rs2, .Regidx rs1, width)))
    (permission : Model.Core.InstructionWrite.PermittedAt readOnly program source)
    (normal : SailRetiresNormally source target) :
    SailConfigured target ∧
      (∀ address, readOnly address = true → target.mem.get? address = source.mem.get? address) ∧
      ∀ address, (source.mem.get? address).isSome → (target.mem.get? address).isSome := by
  have checked := permission.check configured atPc fetched decode
  apply normal_memory_of_observed_direct_execute configured loaded atPc fetched decode
    (fun memory => (∀ address, readOnly address = true → memory.get? address = source.mem.get? address) ∧
      ∀ address, (source.mem.get? address).isSome → (memory.get? address).isSome) ?_ normal
  intro state cfg observed sameMemory result next ran
  have permitted : Model.Core.InstructionWrite.check readOnly state.get_reg?
      (.STORE (imm, .Regidx rs2, .Regidx rs1, width)) = true := by
    rw [funext observed]
    exact checked
  obtain ⟨direct, frame⟩ := store_execute_memory_frame readOnly state cfg imm rs2 rs1 width permitted result next ran
  refine ⟨direct, frame.configured cfg, ?_, ?_⟩
  · exact fun address selected => (frame.memory address selected).trans (by rw [sameMemory])
  · intro address present
    exact frame.present address (by simpa only [sameMemory] using present)

/-- Normally retiring SB/SH/SW/SD preserve configuration and every byte protected by their actual
decoded write permission. No alignment, address-window or compiler-readiness premise is added. -/
theorem store_normal_frame {readOnly : ℕ → Bool} {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {imm : BitVec 12} {rs2 rs1 : BitVec 5} {width : word_width}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc) (fetched : program.fetchWord pc = some word)
    (decode : ConfiguredDecode word (.STORE (imm, .Regidx rs2, .Regidx rs1, width)))
    (permission : Model.Core.InstructionWrite.PermittedAt readOnly program source)
    (normal : SailRetiresNormally source target) :
    SailConfigured target ∧
      ∀ address, readOnly address = true → target.mem.get? address = source.mem.get? address := by
  have frame := store_normal_memory_frame configured loaded atPc fetched decode permission normal
  exact ⟨frame.1, frame.2.1⟩

end SP1Clean.Advance
