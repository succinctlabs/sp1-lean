import SP1Clean.Model.Semantics.SailRetirement

/-! # Circuit-independent execute and retirement frames

Shared configuration frames and the official retirement composition. The inversion theorem
recovers an actual normally retiring execute stage without assuming total success of that stage.
Instruction families discharge its direct-execution and preservation obligations.
-/

namespace SP1Clean.Advance
open SP1Clean Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction

/-- Initialization supplies an actual value for every architectural GPR, including x0. -/
theorem initialized_gpr (source : SailState) (initialized : source.isInitialized) (index : BitVec 5) :
    ∃ value, source.get_reg? index = some value := by
  unfold SailState.get_reg?
  split_ifs
  · exact ⟨_, rfl⟩
  · refine ⟨cast (reg_idx_must_64 index) (source.regs.get _ (initialized _)), ?_⟩
    rw [Std.ExtDHashMap.get?_eq_some_get (initialized _)]
    simp only [eqRec_eq_cast]
    apply cast_eq_iff_heq.mpr
    congr 1
    · exact reg_idx_must_64 index
    · exact (cast_heq _ _).symm

/-- Staging the sequential successor does not change the platform configuration. -/
theorem SailConfigured.writeNextPC {source : SailState} (configured : SailConfigured source)
    (pc : BitVec 64) : SailConfigured { source with regs := source.regs.insert Register.nextPC pc } := by
  apply SailConfigured.congr configured (source.isInitialized_insert configured.init _ _)
  rintro register (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]

/-- A GPR write, or a discarded x0 write, preserves the platform configuration. -/
theorem SailConfigured.writeGPR {source : SailState} (configured : SailConfigured source)
    (rd : BitVec 5) (value : BitVec 64) :
    SailConfigured (if rd = 0 then source else
      { source with regs := source.regs.insert (reg_idx_to_Register rd) (bitVecToRegidxVal rd value) }) := by
  split_ifs
  · exact configured
  · apply SailConfigured.congr configured (source.isInitialized_insert configured.init _ _)
    rintro register (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      rw [Std.ExtDHashMap.get?_insert, dif_neg (by unfold reg_idx_to_Register; split <;> decide)]

/-- Compose an execute stage observing the actual incoming registers, memory and staged successor
with official retirement, retaining an arbitrary predicate on its resulting memory. -/
theorem retire_memory_of_observed_execute {program : GuestProgram} {source : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (memoryProperty : Std.ExtHashMap ℕ (BitVec 8) → Prop)
    (executeFrame : ∀ state, SailConfigured state →
      (∀ index, state.get_reg? index = source.get_reg? index) → state.mem = source.mem →
      state.regs.get? Register.PC = some pc →
      state.regs.get? Register.nextPC = some (pc + 4#64) → ∃ next,
      (execute decoded).run state = .ok (.Retire_Success ()) next ∧
        SailConfigured next ∧ memoryProperty next.mem) :
    ∃ target, SailRetiresNormally source target ∧ SailConfigured target ∧ memoryProperty target.mem := by
  obtain ⟨increment, incrementRun⟩ : ∃ increment,
      (should_inc_minstret Privilege.Machine).run source = .ok increment source :=
    ⟨_, run_should_inc_minstret source configured.init _⟩
  let marked : SailState := {source with regs := source.regs.insert Register.minstret_increment increment}
  have markedCfg : SailConfigured marked := SailConfigured.writeMinstret configured increment
  have ready : StraightLineReady marked word := by
    simpa only [word_reassemble] using SailConfigured.toStraightLineReady configured increment pc _ _ _ _
      (fetchReady_of_romLoaded program source pc word loaded fetched atPc)
  let nextPc := BitVec.addInt (marked.regs.get Register.PC (ready.init _)) 4
  let staged : SailState := {marked with regs := marked.regs.insert Register.nextPC nextPc}
  have stagedCfg : SailConfigured staged := SailConfigured.writeNextPC markedCfg _
  have markedPc : marked.regs.get? Register.PC = some pc := by
    simpa only [marked, Std.ExtDHashMap.get?_insert, beq_iff_eq, reduceCtorEq, ↓reduceDIte] using atPc
  have pcValue : marked.regs.get Register.PC (ready.init _) = pc := by
    rwa [Std.ExtDHashMap.get?_eq_some_get (ready.init _), Option.some.injEq] at markedPc
  have observed : ∀ index, staged.get_reg? index = source.get_reg? index := by
    intro index
    exact (SailState.get_reg?_insert_of_ne (s := marked)
      (by unfold reg_idx_to_Register; split <;> decide)).trans
      (SailState.get_reg?_insert_of_ne (s := source)
        (by unfold reg_idx_to_Register; split <;> decide))
  have stagedPc : staged.regs.get? Register.PC = some pc := by
    simpa only [staged, Std.ExtDHashMap.get?_insert, beq_iff_eq, reduceCtorEq, ↓reduceDIte] using markedPc
  have stagedNext : staged.regs.get? Register.nextPC = some (pc + 4#64) := by
    simp only [staged, Std.ExtDHashMap.get?_insert_self, nextPc, pcValue]
    rfl
  obtain ⟨post, executed, postCfg, memory⟩ := executeFrame staged stagedCfg observed rfl stagedPc stagedNext
  obtain ⟨actual, _, normal, _, _, sameMemory, registerFrame, initialized, _⟩ :=
    sailStep_of_ladder_bookkeeping source staged post word decoded increment incrementRun
      (by rw [Sail.run_readReg, configured.priv]) markedCfg.active ready (decode marked markedCfg)
      (by rw [Sail.run_writeReg]) executed postCfg.active postCfg.init
  refine ⟨actual, normal, ?_, by rwa [sameMemory]⟩
  apply SailConfigured.congr postCfg initialized
  rintro register (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    exact registerFrame _ (by decide) (by decide)

/-- A state-preserving execute stage composes with official retirement and its full memory frame. -/
theorem retire_frame_of_observed_execute {program : GuestProgram} {source : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (executeFrame : ∀ state, SailConfigured state →
      (∀ index, state.get_reg? index = source.get_reg? index) →
      state.regs.get? Register.PC = some pc →
      state.regs.get? Register.nextPC = some (pc + 4#64) → ∃ next,
      (execute decoded).run state = .ok (.Retire_Success ()) next ∧
        SailConfigured next ∧ next.mem = state.mem) :
    ∃ target, SailRetiresNormally source target ∧ SailConfigured target ∧ target.mem = source.mem := by
  apply retire_memory_of_observed_execute configured loaded atPc fetched decode
    (fun memory => memory = source.mem)
  intro state cfg observed sameMemory current successor
  obtain ⟨next, ran, nextCfg, preserved⟩ := executeFrame state cfg observed current successor
  exact ⟨next, ran, nextCfg, preserved.trans sameMemory⟩

/-- A total execute-stage frame is a special case of the observed-state retirement composition. -/
theorem retire_frame_of_execute {program : GuestProgram} {source : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (executeFrame : ∀ state, SailConfigured state → ∃ next,
      (execute decoded).run state = .ok (.Retire_Success ()) next ∧
        SailConfigured next ∧ next.mem = state.mem) :
    ∃ target, SailRetiresNormally source target ∧ SailConfigured target ∧ target.mem = source.mem :=
  retire_frame_of_observed_execute configured loaded atPc fetched decode
    (fun state cfg _ _ _ => executeFrame state cfg)

/-- A successful sequential Sail action exposes its actual intermediate state and return value. -/
theorem run_bind_success {α β : Type} (action : SailM α) (next : α → SailM β)
    (source target : SailState) (value : β)
    (ran : (action >>= next).run source = .ok value target) :
    ∃ middle result, action.run source = .ok result middle ∧
      (next result).run middle = .ok value target := by
  cases h : action.run source with
  | error error state =>
    change action source = .error error state at h
    simp only [bind, EStateM.bind, EStateM.run, h] at ran
    cases ran
  | ok result middle =>
    exact ⟨middle, result, rfl, by rwa [run_bind_of_run' source middle action result h] at ran⟩

/-- Recover actual incoming GPR observations and a direct execute result, then transport an
arbitrary memory predicate through official normal-retirement bookkeeping. -/
theorem normal_memory_of_observed_direct_execute {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (memoryProperty : Std.ExtHashMap ℕ (BitVec 8) → Prop)
    (frame : ∀ state, SailConfigured state →
      (∀ index, state.get_reg? index = source.get_reg? index) → state.mem = source.mem → ∀ result next,
      (execute decoded).run state = .ok result next →
        (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured next ∧ memoryProperty next.mem)
    (normal : SailRetiresNormally source target) :
    SailConfigured target ∧ memoryProperty target.mem := by
  obtain ⟨increment, bits, post, incrementRun, hartRun, targetRun⟩ := normal
  let marked : SailState := {source with regs := source.regs.insert Register.minstret_increment increment}
  have markedCfg : SailConfigured marked := SailConfigured.writeMinstret configured increment
  have ready : StraightLineReady marked word := by
    simpa only [word_reassemble] using SailConfigured.toStraightLineReady configured increment pc _ _ _ _
      (fetchReady_of_romLoaded program source pc word loaded fetched atPc)
  let nextPc := BitVec.addInt (marked.regs.get Register.PC (ready.init _)) 4
  let staged : SailState := {marked with regs := marked.regs.insert Register.nextPC nextPc}
  have stagedCfg : SailConfigured staged := SailConfigured.writeNextPC markedCfg _
  have reduced := hartRun
  rw [run_hart_active_eq_of_ready marked word decoded 0 ready (decode marked markedCfg),
    run_bind_of_run marked _ _ (Sail.run_readReg_of_isInitialized marked Register.PC ready.init),
    run_writeReg_bind] at reduced
  obtain ⟨afterExecute, result, executeRun, rest⟩ := run_bind_success _ _ staged post _ reduced
  have observed : ∀ index, staged.get_reg? index = source.get_reg? index := by
    intro index
    exact (SailState.get_reg?_insert_of_ne (s := marked)
      (by unfold reg_idx_to_Register; split <;> decide)).trans
      (SailState.get_reg?_insert_of_ne (s := source)
        (by unfold reg_idx_to_Register; split <;> decide))
  obtain ⟨direct, afterCfg, memory⟩ := frame staged stagedCfg observed rfl result afterExecute executeRun
  have returned : result = .Retire_Success () ∧ afterExecute = post := by
    cases result
    case ExecuteAs other => exact False.elim (direct other rfl)
    all_goals
      change EStateM.Result.ok (Step.Step_Execute (_, zero_extend word)) afterExecute =
        EStateM.Result.ok (Step.Step_Execute (.Retire_Success (), bits)) post at rest
      cases rest <;> exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := returned
  obtain ⟨actual, tailRun, _, _, memoryTail, registers, initialized, _⟩ := tail_bookkeeping _ afterCfg.init
  rw [tryStep_eq_of_hart_active source 0 increment bits afterExecute markedCfg.active incrementRun
    (by rw [Sail.run_readReg, configured.priv]) hartRun afterCfg.active, tailRun] at targetRun
  cases targetRun
  refine ⟨?_, by rwa [memoryTail]⟩
  apply SailConfigured.congr afterCfg initialized
  rintro register (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    exact registers _ (by decide) (by decide)

/-- A complete-memory frame is a special case of observed-state normal retirement. -/
theorem normal_frame_of_direct_execute {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (frame : ∀ state, SailConfigured state → ∀ result next,
      (execute decoded).run state = .ok result next →
        (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured next ∧ next.mem = state.mem)
    (normal : SailRetiresNormally source target) :
    SailConfigured target ∧ target.mem = source.mem := by
  apply normal_memory_of_observed_direct_execute configured loaded atPc fetched decode
    (fun memory => memory = source.mem) ?_ normal
  intro state cfg _ sameMemory result next ran
  obtain ⟨direct, nextCfg, preserved⟩ := frame state cfg result next ran
  exact ⟨direct, nextCfg, preserved.trans sameMemory⟩

end SP1Clean.Advance
