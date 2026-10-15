import SP1Clean.Soundness.HostHintReadMemoryEffect

/-! # Installed syscall execution on the complete carrier

The physical wrapper inventory and full HostCall balance select either an installed queue row or
a control call. Queue dispatch uses the authenticated current hint history; control dispatch uses
the actual host at that prefix. Both feed the same timed step/frame assembly, so no handler case
or per-call semantic premise escapes the final SyscallInstrs statement. WRITE and VERIFY handlers
and complete outgoing snapshot authentication remain separate obligations.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance syscallLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance syscallLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem event_eq (left right : Machine.CoreSyscallEvent)
    (leftLaw : left.PcLaw) (rightLaw : right.PcLaw)
    (clock : left.clock = right.clock) (pc : left.pc = right.pc) (code : left.rawCode = right.rawCode)
    (arg1 : left.arg1 = right.arg1) (arg2 : left.arg2 = right.arg2) (result : left.result = right.result) :
    left = right := by
  have next : left.nextPc = right.nextPc := by
    simp only [Machine.CoreSyscallEvent.PcLaw, Machine.CoreSyscallEvent.syscallId, code, pc] at leftLaw rightLaw
    by_cases h : right.rawCode.toNat % 256 = Machine.haltSyscallId
    · simp only [h, if_true] at leftLaw rightLaw
      exact leftLaw.trans rightLaw.symm
    · simp only [h, if_false] at leftLaw rightLaw
      exact leftLaw.trans rightLaw.symm
  cases left
  cases right
  simp only at clock pc code arg1 arg2 result next
  cases clock
  cases pc
  cases code
  cases arg1
  cases arg2
  cases result
  cases next
  rfl

omit [Fact (2 ^ 25 < p)] in
private theorem event_of_run (wrapper : HostCallChip.Inputs (ZMod p)) (flag : ZMod p)
    (host : HostState) (policy : HostPolicy) (context : HostReadContext) (execution : HostExecution)
    (observed : context.register 5 = some (Word.toBitVec64 (wrapper.message flag).code) ∧
      context.register 10 = some (Word.toBitVec64 (wrapper.message flag).arg1) ∧
      context.register 11 = some (Word.toBitVec64 (wrapper.message flag).arg2))
    (ran : host.run policy context = some execution)
    (result : execution.result = Word.toBitVec64 (wrapper.message flag).result)
    (law : (syscallEventOfRow wrapper.instruction).RowLaw)
    (clock : ℕ) (atClock : clock = (syscallEventOfRow wrapper.instruction).clock) :
    execution.toEvent clock (StateMsg.pcBits (SyscallInstrsChip.statePulledMessage wrapper.instruction)) =
      syscallEventOfRow wrapper.instruction := by
  have dispatched := (host.run_eq_some_iff policy context execution).mp ran
  apply event_eq _ _ (execution.rowLaw dispatched.2.2.2.2.1 _ _).2.2.1 law.2.2.1 atClock rfl
  · exact Option.some.inj (dispatched.2.1.symm.trans observed.1)
  · exact Option.some.inj (dispatched.2.2.1.symm.trans observed.2.1)
  · exact Option.some.inj (dispatched.2.2.2.1.symm.trans observed.2.2)
  · exact result

private theorem syscall_physical {auxiliary : List (Component (ZMod p))}
    {names : ((HostLocalCore.tables image source auxiliary).map (·.circuit.name)).Nodup}
    (witness : EnsembleWitness (HostLocalCore.ensemble image source auxiliary channels names))
    {row : SyscallInstrsChip.Inputs (ZMod p)}
    (member : ExecutionRow.syscall row ∈ LocalCore.executionRows (HostLocalCore.localWitness witness)) :
    ∃ env ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable witness) witness.data,
      row = (HostCallLedger.input env).instruction := by
  have active : row ∈ activeSystemRows (LocalCore.systemTable (HostLocalCore.localWitness witness) 3)
      (syscallInstrsRow (HostLocalCore.localWitness witness).data) (·.is_real) := by simpa [LocalCore.executionRows] using member
  rw [← HostLocalCore.hostCallTable_projection witness] at active
  obtain ⟨env, active, same⟩ := List.mem_map.mp active
  exact ⟨env, active, same.symm⟩

private theorem control_not_read (event : ExecutionRow p) (wrapper : HostCallChip.Inputs (ZMod p))
    (flag : ZMod p) (same : event = .syscall wrapper.instruction)
    (code : Word.toBitVec64 (wrapper.message flag).code ≠ SyscallKind.hintRead.code) :
    ∀ row, event = .syscall row → (syscallEventOfRow row).rawCode ≠ SyscallKind.hintRead.code := by
  intro row rowEq
  have sameRow := ExecutionRow.syscall.inj (same.symm.trans rowEq)
  rw [← sameRow]
  exact code

private theorem control_step (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (physical : Environment (ZMod p))
    (active : physical ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable (HostHintQueueBoundary.projected witness)) witness.data)
    (sameEvent : event = .syscall (HostCallLedger.input physical).instruction)
    (notRead : Word.toBitVec64 (HostCallLedger.call physical).code ≠ SyscallKind.hintRead.code)
    (dispatch : ∀ (host : HostState), host.exitCode = none → ∀ (context : HostReadContext),
      (context.register 5 = some (Word.toBitVec64 (HostCallLedger.call physical).code) ∧
        context.register 10 = some (Word.toBitVec64 (HostCallLedger.call physical).arg1) ∧
        context.register 11 = some (Word.toBitVec64 (HostCallLedger.call physical).arg2)) →
      ∃ execution, host.run ⟨{ readOnly := image.readOnly }, p⟩ context = some execution ∧
        execution.result = Word.toBitVec64 (HostCallLedger.call physical).result ∧ execution.effect.write = none)
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (event.facts witness.data).statePull)
    (currency : ∀ mp ∈ (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∃ n current next, carrier.ordered[n]? = some event ∧
      carrier.pairedTrajectory valid n = some current ∧ carrier.pairedTrajectory valid (n + 1) = some next ∧
      ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event.event next ∧
      (∀ cell : RamCell, locContent next.sail (.ram cell) = locContent current.sail (.ram cell)) ∧
      wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event = [] := by
  obtain ⟨n, state, present, time, atPc, rom, _⟩ := pull
  change (carrier.pairedTrajectory valid n).map ExecutionState.sail = some state at present
  obtain ⟨current, paired, sail⟩ := Option.map_eq_some_iff.mp present
  rw [← sail] at atPc rom
  change current.sail.regs.get? LeanRV64D.Defs.Register.PC =
    some (StateMsg.pcBits (event.facts witness.data).statePull) at atPc
  have atIndex := ExecutionCarrier.ordered_at carrier member time
  have before : carrier.trajectory valid n = some current.sail := by
    simp only [GroundingCarrier.trajectory, paired, Option.map_some]
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have interface := source_interface (p := p) source.host.io.hints
  have program := HostHintQueueBoundary.projected_core_balancedChannel witness balanced programChannel.toRaw
    (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
  have byteBalance := (HostHintQueueBoundary.record_channels witness balanced).byte
  have original : ∀ mp ∈ (syscallRowFacts (HostCallLedger.input physical).instruction).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
    intro mp present
    apply currency mp
    apply List.mem_append_left
    simpa only [sameEvent, ExecutionRow.facts] using present
  have instructionTime : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
      (HostCallLedger.input physical).instruction) = carrier.timeline.start n := by
    simpa only [sameEvent, ExecutionRow.facts, syscallRowFacts_statePull] using time
  have registers := HostLocalCore.hostCall_registers valid (HostHintQueueBoundary.projected witness)
    (source_program_silent source) checks program
  simp only [HostHintQueueBoundary.projected_data] at registers
  have registers := registers physical active _ source.sail.realize current.sail _ n
    before instructionTime (fun mp present => (original mp present).2.2)
  have committed := HostLocalCore.hostCall_program_committed valid (HostHintQueueBoundary.projected witness)
    (source_program_silent source) checks program
  simp only [HostHintQueueBoundary.projected_data] at committed
  have committed := committed physical active
  have fetched := (committed.ecall_of_opcode rfl).1
  change (image.toGuestProgram valid).fetchWord
    (StateMsg.pcBits (SyscallInstrsChip.statePulledMessage (HostCallLedger.input physical).instruction)) =
      some Target.ECALL_ENC at fetched
  have sourcePc : StateMsg.pcBits (event.facts witness.data).statePull =
      StateMsg.pcBits (SyscallInstrsChip.statePulledMessage (HostCallLedger.input physical).instruction) := by
    rw [sameEvent]; rfl
  have atInstructionPc : current.sail.regs.get? LeanRV64D.Defs.Register.PC =
      some (StateMsg.pcBits (SyscallInstrsChip.statePulledMessage (HostCallLedger.input physical).instruction)) := by
    rwa [sourcePc] at atPc
  have running := carrier.pairedTrajectory_running_of_fetch valid constraints balanced member paired atInstructionPc fetched
  obtain ⟨execution, ran, result, noWrite⟩ := dispatch current.host running (.ofSail current.sail) registers
  have law := HostLocalCore.hostCall_eventLaw (HostHintQueueBoundary.projected witness)
    (auxiliaryInterface interface) (source_program_silent source) checks program byteBalance
  simp only [HostHintQueueBoundary.projected_data] at law
  have law := law physical active
    (fun mp present => ⟨(original mp present).1, (original mp present).2.1⟩)
  have covered : n ≤ carrier.events.length := by
    have bound := (List.getElem?_eq_some_iff.mp atIndex).1
    simpa only [ExecutionCarrier.events, List.length_map] using Nat.le_of_lt bound
  have currentTime : current.clock = carrier.timeline.start n := by
    rw [carrier.timeline_events constraints balanced, eventTimeline_start_le _ _ _ covered]
    exact replayEvents?_clock paired
  have label := event_of_run (HostCallLedger.input physical) _ current.host _ (.ofSail current.sail)
    execution registers ran result law.1 current.clock (currentTime.trans (instructionTime.symm.trans law.2.symm))
  let next : ExecutionState := ⟨execution.apply current.sail (StateMsg.pcBits (event.facts witness.data).statePull),
    execution.effect.state, current.clock + Machine.syscallSchedule.duration⟩
  have step : ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event.event next := by
    have stepped := HostState.step_of_run atPc (show (image.toGuestProgram valid).fetchWord
      (StateMsg.pcBits (event.facts witness.data).statePull) = some Target.ECALL_ENC by rwa [sourcePc])
      (InstructionBytes.check_of_romLoaded rom (by rwa [sourcePc])) ran current.clock
    rw [sourcePc, label] at stepped
    rw [sameEvent]
    apply ExecutionStep.syscall
    simpa only [next, sourcePc] using stepped
  have after : carrier.pairedTrajectory valid (n + 1) = some next := by
    change ExecutionCarrier.pairedTrajectory carrier _ _ _ (n + 1) = _
    rw [ExecutionCarrier.pairedTrajectory_succ carrier _ _ _ member time]
    change (carrier.pairedTrajectory valid n).bind _ = _
    rw [paired, Option.bind_some, step.replay]
  have noWords := source_wordsAt_nil_of_not_read witness constraints balanced event member
    (control_not_read event (HostCallLedger.input physical) _ sameEvent notRead)
  refine ⟨n, current, next, atIndex, paired, after, step, ?_, noWords⟩
  intro cell
  simp only [next, locContent, HostExecution.apply, HostEffect.applyMemory, noWrite]
  rfl

/-- Every installed SyscallInstrs occurrence supplies its complete timed execution facts.
Full-call balance selects and discharges control and hint cases internally, including actual
host returns and RAM effects; no handler or successful-dispatch premise is supplied. -/
theorem GroundingCarrier.syscall_engineFacts (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : SyscallInstrsChip.Inputs (ZMod p)}
    (member : ExecutionRow.syscall row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
        (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) (.syscall row)) ∧
      FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
        (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) (.syscall row)) := by
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have interface := source_interface (p := p) source.host.io.hints
  have calls := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  have byteBalance := (HostHintQueueBoundary.record_channels witness balanced).byte
  obtain ⟨physical, active, same⟩ := syscall_physical (HostHintQueueBoundary.projected witness) member
  have ledger := HostLocalHandoff.calls_perm_of_balancedChannel (HostHintQueueBoundary.projected witness)
    (resources_hostCall_silent interface) checks calls
  have callMem := ledger.mem_iff.mp (List.mem_map_of_mem (f := HostCallLedger.call) active)
  have dispatch := HostQueueCallProjection.calls_run_or_queue (HostHintQueueBoundary.projected witness)
    interface checks byteBalance _ callMem
  simp only [HostHintQueueBoundary.projected_data] at active dispatch
  rcases dispatch with queue | control
  · obtain ⟨queueRow, queueMem, sameCall⟩ := queue
    apply carrier.queue_engineFacts valid constraints balanced (.syscall row) member queueRow queueMem
    rw [same]
    exact (congrArg (fun message : HostCallChip.Message (ZMod p) => clkNat message.clk_high message.clk_low) sameCall).trans
      (HostQueueCPUOrder.call_time queueRow)
  · have sameEvent : ExecutionRow.syscall row = .syscall (HostCallLedger.input physical).instruction := congrArg _ same
    apply carrier.syscall_engineFacts_of_effects valid constraints balanced (.syscall row) member physical active sameEvent
    intro pull currency
    obtain ⟨n, current, next, atIndex, paired, after, step, unchanged, noWords⟩ :=
      control_step valid carrier constraints balanced (.syscall row) member physical active sameEvent control.1
        (fun host running context observed => control.2 host running _ rfl context observed) pull currency
    refine ⟨n, current, next, atIndex, paired, after, step, ?_, ?_⟩
    · intro word wordMem
      rw [noWords] at wordMem
      contradiction
    · intro cell _
      exact unchanged cell

end SP1Clean.Soundness.HostHintReadCPU
