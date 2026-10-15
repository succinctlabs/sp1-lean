import SP1Clean.Soundness.InstructionWritePolicy
import SP1Clean.Soundness.HostHintReadTrajectory
import SP1Clean.Soundness.HostLocalCoreRom
import SP1Clean.Soundness.CoreInstructionExecution

/-! # Ordinary execution on the complete instruction and hint carrier

Every ordinary instruction retains its original footprint: authenticated hint ownership excludes
added RAM rows at its clock. Byte and Program guarantees supply the registered chip contracts,
and the extended permission ledger protects ROM. The resulting step/frame facts use the same
paired Sail/host replay as the hint handlers, with all instruction cases internal to the registry.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance instructionLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance instructionLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

private theorem instruction_staticInputs
    (witness : EnsembleWitness (LocalCore.ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (byte : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (program : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data programChannel.toRaw)
    {row : DecodedInstructionRow p} (member : row ∈ LocalCore.instructionRows witness) :
    DecodedRowStaticInputs row witness.data :=
  ⟨mem_chip_of_mem_decodeInstructionTables member,
    LocalCore.instructionRows_constraints witness constraints row member,
    channelGuarantees_of_mem_decodeInstructionTables witness.data _ (LocalCore.instructionTables_aligned witness)
      (fun table tableMem => byte table (LocalCore.instructionTables_mem witness tableMem)) row member,
    channelGuarantees_of_mem_decodeInstructionTables witness.data _ (LocalCore.instructionTables_aligned witness)
      (fun table tableMem => program table (LocalCore.instructionTables_mem witness tableMem)) row member⟩

private theorem instruction_inputs (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) :
    DecodedRowStaticInputs row witness.data ∧
      Target.decodedInROM (image.toGuestProgram valid) (programAccess (row.toChipRow witness.data).view).toRow := by
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have checked := HostLocalCore.localWitness_constraints _ checks
  have ordering := HostHintQueueBoundary.projected_orderingChannels witness
    (source_interface source.host.io.hints) constraints balanced
  have active : row ∈ LocalCore.instructionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) ∧
      (row.toChipRow (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data).is_real = 1 := by
    simpa [LocalCore.executionRows, LocalCore.activeInstructionRows] using member
  have programBalance : (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).BalancedChannel
      programChannel.toRaw := by
    change BalancedInteractions ((HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).interactionsWith _)
    rw [HostLocalCore.localWitness_program _ (source_program_silent source)]
    exact HostHintQueueBoundary.projected_core_balancedChannel witness balanced _
      (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
  have program := LocalCore.program_guarantees_of_balance image source _ checked programBalance
  have inputs := (instruction_staticInputs _ checked ordering.byte program.2 active.1).setData witness.data
  have committed := LocalCore.instructionRows_program_committed_of_balance valid _ checked programBalance active.1 active.2
  rw [row.toChipRow_setData (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data] at committed active
  refine ⟨inputs, ?_⟩
  exact committed.decoded_of_opcode_ne
    (supportedChip_fetchDiscriminantShape row.chip inputs.registered witness.data row.physical
      inputs.constraints inputs.byte active.2)

private theorem trajectory_ordinary (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (decoded : Target.decodedInROM (image.toGuestProgram valid) (programAccess (row.toChipRow witness.data).view).toRow)
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (row.ordinaryRowFacts witness.data).statePull)
    (n : ℕ) (time : StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull = carrier.timeline.start n) :
    carrier.trajectory valid (n + 1) = (carrier.trajectory valid n).bind Machine.stepOnce := by
  obtain ⟨m, state, present, atIndex, pc, _, configured⟩ := pull
  have same : m = n := start_injective carrier.timeline (atIndex.symm.trans time)
  subst m
  change (carrier.pairedTrajectory valid n).map ExecutionState.sail = some state at present
  obtain ⟨whole, paired, sail⟩ := Option.map_eq_some_iff.mp present
  have atPc : whole.sail.regs.get? LeanRV64D.Defs.Register.PC =
      some (Target.pcBitsOfRow (programAccess (row.toChipRow witness.data).view).toRow) := by
    rw [sail, program_pc_eq_statePull]
    exact pc
  have notEcall := decoded.notEcall (by rwa [sail]) atPc
  obtain ⟨_, _, fetched, _, _⟩ := decoded
  have running := carrier.pairedTrajectory_running_of_fetch valid constraints balanced member paired atPc fetched
  change (ExecutionCarrier.pairedTrajectory carrier _ _ _ (n + 1)).map ExecutionState.sail = _
  rw [ExecutionCarrier.pairedTrajectory_succ carrier _ _ _ member time]
  change ((carrier.pairedTrajectory valid n).bind _).map ExecutionState.sail = _
  rw [paired, Option.bind_some]
  change (replayStep? _ (image.toGuestProgram valid) whole .ordinary).map ExecutionState.sail = _
  rw [replayStep?_ordinary_sail _ _ _ running notEcall]
  simp only [GroundingCarrier.trajectory, paired, Option.map_some, Option.bind_some]

/-- All 25 ordinary instruction families supply complete step/frame facts on the same carrier
as the hint handlers. ROM preservation and absence of added hint accesses follow from the AIR. -/
theorem GroundingCarrier.instruction_engineFacts (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
        (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) (.instruction row)) ∧
      FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
        (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) (.instruction row)) := by
  have noWords := source_wordsAt_nil_of_not_read witness constraints balanced (.instruction row) member
    (fun _ impossible => by cases impossible)
  simp only [eventFacts, noWords, List.map_nil, List.append_nil]
  change LocalStepFactG _ _ _ _ (row.ordinaryRowFacts witness.data) ∧
    FrameFactG _ _ _ _ (row.ordinaryRowFacts witness.data)
  have checked := instruction_inputs valid witness constraints balanced member
  have contracts := supportedChip_groundingContracts row.chip checked.1.registered
  have active : row ∈ LocalCore.instructionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) ∧
      (row.toChipRow (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data).is_real = 1 := by
    simpa [LocalCore.executionRows, LocalCore.activeInstructionRows] using member
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have permissions := HostHintQueueBoundary.projected_permission_balancedChannel witness balanced
  have permission := HostLocalCore.instructionRows_write_permitted (HostHintQueueBoundary.projected witness)
    (auxiliary_permission_pulls (HostQueueCurrent.source_permission_pulls source)) checks permissions active.1 active.2
  rw [row.toChipRow_setData (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data] at permission active
  apply contracts.engineFactsLocalG_of_rowEffect witness.data row rfl checked.1 active.2 _ checked.2
    (carrier.trajectory valid) source.sail.realize carrier.timeline
    (fun _ effect loaded => effect.romLoaded_of_writePermission valid permission loaded)
  · intro n time
    have successor := ExecutionCarrier.originalTimeStep carrier member n time
    have ordering := HostHintQueueBoundary.projected_orderingChannels witness
      (source_interface source.host.io.hints) constraints balanced
    have duration := (LocalCore.executionRows_advancing_of_orderingChannels _
      (HostLocalCore.localWitness_constraints _ checks) ordering member).2
    rw [ExecutionRow.edge_setData (.instruction row)
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data,
      ExecutionRow.edge_eq_facts] at duration
    change StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePush =
      StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull + 8 at duration
    change StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePush = carrier.timeline.start (n + 1) at successor
    exact successor.symm.trans (duration.trans (congrArg (fun clock => clock + 8) time))
  · exact trajectory_ordinary valid carrier constraints balanced member checked.2

/-- Grounded ordinary operands yield a normally retiring semantic step from the actual paired
state, with write permission from the installed AIR. Instruction dispatch and readiness stay
inside the registered chip contracts. -/
theorem GroundingCarrier.instruction_step_effect (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (row.ordinaryRowFacts witness.data).statePull)
    (currency : ∀ mp ∈ (row.ordinaryRowFacts witness.data).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
        LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline
          (MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    {n : ℕ} {current : ExecutionState}
    (present : carrier.pairedTrajectory valid n = some current)
    (time : StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull = carrier.timeline.start n) :
    ∃ next, ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      current .ordinary next ∧
      Target.RowEffect (image.toGuestProgram valid) (row.toChipRow witness.data).view current.sail next.sail ∧
      InstructionWrite.PermittedAt image.readOnly (image.toGuestProgram valid) current.sail := by
  have checked := instruction_inputs valid witness constraints balanced member
  have contracts := supportedChip_groundingContracts row.chip checked.1.registered
  have active : row ∈ LocalCore.instructionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) ∧
      (row.toChipRow (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data).is_real = 1 := by
    simpa [LocalCore.executionRows, LocalCore.activeInstructionRows] using member
  have permission := HostLocalCore.instructionRows_write_permitted (HostHintQueueBoundary.projected witness)
    (auxiliary_permission_pulls (HostQueueCurrent.source_permission_pulls source))
    (HostHintQueueBoundary.projected_constraints witness constraints)
    (HostHintQueueBoundary.projected_permission_balancedChannel witness balanced) active.1 active.2
  rw [row.toChipRow_setData (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data] at permission active
  have guard := contracts.routingLocal witness.data row rfl checked.1.constraints active.2 _ checked.2
  have migrated : (row.toChipRow witness.data).kind.advance.isSome = true := contracts.migrated
  have memory := row.memoryChannelGuarantees_of_pullCurrency witness.data
    (fun mp hmp => ⟨(currency mp hmp).1, (currency mp hmp).2.1⟩)
  have inputs : DecodedRowOpenSoundnessInputs row witness.data :=
    ⟨contracts.assumptionsLocal witness.data row rfl checked.1 active.2 _ checked.2 memory, memory⟩
  have wiring := contracts.wiringLocal witness.data row rfl checked.1 active.2 _ checked.2 inputs
  have ready := contracts.readinessLocal witness.data row rfl checked.1 active.2 guard _ checked.2 inputs
  obtain ⟨m, state, statePresent, atTime, pc, rom, configured⟩ := pull
  have same : m = n := start_injective carrier.timeline (atTime.symm.trans time)
  subst m
  have before : carrier.trajectory valid n = some current.sail := by
    simp only [GroundingCarrier.trajectory, present, Option.map_some]
  have sameState : state = current.sail := Option.some.inj (statePresent.symm.trans before)
  rw [sameState] at pc rom configured
  change current.sail.regs.get? LeanRV64D.Defs.Register.PC =
    some (StateMsg.pcBits (row.ordinaryRowFacts witness.data).statePull) at pc
  obtain ⟨next, _, effect⟩ := wiring.advance_atG (ChipKind.advancePayload_of_migrated migrated)
    active.2 (checked.1.chipSpec inputs) checked.2 ready before time pc rom configured
    (fun mp hmp => ⟨(currency mp hmp).1, (currency mp hmp).2.2⟩)
  have atPc : current.sail.regs.get? LeanRV64D.Defs.Register.PC =
      some (Target.pcBitsOfRow (programAccess (row.toChipRow witness.data).view).toRow) := by
    rw [program_pc_eq_statePull]
    exact pc
  have operands := wiring.valueOperandsBound_of_pullCurrencyG
    (fun mp hmp => (currency mp hmp).2.2) before time
  have sourceA := wiring.sourceAValueBound_of_pullCurrencyG
    (fun mp hmp => (currency mp hmp).2.2) before time
  have pulls := wiring.memoryPullsBound_of_pullCurrencyG
    (fun mp hmp => (currency mp hmp).2.2) before time
  have permitted := row.write_permittedAt checked.1.registered witness.data _ current.sail
    active.2 (checked.1.chipSpec inputs) (ready current.sail operands sourceA pulls)
    atPc operands checked.2 permission
  have notEcall := checked.2.notEcall configured atPc
  obtain ⟨_, _, fetched, _, _⟩ := checked.2
  have running := carrier.pairedTrajectory_running_of_fetch valid constraints balanced member present atPc fetched
  exact ⟨⟨next, current.host, current.clock + Machine.ordinarySchedule.duration⟩,
    .ordinary running notEcall effect.normal, effect, permitted⟩

/-- Projection to normal retirement keeps the original instruction-step interface. -/
theorem GroundingCarrier.instruction_step (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (row.ordinaryRowFacts witness.data).statePull)
    (currency : ∀ mp ∈ (row.ordinaryRowFacts witness.data).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
        LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline
          (MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    {n : ℕ} {current : ExecutionState}
    (present : carrier.pairedTrajectory valid n = some current)
    (time : StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull = carrier.timeline.start n) :
    ∃ next, ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      current .ordinary next := by
  obtain ⟨next, step, _⟩ := carrier.instruction_step_effect valid constraints balanced member pull currency present time
  exact ⟨next, step⟩

end SP1Clean.Soundness.HostHintReadCPU
