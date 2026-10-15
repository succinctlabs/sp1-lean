import SP1Clean.Soundness.HostHintReadInstructionExecution
import SP1Clean.Soundness.HostHintReadSyscallExecution
import SP1Clean.Soundness.LocalCoreHaltExecution

/-! # Closed grounding for the installed instruction, control, and hint assembly

Ordinary, SyscallInstrs, and legacy HALT rows all use the same paired Sail/host replay and the
complete physical Memory ledger. Source genesis, every event step/frame fact, and final frontier
currency follow from constraints and balance. No event-semantic premise remains. This is the
grounding stage: `HostHintReadExecutionPath` derives the installed assembly's local execution
soundness. Complete outgoing snapshot authentication, the full eight-call compiler, and the final
local-execution equivalence remain separate capstone obligations.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance executionLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance executionLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

private theorem source_ordering
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    LocalCore.OrderingChannels (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) :=
  HostHintQueueBoundary.projected_orderingChannels witness (source_interface source.host.io.hints) constraints balanced

private theorem halt_facts (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)}
    (member : ExecutionRow.halt row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) :
    (Word.toBitVec64 row.x5_memory.prev_value = 0 ∧
      (row.x10_memory.prev_value[1] = 0 ∧ row.x10_memory.prev_value[2] = 0 ∧ row.x10_memory.prev_value[3] = 0) ∧
      (((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ row.state.clk_16_24.val < 2 ^ 8)) ∧
      (image.toGuestProgram valid).fetchWord (StateMsg.pcBits (HaltChip.statePulledMessage row)) = some Target.ECALL_ENC := by
  have checked := HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints witness constraints)
  have ordering := source_ordering witness constraints balanced
  refine ⟨LocalCore.haltRows_staticFacts_of_byte _ checked ordering.byte member, ?_⟩
  have programBalance : (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).BalancedChannel
      programChannel.toRaw := by
    change BalancedInteractions ((HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).interactionsWith _)
    rw [HostLocalCore.localWitness_program _ (source_program_silent source)]
    exact HostHintQueueBoundary.projected_core_balancedChannel witness balanced _
      (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
  exact ((LocalCore.halt_program_committed_of_balance valid _ checked programBalance member).ecall_of_opcode rfl).1

private theorem trajectory_halt (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)}
    (member : ExecutionRow.halt row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (haltRowFacts row).statePull)
    (currency : ∀ mp ∈ (haltRowFacts row).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (n : ℕ) (time : StateMsg.timeNat (HaltChip.statePulledMessage row) = carrier.timeline.start n) :
    carrier.trajectory valid (n + 1) = (carrier.trajectory valid n).map
      (fun state => { state with regs := state.regs.insert LeanRV64D.Defs.Register.PC Machine.haltPc }) := by
  obtain ⟨m, state, present, atTime, pc, rom, _⟩ := pull
  have same : m = n := start_injective carrier.timeline (atTime.symm.trans time)
  subst m
  change (carrier.pairedTrajectory valid n).map ExecutionState.sail = some state at present
  obtain ⟨whole, paired, sail⟩ := Option.map_eq_some_iff.mp present
  have before : carrier.trajectory valid n = some whole.sail := by
    simp only [GroundingCarrier.trajectory, paired, Option.map_some]
  have atPc : whole.sail.regs.get? LeanRV64D.Defs.Register.PC =
      some (StateMsg.pcBits (HaltChip.statePulledMessage row)) := by rwa [sail]
  have facts := halt_facts valid witness constraints balanced member
  have running := carrier.pairedTrajectory_running_of_fetch valid constraints balanced member paired atPc facts.2
  have atIndex := ExecutionCarrier.ordered_at carrier member time
  have covered : n ≤ carrier.events.length := by
    have bound := (List.getElem?_eq_some_iff.mp atIndex).1
    simpa only [ExecutionCarrier.events, List.length_map] using Nat.le_of_lt bound
  have currentTime : whole.clock = carrier.timeline.start n := by
    rw [carrier.timeline_events constraints balanced, eventTimeline_start_le _ _ _ covered]
    exact replayEvents?_clock paired
  have step := HaltChip.executionStep_of_currency row ⟨{ readOnly := image.readOnly }, p⟩ rfl _ whole
    facts.1.1 facts.1.2.1 running (currentTime.trans time.symm) atPc facts.2
    (by rwa [sail]) before time currency
  change (ExecutionCarrier.pairedTrajectory carrier _ _ _ (n + 1)).map ExecutionState.sail = _
  rw [ExecutionCarrier.pairedTrajectory_succ carrier _ _ _ member time]
  change ((carrier.pairedTrajectory valid n).bind _).map ExecutionState.sail = _
  rw [paired, Option.bind_some]
  rw [show (ExecutionRow.halt row).event = .syscall (haltEventOfRow row) from rfl, step.replay]
  simp only [GroundingCarrier.trajectory, paired, Option.map_some]

/-- The retained legacy HALT table also executes on the complete carrier. Its existing
16-bit exit restriction follows from its own assertions; no stronger HALT domain is claimed. -/
theorem GroundingCarrier.halt_engineFacts (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)}
    (member : ExecutionRow.halt row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
        (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) (.halt row)) ∧
      FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
        (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) (.halt row)) := by
  have noWords := source_wordsAt_nil_of_not_read witness constraints balanced (.halt row) member
    (fun _ impossible => by cases impossible)
  simp only [eventFacts, noWords, List.map_nil, List.append_nil]
  change LocalStepFactG _ _ _ _ (haltRowFacts row) ∧ FrameFactG _ _ _ _ (haltRowFacts row)
  exact halt_engineFactsG_of_currencyStep row (halt_facts valid witness constraints balanced member).1.2.2 _ _ _ _
    (fun n time => ExecutionCarrier.originalTimeStep carrier member n time)
    (trajectory_halt valid carrier constraints balanced member)

/-- Raw constraints and balance now discharge every event's timed grounding obligations.
The result authenticates all operand values and the final State/Memory frontier on actual
paired replay, including empty local segments. Complete outgoing snapshot binding is separate. -/
theorem GroundingCarrier.ground (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (∀ event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)),
      LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline (event.facts witness.data).statePull ∧
      ∀ pull ∈ (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).memPulls,
        MemoryMsg.isU64 pull.1 ∧ MemoryMsg.ClkBound pull.1 ∧
          LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf pull.1) pull.2 pull.1.value) ∧
      LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
        (finalBoundaryStateMessage witness.publicInput) ∧
      (∀ loc message, LocalCore.memoryFinalFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = some message →
        LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline loc
          (StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput)) message.value) := by
  apply carrier.ground_of_steps valid constraints balanced _ (carrier.trajectory_zero valid)
  intro event member
  cases event with
  | instruction row => exact carrier.instruction_engineFacts valid constraints balanced member
  | syscall row => exact carrier.syscall_engineFacts valid constraints balanced member
  | halt row => exact carrier.halt_engineFacts valid constraints balanced member

end SP1Clean.Soundness.HostHintReadCPU
