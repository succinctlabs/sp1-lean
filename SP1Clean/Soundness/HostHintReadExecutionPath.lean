import SP1Clean.Model.Core.ExecutionWritePolicy
import SP1Clean.Model.Core.ExecutionCompatibility
import SP1Clean.Soundness.HostHintReadExecution

/-! # Local execution soundness for the installed instruction, control, and hint AIR

The constraints and balanced ledger reconstruct one finite path of normally retiring Sail
instructions and concrete host calls from the complete incoming state. Every active event occurs
exactly once, and final PC, clock, and physical Memory-frontier values agree with that path.
Empty segments remain identity paths; inactive padding contributes no execution steps.

This is the installed source-hint assembly's soundness theorem. Complete outgoing snapshot and
Exit-bus binding, WRITE/VERIFY handlers, and constructive completeness remain separate obligations.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding
open LeanRV64D.Defs (Register)

private theorem path_of_replay {policy : HostPolicy} {program : Target.GuestProgram}
    {source target : ExecutionState} {events : List Machine.ExecutionEvent}
    (success : replayEvents? policy program source events = some target)
    (sound : ∀ n current next event, events[n]? = some event →
      replayEvents? policy program source (events.take n) = some current →
      replayStep? policy program current event = some next →
        ExecutionStep policy program current event next) :
    ExecutionPath policy program source events target := by
  induction events generalizing source with
  | nil => cases success; exact .nil _
  | cons event rest ih =>
    obtain ⟨middle, step, suffix⟩ := Option.bind_eq_some_iff.mp success
    refine .cons (sound 0 source middle event rfl rfl step) (ih suffix ?_)
    intro n current next label atLabel prefixReplay replay
    apply sound (n + 1) current next label (by simpa only [List.getElem?_cons_succ] using atLabel) _ replay
    simpa only [List.take_succ_cons, replayEvents?, step, Option.bind_some] using prefixReplay

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance pathLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance pathLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

/-- The registered chip step, effect and permission at an actual replayed instruction occurrence. Incoming
truth and operand currency are supplied by the same installed grounding proof. -/
theorem GroundingCarrier.instruction_step_at (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {n : ℕ} {current : ExecutionState} {row : DecodedInstructionRow p}
    (atRow : carrier.ordered[n]? = some (.instruction row))
    (prefixReplay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize (carrier.events.take n) = some current) :
    ∃ next, ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current .ordinary next ∧
      Target.RowEffect (image.toGuestProgram valid) (row.toChipRow witness.data).view current.sail next.sail ∧
      InstructionWrite.PermittedAt image.readOnly (image.toGuestProgram valid) current.sail := by
  have member := carrier.exhaustive.mem_iff.mp (List.mem_of_getElem? atRow)
  have grounded := (carrier.ground valid constraints balanced).1 _ member
  have time := carrier.time_of_ordered_at atRow
  rw [(eventFacts_state_fetch _ _ _).1] at time
  have currency : ∀ mp ∈ (row.ordinaryRowFacts witness.data).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
        LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline
          (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
    intro mp mem
    apply grounded.2 mp
    exact List.mem_append_left _ mem
  exact carrier.instruction_step_effect valid constraints balanced member grounded.1 currency prefixReplay time

/-- The registered chip effect at an actual replayed instruction occurrence. All incoming
truth and operand currency are supplied by the same installed grounding proof. -/
theorem GroundingCarrier.instruction_effect_at (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {n : ℕ} {current next : ExecutionState} {row : DecodedInstructionRow p}
    (atRow : carrier.ordered[n]? = some (.instruction row))
    (prefixReplay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize (carrier.events.take n) = some current)
    (replay : replayStep? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      current .ordinary = some next) :
    ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current .ordinary next ∧
      Target.RowEffect (image.toGuestProgram valid) (row.toChipRow witness.data).view current.sail next.sail := by
  obtain ⟨target, step, effect, _⟩ := carrier.instruction_step_at valid constraints balanced atRow prefixReplay
  have same : target = next := Option.some.inj (step.replay.symm.trans replay)
  subst target
  exact ⟨step, effect⟩

/-- The actual installed AIR enforces the public ordinary write policy at every replayed prefix.
No permission, decoded-operand, or grounding premise is required from the caller. -/
theorem GroundingCarrier.writesPermitted (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ExecutionPath.WritesPermitted ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events := by
  intro n current atEvent prefixReplay
  simp only [ExecutionCarrier.events, List.getElem?_map] at atEvent
  obtain ⟨row, atRow, event⟩ := Option.map_eq_some_iff.mp atEvent
  cases row with
  | instruction row =>
    obtain ⟨_, _, _, permitted⟩ := carrier.instruction_step_at valid constraints balanced atRow prefixReplay
    exact permitted
  | syscall row | halt row => cases event

private theorem step_of_replay (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (n : ℕ) (current next : ExecutionState) (event : Machine.ExecutionEvent)
    (atEvent : carrier.events[n]? = some event)
    (prefixReplay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize (carrier.events.take n) = some current)
    (replay : replayStep? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      current event = some next) :
    ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event next ∧
      (∀ address, 2 ^ 48 ≤ address → next.sail.mem.get? address = current.sail.mem.get? address) ∧
      (next.sail.cycleCount = current.sail.cycleCount ∧ next.sail.sailOutput = current.sail.sailOutput) ∧
      ∀ R : Register, R ≠ Register.PC → R ≠ Register.nextPC → R ≠ Register.minstret →
        R ≠ Register.minstret_increment → (∀ index : BitVec 5, R ≠ reg_idx_to_Register index) →
          next.sail.regs.get? R = current.sail.regs.get? R := by
  simp only [ExecutionCarrier.events, List.getElem?_map] at atEvent
  obtain ⟨row, atRow, rfl⟩ := Option.map_eq_some_iff.mp atEvent
  have member := carrier.exhaustive.mem_iff.mp (List.mem_of_getElem? atRow)
  cases row with
  | instruction row =>
    obtain ⟨step, effect⟩ := carrier.instruction_effect_at valid constraints balanced atRow prefixReplay replay
    refine ⟨step, ?_, effect.runtime, effect.otherRegs⟩
    have active : row ∈ LocalCore.instructionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) ∧
        (row.toChipRow (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data).is_real = 1 := by
      simpa [LocalCore.executionRows, LocalCore.activeInstructionRows] using member
    have authorization := HostLocalCore.instructionRows_write_authorized (HostHintQueueBoundary.projected witness)
      (auxiliary_permission_pulls (HostQueueCurrent.source_permission_pulls source))
      (HostHintQueueBoundary.projected_constraints witness constraints)
      (HostHintQueueBoundary.projected_permission_balancedChannel witness balanced) active.1 active.2
    rw [row.toChipRow_setData (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data]
      at authorization
    exact effect.memory_outside_of_writeAuthorization valid authorization
  | syscall row | halt row =>
    have step := (replayHost?_eq_some_iff _ _ _ _ _).mp replay
    refine ⟨step, ?_⟩
    cases step with
    | syscall success =>
      obtain ⟨pc, execution, _, _, ran, _, sail, _⟩ := HostState.step_observations success
      refine ⟨?_, ?_, ?_⟩
      · intro address outside
        rw [sail]
        exact HostExecution.preserves_memory_outside ran pc address (Or.inr outside)
      · rw [sail]
        exact ⟨rfl, rfl⟩
      · intro R notPc _ _ _ notGpr
        rw [sail]
        exact execution.other_register_frame current.sail pc R notPc (notGpr 5)

private theorem final_replay (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (truth : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (finalBoundaryStateMessage witness.publicInput)) :
    ∃ target, carrier.pairedTrajectory valid carrier.events.length = some target ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) := by
  obtain ⟨n, state, present, time, pc, _, _⟩ := truth
  have atEnd : n = carrier.rows.length := start_injective carrier.timeline (time.symm.trans carrier.finalClock.symm)
  change (carrier.pairedTrajectory valid n).map ExecutionState.sail = some state at present
  rw [atEnd, ← carrier.events_length] at present
  obtain ⟨target, paired, sail⟩ := Option.map_eq_some_iff.mp present
  refine ⟨target, paired, ?_, ?_⟩
  · have clock := replayEvents?_clock paired
    rw [List.take_length] at clock
    have timeline := congrArg (fun tl : Timeline => tl.start carrier.events.length)
      (carrier.timeline_events constraints balanced)
    rw [eventTimeline_start_le _ _ _ le_rfl, List.take_length, carrier.events_length, carrier.finalClock] at timeline
    exact clock.trans timeline.symm
  · rwa [sail]

/-- Raw installed AIR constraints and balance yield a normally retiring local execution on the
derived complete event tape. Its endpoint agrees with the public PC/clock and every final record. -/
theorem GroundingCarrier.execution (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ target, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize carrier.events target ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      ∀ loc message, LocalCore.memoryFinalFrontier
          (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = some message →
        locContent target.sail loc = some (Word.toBitVec64 message.value) := by
  have grounded := carrier.ground valid constraints balanced
  obtain ⟨target, present, clock, pc⟩ := final_replay valid carrier constraints balanced grounded.2.1
  have replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target := by
    simpa only [GroundingCarrier.pairedTrajectory, ExecutionCarrier.pairedTrajectory,
      executionTrajectory, List.take_length] using present
  refine ⟨target, path_of_replay replay (fun n current next event atEvent prefixReplay replay =>
    (step_of_replay valid carrier constraints balanced n current next event atEvent prefixReplay replay).1), clock, pc, ?_⟩
  intro loc message finalRecord
  have value := grounded.2.2 loc message finalRecord
  have before : carrier.trajectory valid carrier.events.length = some target.sail := by
    simp only [GroundingCarrier.trajectory, present, Option.map_some]
  rw [← carrier.finalClock, ← carrier.events_length] at value
  exact (localValueAtG_stepStart_iff before).mp value

/-- The same actual replay preserves the full Sail memory map outside the native address range. -/
theorem GroundingCarrier.memory_outside (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {target : ExecutionState}
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target) (address : ℕ) (outside : 2 ^ 48 ≤ address) :
    target.sail.mem.get? address = source.sail.realize.mem.get? address := by
  exact replayEvents?_preserves (fun state => state.sail.mem.get? address) replay
    (fun n current next event atEvent prefixReplay replay =>
      (step_of_replay valid carrier constraints balanced n current next event atEvent prefixReplay replay).2.1 address outside)

/-- Native instruction and host steps preserve Sail's simulator counter and output exactly. -/
theorem GroundingCarrier.runtime (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {target : ExecutionState}
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target) :
    target.sail.cycleCount = source.sail.cycleCount ∧ target.sail.sailOutput = source.sail.output := by
  have same := replayEvents?_preserves (fun state => (state.sail.cycleCount, state.sail.sailOutput)) replay
    (fun n current next event atEvent prefixReplay replay => Prod.ext
      (step_of_replay valid carrier constraints balanced n current next event atEvent prefixReplay replay).2.2.1.1
      (step_of_replay valid carrier constraints balanced n current next event atEvent prefixReplay replay).2.2.1.2)
  exact Prod.mk.inj same

/-- Every Sail register outside the GPR/PC/retirement footprint retains its complete source observation. -/
theorem GroundingCarrier.other_registers (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {target : ExecutionState}
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target)
    (R : Register) (notPc : R ≠ Register.PC) (notNext : R ≠ Register.nextPC)
    (notRetired : R ≠ Register.minstret) (notIncrement : R ≠ Register.minstret_increment)
    (notGpr : ∀ index : BitVec 5, R ≠ reg_idx_to_Register index) :
    target.sail.regs.get? R = source.sail.registers.get? R := by
  exact replayEvents?_preserves (fun state => state.sail.regs.get? R) replay
    (fun n current next event atEvent prefixReplay replay =>
      (step_of_replay valid carrier constraints balanced n current next event atEvent prefixReplay replay).2.2.2
        R notPc notNext notRetired notIncrement notGpr)

/-- The installed ensemble proves a local RISC-V/host path without caller-supplied ordering,
grounding, or event semantics. The path exhausts the active physical inventory, preserving repeated
occurrences and erasing inactive padding. Complete outgoing snapshot binding is not asserted. -/
theorem source_execution (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ events target, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events target ∧
      ExecutionPath.WritesPermitted ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events ∧
      events.Perm ((LocalCore.executionRows
        (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map ExecutionRow.event) ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      ∀ loc message, LocalCore.memoryFinalFrontier
          (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = some message →
        locContent target.sail loc = some (Word.toBitVec64 message.value) := by
  obtain ⟨carrier⟩ := source_grounding_carrier valid witness constraints balanced
  obtain ⟨target, path, endpoint⟩ := carrier.execution valid constraints balanced
  exact ⟨carrier.events, target, path, carrier.writesPermitted valid constraints balanced, carrier.exhaustive.map ExecutionRow.event, endpoint⟩

/-- The installed ordinary/HALT fragment supplies the legacy trace from its complete stateful
path, using one fixed handler for the whole trace. All endpoint and inventory conclusions of
`source_execution` are retained. General mixed callers keep the complete paired replay. -/
theorem source_execution_ordinaryHalt (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (fragment : ∀ event ∈ (LocalCore.executionRows
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map ExecutionRow.event,
        OrdinaryOrHalt event) (handler : Machine.ExecutableSyscallHandler) :
    ∃ (target : ExecutionState) (trace : Machine.EventExecutionTrace),
      ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize trace.events target ∧
      ExecutionPath.WritesPermitted ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize trace.events ∧
      Machine.traceOfEvents? handler.withHalt (image.toGuestProgram valid) source.sail.realize trace.events =
        some trace ∧
      trace.Valid handler.withHalt.relation (image.toGuestProgram valid) ∧ trace.Clocked source.clock ∧
      trace.initialState = source.sail.realize ∧ trace.finalState = target.sail ∧
      trace.events.Perm ((LocalCore.executionRows
        (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map ExecutionRow.event) ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      ∀ loc message, LocalCore.memoryFinalFrontier
          (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = some message →
        locContent target.sail loc = some (Word.toBitVec64 message.value) := by
  obtain ⟨events, target, path, permitted, inventory, endpoint⟩ :=
    source_execution valid witness constraints balanced
  obtain ⟨trace, replay, legacy, clocked, initial, tape, final, _⟩ := path.ordinaryHalt_trace
    (fun event member => fragment event (inventory.mem_iff.mp member)) handler
  rw [← tape] at path permitted inventory replay
  exact ⟨target, trace, path, permitted, replay, legacy, clocked, initial, final, inventory, endpoint⟩

end SP1Clean.Soundness.HostHintReadCPU
