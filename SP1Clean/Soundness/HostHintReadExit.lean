import SP1Clean.Soundness.HostHintReadHostAgreement
import SP1Clean.Soundness.LocalCoreExit

/-! # Public Exit values on the installed complete execution

The host auxiliaries are Exit-silent, so the complete installed ledger preserves the original
local Exit accounting even though its Memory ledger cannot be projected. A genuine terminal
HALT therefore binds the public field to the concrete host's canonical 32-bit exit. Running and
HALT-zero remain distinct in the path. `HostHintReadTerminalAgreement` connects the separate
terminal receipt's supplied optional status to this same execution.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance exitLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance exitLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

private theorem source_exit_silent :
    ∀ component ∈ (HostHintReadHandoff.receiver (p := p) :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ sourceResources source.host.io.hints),
      exitChannel.toRaw ∉ component.circuit.channels := by
  have checked : ((HostHintReadHandoff.receiver (p := p) :: HostCallReceivers.available).map
      (fun view : HostLocalHandoff.Receiver (p := p) => view.component) ++
      (HostHintReadHandoff.wordResources ++ sourceResources source.host.io.hints)).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains
        (exitChannel (p := p)).toRaw.name) = true := rfl
  intro component member used
  have silent := List.all_eq_true.mp checked component member
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at silent
  contradiction

/-- Exit balance projects from the full installed witness, independently of Memory balance. -/
theorem source_exit_balance
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (balanced : witness.BalancedChannels) :
    (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).BalancedChannel exitChannel.toRaw := by
  change BalancedInteractions ((HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).interactionsWith _)
  rw [HostLocalCore.localWitness_other _ exitChannel.toRaw
    (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
    (by simp [exitChannel, byteChannel, Channel.toRaw])
    (by simp [exitChannel, memoryChannel, Channel.toRaw])
    (by simp [exitChannel, HostCallChip.channel, Channel.toRaw])
    (by simp [exitChannel, WritePermissionProvider.channel, Channel.toRaw]) source_exit_silent]
  exact HostHintQueueBoundary.projected_core_balancedChannel witness balanced _
    (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])

omit [Fact (2 ^ 25 < p)] in
private theorem word_reduction (word : Word (ZMod p)) (small : Word.isU64 word) :
    word[0] + (word[1] + (word[2] + word[3] * 65536) * 65536) * 65536 =
      ((Word.toBitVec64 word).toNat : ZMod p) := by
  rw [Word.toBitVec64_toNat small]
  simp only [Word.toNat, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_pow, Nat.cast_ofNat]
  ring

private theorem halt_selector (row : SyscallInstrsChip.Inputs (ZMod p))
    (spec : SyscallInstrsChip.Spec row) (real : row.is_real = 1)
    (zero : (syscallEventOfRow row).rawCode = 0) : row.is_halt = 1 := by
  have selectors := spec.selectorsValid
  have id : (syscallEventOfRow row).syscallId = 0 := by
    simp only [Machine.CoreSyscallEvent.syscallId, zero]
    rfl
  have field : SyscallInstrsChip.syscallId row = ((SyscallInstrsChip.haltCode : ℕ) : ZMod p) :=
    (syscallId_field_iff row selectors real (by decide : 0 < 256)).mp id
  have selected : row.is_halt_zero.result = 1 := by
    rw [(selectors.2.1 real).1, if_pos field]
  rw [selectors.2.2.2.1, selected, real, one_mul]

private theorem GroundingCarrier.halt_field (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {call : Machine.CoreSyscallEvent} (member : .syscall call ∈ carrier.events)
    (zero : call.rawCode = 0) : (call.arg1.toNat : ZMod p) = witness.publicInput.exit_code := by
  obtain ⟨event, eventMem, same⟩ := List.mem_map.mp member
  have actual := carrier.exhaustive.mem_iff.mp eventMem
  have incoming := (carrier.ground valid constraints balanced).1 event actual
  have original : ∀ mp ∈ (event.facts witness.data).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 := by
    intro mp present
    have current := incoming.2 mp (List.mem_append_left _ present)
    exact ⟨current.1, current.2.1⟩
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have checked := HostLocalCore.localWitness_constraints _ checks
  have exitBalance := source_exit_balance witness balanced
  cases event with
  | instruction row => contradiction
  | halt row =>
    cases Machine.ExecutionEvent.syscall.inj same
    have active : row ∈ activeSystemRows
        (LocalCore.systemTable (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) 2)
        (haltRow (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data) (·.is_real) := by simpa [LocalCore.executionRows] using actual
    have small : Word.isU64 row.x10_memory.prev_value := (original (HaltChip.memPulledMessage row row.x10_memory 10,
      StateMsg.timeNat (HaltChip.statePulledMessage row))
      (by simp [ExecutionRow.facts, haltRowFacts, HaltChip.memoryPairs])).1
    have emitted := LocalCore.halt_exit_code _ checked exitBalance active
    rw [HaltChip.exitMessage, word_reduction _ small] at emitted
    rw [HostLocalCore.localWitness_publicInput, HostHintQueueBoundary.projected_publicInput] at emitted
    exact emitted
  | syscall row =>
    cases Machine.ExecutionEvent.syscall.inj same
    have active : row ∈ activeSystemRows
        (LocalCore.systemTable (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) 3)
        (syscallInstrsRow (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data) (·.is_real) := by simpa [LocalCore.executionRows] using actual
    obtain ⟨physical, physicalMem, rowEq, real⟩ := activeSystemRows_member _ _ _ active
    have interface := source_interface (p := p) source.host.io.hints
    have ordering := HostHintQueueBoundary.projected_orderingChannels witness interface constraints balanced
    have programBalance : (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).BalancedChannel
        programChannel.toRaw := by
      change BalancedInteractions
        ((HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).interactionsWith programChannel.toRaw)
      rw [HostLocalCore.localWitness_program _ (source_program_silent source)]
      exact HostHintQueueBoundary.projected_core_balancedChannel witness balanced _
        (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
    have program := LocalCore.program_guarantees_of_balance image source _ checked programBalance
    have contract := syscallInstrsRow_contract_of_component _
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data (LocalCore.systemTable_component _ 3)
      (LocalCore.systemTable_constraints _ checked 3)
      (ordering.byte _ (LocalCore.systemTable_mem _ 3))
      (program.2 _ (LocalCore.systemTable_mem _ 3)) physicalMem (by rwa [rowEq])
    rw [rowEq] at contract
    have selected := halt_selector row contract.1 real zero
    have small : Word.isU64 row.op_b_memory.prev_value :=
      (syscallRowFacts_currency_split row original).2.1.1
    have emitted := LocalCore.syscall_exit_code _ checked exitBalance active selected
    rw [SyscallInstrsChip.exitMessage, word_reduction _ small] at emitted
    rw [HostLocalCore.localWitness_publicInput, HostHintQueueBoundary.projected_publicInput] at emitted
    exact emitted

private theorem halt_bounds {policy : HostPolicy} {program : Target.GuestProgram}
    {before after : ExecutionState} {call : Machine.CoreSyscallEvent}
    (step : ExecutionStep policy program before (.syscall call) after) (zero : call.rawCode = 0) :
    call.arg1.toNat < policy.characteristic ∧ call.arg1.toNat < 2 ^ 32 := by
  cases step with
  | syscall success =>
    obtain ⟨pc, execution, _, _, ran, _, _, rfl⟩ := HostState.step_observations success
    have kind : execution.kind = .halt := SyscallKind.code_injective zero
    have executed := ((before.host.run_eq_some_iff policy (.ofSail before.sail) execution).mp ran).2.2.2.2.2
    rw [kind] at executed
    simp only [HostState.executeKind] at executed
    split at executed
    · assumption
    · contradiction

/-- Every newly halted endpoint has exactly the public Exit value, with no modular alias.
A stopped source instead admits only the existing identity path and preserves its prior status. -/
theorem GroundingCarrier.final_exit (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {target : ExecutionState}
    (path : ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events target) (running : source.host.exitCode = none)
    {code : BitVec 32} (halted : target.host.exitCode = some code) :
    code.toNat = witness.publicInput.exit_code.val := by
  obtain ⟨events, before, call, tape, _, step, zero, exit⟩ := path.ends_in_halt running halted
  have member : Machine.ExecutionEvent.syscall call ∈ carrier.events := by
    rw [tape]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have field := carrier.halt_field valid constraints balanced member zero
  have bounds := halt_bounds step zero
  rw [← exit, ← field, ZMod.val_natCast_of_lt bounds.1,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt bounds.2]

end SP1Clean.Soundness.HostHintReadCPU
