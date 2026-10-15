import SP1Clean.Soundness.NativeCoreGrounding
import SP1Clean.Soundness.SyscallWiring

/-! # Ordinary execution facts for the authenticated native core

All 25 ordinary chip contracts consume physical constraints and the combined AIR's finished
Byte/Program guarantees. Incoming Memory currency supplies their remaining circuit inputs.
The carrier derives the eight-tick successor position internally. The remaining semantic boundary
is the chosen trajectory's ordinary Sail transition, ROM preservation, and HALT/host execution.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The combined assembly supplies the component-local inputs for every physical instruction row. -/
theorem instructionRows_staticInputs {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : row ∈ instructionRows witness) :
    DecodedRowStaticInputs row witness.data :=
  ⟨mem_chip_of_mem_decodeInstructionTables member,
    instructionRows_constraints witness constraints row member,
    (instructionRows_finished_guarantees witness constraints balanced member).1,
    (instructionRows_finished_guarantees witness constraints balanced member).2⟩

/-- Transport the derived successor position back to the original event, before alignment,
refresh elimination, and State canonicalization. -/
theorem GroundingCarrier.originalTimeStep {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) :
    ∀ n, StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n →
      StateMsg.timeNat (event.facts witness.data).statePush = carrier.timeline.start (n + 1) := by
  have originalMem := List.mem_map_of_mem (f := ExecutionRow.facts witness.data)
    (carrier.exhaustive.mem_iff.mpr member)
  obtain ⟨row, rowMem, aligned⟩ := forall₂_exists_right carrier.aligned.flip _ originalMem
  intro n time
  rw [← aligned.pushTime]
  exact carrier.timeStep row rowMem n (aligned.pullTime.trans time)

private theorem instruction_member {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈ executionRows witness) :
    row ∈ instructionRows witness ∧ (row.toChipRow witness.data).is_real = 1 := by
  simpa [executionRows, activeInstructionRows] using member

/-- Ordinary rows discharge their own step and frame facts through the registered whole-chip
Sail bridges. No chip assumptions, operand bindings, or Memory truth are supplied by the caller. -/
theorem GroundingCarrier.instruction_engineFacts {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : ExecutionRow.instruction row ∈ executionRows witness)
    (trajectory : Trajectory)
    (codeMemoryCompatible : ∀ {n : ℕ} {state next : SailState},
      trajectory n = some state → Target.SailStep state next →
      Target.RomLoaded (image.toGuestProgram valid) state →
      Target.RomLoaded (image.toGuestProgram valid) next)
    (step : ∀ n, StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull = carrier.timeline.start n →
      trajectory (n + 1) = (trajectory n).bind Machine.stepOnce) :
    LocalStepFactG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline
        (row.ordinaryRowFacts witness.data) ∧
      FrameFactG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline
        (row.ordinaryRowFacts witness.data) := by
  obtain ⟨rowMem, real⟩ := instruction_member member
  have inputs := instructionRows_staticInputs witness constraints balanced rowMem
  have contracts := supportedChip_groundingContracts row.chip inputs.registered
  have committed := instructionRows_program_committed valid witness constraints balanced rowMem real
  have decode := committed.decoded_of_opcode_ne
    (supportedChip_fetchDiscriminantShape row.chip inputs.registered witness.data row.physical
      inputs.constraints inputs.byte real)
  apply contracts.engineFactsLocalG witness.data row rfl inputs real _ decode
    trajectory image.initialSailState carrier.timeline codeMemoryCompatible _ step
  intro n time
  have successor := carrier.originalTimeStep member n time
  have duration := (executionRows_advancing witness constraints balanced member).2
  change StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePush =
    StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull + 8 at duration
  change StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePush =
    carrier.timeline.start (n + 1) at successor
  exact successor.symm.trans (duration.trans (congrArg (fun clock => clock + 8) time))

/-- Native grounding with all ordinary instruction semantics discharged. The remaining premises
name the trajectory choice, ROM protection, and the two system-row kinds explicitly. -/
theorem GroundingCarrier.ground_of_system_steps {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (initial : trajectory 0 = some image.initialSailState)
    (codeMemoryCompatible : ∀ {n : ℕ} {state next : SailState},
      trajectory n = some state → Target.SailStep state next →
      Target.RomLoaded (image.toGuestProgram valid) state →
      Target.RomLoaded (image.toGuestProgram valid) next)
    (ordinary : ∀ row, ExecutionRow.instruction row ∈ executionRows witness →
      ∀ n, StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull = carrier.timeline.start n →
        trajectory (n + 1) = (trajectory n).bind Machine.stepOnce)
    (halt : ∀ row, ExecutionRow.halt row ∈ executionRows witness →
      LocalStepFactG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline
          (haltRowFacts row) ∧
      FrameFactG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline
          (haltRowFacts row))
    (syscall : ∀ row, ExecutionRow.syscall row ∈ executionRows witness →
      LocalStepFactG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline
          (syscallRowFacts row) ∧
      FrameFactG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline
          (syscallRowFacts row)) :
    (∀ row ∈ carrier.rows, GroundedG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline row) ∧
      LocalStateTruthG (image.toGuestProgram valid) trajectory carrier.timeline (finalBoundaryStateMessage witness.publicInput) ∧
      (∀ loc message, memoryFinalFrontier witness loc = some message →
        LocalValueAtG trajectory image.initialSailState carrier.timeline loc
          (StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput)) message.value) := by
  apply carrier.ground_of_steps valid constraints balanced trajectory initial
  intro event member
  cases event with
  | instruction row =>
    exact carrier.instruction_engineFacts valid constraints balanced member trajectory
      codeMemoryCompatible (ordinary row member)
  | halt row => exact halt row member
  | syscall row => exact syscall row member

end SP1Clean.Soundness.NativeCore
