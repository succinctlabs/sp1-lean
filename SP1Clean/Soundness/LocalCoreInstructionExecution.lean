import SP1Clean.Soundness.LocalCoreTrajectory
import SP1Clean.Soundness.CoreInstructionExecution

/-! # Ordinary instruction facts on the stateful local trajectory

Physical constraints and closed Byte/Program guarantees provide all static chip inputs. Incoming
State truth authenticates the PC and configuration, so official decoding excludes ECALL and the
paired replay's terminal-PC invariant proves that the host is still running. These derived guards
make ordinary replay agree with Sail exactly where grounding needs it. All 25 instruction cases
remain in the registered chip contracts. ROM protection and the host rows' effects remain open.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The combined assembly supplies every ordinary row's static component inputs. -/
theorem instructionRows_staticInputs {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : row ∈ instructionRows witness) :
    DecodedRowStaticInputs row witness.data :=
  ⟨mem_chip_of_mem_decodeInstructionTables member,
    instructionRows_constraints witness constraints row member,
    (instructionRows_finished_guarantees witness constraints balanced member).1,
    (instructionRows_finished_guarantees witness constraints balanced member).2⟩

private theorem instruction_member {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈ executionRows witness) :
    row ∈ instructionRows witness ∧ (row.toChipRow witness.data).is_real = 1 := by
  simpa [executionRows, activeInstructionRows] using member

/-- An active ordinary row names a supported official decode, excluding the ECALL branch. -/
theorem instructionRows_decoded {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : ExecutionRow.instruction row ∈ executionRows witness) :
    Target.decodedInROM (image.toGuestProgram valid) (programAccess (row.toChipRow witness.data).view).toRow := by
  obtain ⟨rowMem, real⟩ := instruction_member member
  have inputs := instructionRows_staticInputs witness constraints balanced rowMem
  exact (instructionRows_program_committed valid witness constraints balanced rowMem real).decoded_of_opcode_ne
    (supportedChip_fetchDiscriminantShape row.chip inputs.registered witness.data row.physical
      inputs.constraints inputs.byte real)

/-- State truth discharges both guards of ordinary stateful replay. No running-host or
trajectory-successor premise is supplied by the caller. -/
theorem GroundingCarrier.trajectory_ordinary {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : ExecutionRow.instruction row ∈ executionRows witness)
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid policy) carrier.timeline
      (row.ordinaryRowFacts witness.data).statePull)
    (n : ℕ) (time : StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull = carrier.timeline.start n) :
    carrier.trajectory valid policy (n + 1) = (carrier.trajectory valid policy n).bind Machine.stepOnce := by
  obtain ⟨m, state, present, atIndex, pc, _, configured⟩ := pull
  have same : m = n := start_injective carrier.timeline (atIndex.symm.trans time)
  subst m
  change (carrier.pairedTrajectory valid policy n).map ExecutionState.sail = some state at present
  obtain ⟨whole, paired, sail⟩ := Option.map_eq_some_iff.mp present
  have decoded := instructionRows_decoded valid witness constraints balanced member
  have atPc : whole.sail.regs.get? LeanRV64D.Defs.Register.PC =
      some (Target.pcBitsOfRow (programAccess (row.toChipRow witness.data).view).toRow) := by
    rw [sail, program_pc_eq_statePull]
    exact pc
  have notEcall := decoded.notEcall (by rwa [sail]) atPc
  obtain ⟨_, _, fetched, _, _⟩ := decoded
  have running := carrier.pairedTrajectory_running_of_fetch valid policy constraints balanced member paired atPc fetched
  change ((carrier.pairedTrajectory valid policy (n + 1)).map ExecutionState.sail) = _
  rw [carrier.pairedTrajectory_succ valid policy member time, paired, Option.bind_some]
  change (replayStep? policy (image.toGuestProgram valid) whole .ordinary).map ExecutionState.sail = _
  rw [replayStep?_ordinary_sail _ _ _ running notEcall]
  simp only [trajectory, paired, Option.map_some, Option.bind_some]

/-- Registered chip bridges discharge ordinary step/frame facts on the actual stateful replay.
The only additional semantic premise is preservation of the committed instruction bytes. -/
theorem GroundingCarrier.instruction_engineFacts {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : ExecutionRow.instruction row ∈ executionRows witness)
    (codeMemoryCompatible : ∀ {n : ℕ} {state next : SailState},
      carrier.trajectory valid policy n = some state → Target.SailStep state next →
      Target.RomLoaded (image.toGuestProgram valid) state → Target.RomLoaded (image.toGuestProgram valid) next) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
        (row.ordinaryRowFacts witness.data) ∧
      FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
        (row.ordinaryRowFacts witness.data) := by
  obtain ⟨rowMem, real⟩ := instruction_member member
  have inputs := instructionRows_staticInputs witness constraints balanced rowMem
  have contracts := supportedChip_groundingContracts row.chip inputs.registered
  apply contracts.engineFactsLocalG_of_stateStep witness.data row rfl inputs real _
    (instructionRows_decoded valid witness constraints balanced member)
    (carrier.trajectory valid policy) source.sail.realize carrier.timeline codeMemoryCompatible
  · intro n time
    have successor := carrier.originalTimeStep member n time
    have duration := (executionRows_advancing witness constraints balanced member).2
    change StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePush =
      StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull + 8 at duration
    change StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePush = carrier.timeline.start (n + 1) at successor
    exact successor.symm.trans (duration.trans (congrArg (fun clock => clock + 8) time))
  · exact carrier.trajectory_ordinary valid policy constraints balanced member

/-- The local AIR now supplies the trajectory and every ordinary instruction's semantics.
Only ROM preservation and the two system-row kinds remain explicit semantic obligations.
This statement does not assume successful replay or an execution path. -/
theorem GroundingCarrier.ground_of_system_steps {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (codeMemoryCompatible : ∀ {n : ℕ} {state next : SailState},
      carrier.trajectory valid policy n = some state → Target.SailStep state next →
      Target.RomLoaded (image.toGuestProgram valid) state → Target.RomLoaded (image.toGuestProgram valid) next)
    (halt : ∀ row, ExecutionRow.halt row ∈ executionRows witness →
      LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
          (haltRowFacts row) ∧
        FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
          (haltRowFacts row))
    (syscall : ∀ row, ExecutionRow.syscall row ∈ executionRows witness →
      LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
          (syscallRowFacts row) ∧
        FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
          (syscallRowFacts row)) :
    (∀ row ∈ carrier.rows, GroundedG (image.toGuestProgram valid) (carrier.trajectory valid policy)
      source.sail.realize carrier.timeline row) ∧
      LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid policy) carrier.timeline
        (finalBoundaryStateMessage witness.publicInput) ∧
      (∀ loc message, memoryFinalFrontier witness loc = some message →
        LocalValueAtG (carrier.trajectory valid policy) source.sail.realize carrier.timeline loc
          (StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput)) message.value) := by
  apply carrier.ground_of_steps valid constraints balanced _ (carrier.trajectory_zero valid policy)
  intro event member
  cases event with
  | instruction row => exact carrier.instruction_engineFacts valid policy constraints balanced member codeMemoryCompatible
  | halt row => exact halt row member
  | syscall row => exact syscall row member

end SP1Clean.Soundness.LocalCore
