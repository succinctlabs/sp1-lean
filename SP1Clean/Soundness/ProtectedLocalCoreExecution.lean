import SP1Clean.Soundness.ProtectedLocalCoreRom
import SP1Clean.Soundness.LocalCoreHaltExecution

/-! # Local grounding derives ordinary ROM preservation from the protected AIR

The protected witness supplies the original local constraints and balance, the exhaustive mixed
ordering, and byte permissions for every ordinary store. Its registered row effects preserve ROM
internally. HALT still uses the actual stateful host transition. Active SyscallInstrs effects remain
the explicit semantic obligation; this is not yet a full outgoing-snapshot execution theorem.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow)
open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Every ordinary row's step/frame facts, including ROM preservation, follow from this AIR. -/
theorem instruction_engineFacts {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) (witness : EnsembleWitness (ensemble (p := p) image source))
    (carrier : LocalCore.GroundingCarrier (localWitness witness)) (policy : HostPolicy)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈ LocalCore.executionRows (localWitness witness)) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
        (row.ordinaryRowFacts (localWitness witness).data) ∧
      FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
        (row.ordinaryRowFacts (localWitness witness).data) := by
  have originalConstraints := localWitness_constraints witness constraints
  have originalBalance := localWitness_balanced witness balanced
  have active : row ∈ LocalCore.instructionRows (localWitness witness) ∧
      (row.toChipRow (localWitness witness).data).is_real = 1 := by
    simpa [LocalCore.executionRows, LocalCore.activeInstructionRows] using member
  have inputs := LocalCore.instructionRows_staticInputs (localWitness witness)
    originalConstraints originalBalance active.1
  have contracts := supportedChip_groundingContracts row.chip inputs.registered
  have permission := instructionRows_write_permitted witness constraints balanced active.1 active.2
  apply contracts.engineFactsLocalG_of_rowEffect (localWitness witness).data row rfl inputs active.2 _
    (LocalCore.instructionRows_decoded valid (localWitness witness) originalConstraints originalBalance member)
    (carrier.trajectory valid policy) source.sail.realize carrier.timeline
    (fun _ effect loaded => effect.romLoaded_of_writePermission valid permission loaded)
  · intro n time
    have successor := carrier.originalTimeStep member n time
    have duration := (LocalCore.executionRows_advancing (localWitness witness)
      originalConstraints originalBalance member).2
    change StateMsg.timeNat (row.ordinaryRowFacts (localWitness witness).data).statePush =
      StateMsg.timeNat (row.ordinaryRowFacts (localWitness witness).data).statePull + 8 at duration
    change StateMsg.timeNat (row.ordinaryRowFacts (localWitness witness).data).statePush = carrier.timeline.start (n + 1) at successor
    exact successor.symm.trans (duration.trans (congrArg (fun clock => clock + 8) time))
  · exact carrier.trajectory_ordinary valid policy originalConstraints originalBalance member

/-- Ordinary instructions and HALT need no caller-supplied ROM-preservation hypothesis.
Only active SyscallInstrs step/frame effects remain before the shared grounding conclusion. -/
theorem ground_of_host_steps {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) (witness : EnsembleWitness (ensemble (p := p) image source))
    (carrier : LocalCore.GroundingCarrier (localWitness witness))
    (policy : HostPolicy) (field : policy.characteristic = p)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (syscall : ∀ row, ExecutionRow.syscall row ∈ LocalCore.executionRows (localWitness witness) →
      LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
          (syscallRowFacts row) ∧
        FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
          (syscallRowFacts row)) :
    (∀ row ∈ carrier.rows, GroundedG (image.toGuestProgram valid) (carrier.trajectory valid policy)
      source.sail.realize carrier.timeline row) ∧
      LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid policy) carrier.timeline
        (finalBoundaryStateMessage witness.publicInput) ∧
      (∀ loc message, LocalCore.memoryFinalFrontier (localWitness witness) loc = some message →
        LocalValueAtG (carrier.trajectory valid policy) source.sail.realize carrier.timeline loc
          (StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput)) message.value) := by
  have originalConstraints := localWitness_constraints witness constraints
  have originalBalance := localWitness_balanced witness balanced
  apply carrier.ground_of_steps valid originalConstraints originalBalance _ (carrier.trajectory_zero valid policy)
  intro event member
  cases event with
  | instruction row => exact instruction_engineFacts valid witness carrier policy constraints balanced member
  | halt row => exact carrier.halt_engineFacts valid policy field originalConstraints originalBalance member
  | syscall row => exact syscall row member

end SP1Clean.Soundness.ProtectedLocalCore
