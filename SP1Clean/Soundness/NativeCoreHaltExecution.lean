import SP1Clean.Soundness.NativeCoreTrajectory
import SP1Clean.Soundness.HaltGrounding

/-! # Native grounding with the trajectory and HALT derived internally

The combined AIR supplies HALT's zero code and clock bounds. Together with the carrier's own
event executor, these close its step and frame facts. The remaining semantic premises are ROM
preservation and the supplied host's agreement with active syscall rows. No instruction cases,
trajectory successor equations, or HALT execution facts remain caller obligations.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem halt_member {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} {row : HaltChip.Inputs (ZMod p)}
    (member : ExecutionRow.halt row ∈ executionRows witness) :
    ∃ physical ∈ (systemTable witness 2).table,
      haltRow witness.data physical = row ∧ row.is_real = 1 := by
  have active : row ∈ activeSystemRows (systemTable witness 2) (haltRow witness.data) (·.is_real) := by
    simpa [executionRows] using member
  obtain ⟨mapped, real⟩ := List.mem_filter.mp active
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  exact ⟨physical, physicalMem, rfl, of_decide_eq_true real⟩

/-- HALT's code and clock are consequences of the actual active row's assertions and Byte pulls. -/
theorem haltRows_staticFacts {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)} (member : ExecutionRow.halt row ∈ executionRows witness) :
    (haltEventOfRow row).rawCode = 0 ∧
      (((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ row.state.clk_16_24.val < 2 ^ 8) := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := halt_member member
  have checked := systemTable_constraints witness constraints 2 physical physicalMem
  rw [systemTable_component witness 2] at checked
  have realEval : Expression.eval (Environment.fromArray physical witness.data)
      (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod p)).is_real = 1 := by
    simpa only [haltRow_eq, circuit_norm] using real
  have zero := HaltChip.codeZero_of_shallow _ _ _
    (shallowConstraints_of_componentConstraints HaltChip.circuit _ checked) realEval
  refine ⟨?_, haltRow_cpuState_bounds_of_component _ witness.data (systemTable_component witness 2)
    ((finishedChannel_guarantees image witness constraints balanced).2 _ (systemTable_mem witness 2)).1
    physicalMem real⟩
  simpa only [haltEventOfRow, haltRow_eq] using zero

/-- Every physical HALT row supplies its generic step/frame facts on the constructed trajectory. -/
theorem GroundingCarrier.halt_engineFacts {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (handler : Machine.ExecutableSyscallHandler) {row : HaltChip.Inputs (ZMod p)}
    (member : ExecutionRow.halt row ∈ executionRows witness) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid handler)
        image.initialSailState carrier.timeline (haltRowFacts row) ∧
      FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid handler)
        image.initialSailState carrier.timeline (haltRowFacts row) := by
  have facts := haltRows_staticFacts witness constraints balanced member
  exact halt_engineFactsG row facts.2 _ _ _ _
    (fun n time => carrier.originalTimeStep member n time)
    (fun _ time => carrier.trajectory_halt valid handler member time facts.1)

/-- The native AIR grounds its own mixed execution. Only ROM preservation and active syscall
step/frame facts remain semantic obligations; the trajectory and all ordinary/HALT facts are
constructed internally. Final values refer to the physical frontier at the public final clock.
This is still conditional grounding, not the completed boot-to-HALT soundness theorem. -/
theorem GroundingCarrier.ground_of_host_steps {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (handler : Machine.ExecutableSyscallHandler)
    (codeMemoryCompatible : ∀ {n : ℕ} {state next : SailState},
      carrier.trajectory valid handler n = some state → Target.SailStep state next →
      Target.RomLoaded (image.toGuestProgram valid) state →
      Target.RomLoaded (image.toGuestProgram valid) next)
    (syscall : ∀ row, ExecutionRow.syscall row ∈ executionRows witness →
      LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid handler)
          image.initialSailState carrier.timeline (syscallRowFacts row) ∧
      FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid handler)
          image.initialSailState carrier.timeline (syscallRowFacts row)) :
    (∀ row ∈ carrier.rows, GroundedG (image.toGuestProgram valid) (carrier.trajectory valid handler)
      image.initialSailState carrier.timeline row) ∧
      LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid handler) carrier.timeline
        (finalBoundaryStateMessage witness.publicInput) ∧
      (∀ loc message, memoryFinalFrontier witness loc = some message →
        LocalValueAtG (carrier.trajectory valid handler) image.initialSailState carrier.timeline loc
          (StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput)) message.value) :=
  carrier.ground_of_system_steps valid constraints balanced _ (carrier.trajectory_zero valid handler)
    codeMemoryCompatible (fun _ member _ time => carrier.trajectory_ordinary valid handler member time)
    (fun _ member => carrier.halt_engineFacts valid constraints balanced handler member) syscall

end SP1Clean.Soundness.NativeCore
