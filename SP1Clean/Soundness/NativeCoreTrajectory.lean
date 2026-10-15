import SP1Clean.Soundness.NativeCoreInstructionExecution
import SP1Clean.Soundness.CoreExecutionTrajectory

/-! # Executing the native AIR's ordered events

The carrier supplies a complete ordered transcript, including ordinary instructions, HALT, and
host calls. The existing event executor determines its trajectory from the checked initial state.
The State walk identifies each event's exact list position, so ordinary successor equations are
conclusions rather than caller premises. The HALT wrapper fixes the zero-code host behavior;
agreement of other host effects with the AIR remains a separate obligation.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The transcript retains every active row occurrence in the balance-derived State order. -/
noncomputable def GroundingCarrier.events {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness) :
    List Machine.ExecutionEvent :=
  ExecutionCarrier.events carrier

/-- Execute the carrier's transcript with canonical HALT and the supplied non-HALT host. -/
noncomputable def GroundingCarrier.trajectory {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (handler : Machine.ExecutableSyscallHandler) : Trajectory :=
  eventTrajectory handler.withHalt (image.toGuestProgram valid) carrier.events image.initialSailState

/-- Execution starts at the checked program image's configured Sail state. -/
theorem GroundingCarrier.trajectory_zero {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (handler : Machine.ExecutableSyscallHandler) :
    carrier.trajectory valid handler 0 = some image.initialSailState := rfl

/-- A physical event's bus clock identifies its exact position, including repeated row values. -/
theorem GroundingCarrier.ordered_at {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n) :
    carrier.ordered[n]? = some event :=
  ExecutionCarrier.ordered_at carrier member atIndex

/-- The semantic transcript and the clock-indexed event are the same occurrence. -/
theorem GroundingCarrier.event_at {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n) :
    carrier.events[n]? = some event.event :=
  ExecutionCarrier.event_at carrier member atIndex

/-- Each ordinary event executes the official Sail step at its own derived timeline position. -/
theorem GroundingCarrier.trajectory_ordinary {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (handler : Machine.ExecutableSyscallHandler) {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull = carrier.timeline.start n) :
    carrier.trajectory valid handler (n + 1) =
      (carrier.trajectory valid handler n).bind Machine.stepOnce := by
  unfold trajectory
  rw [eventTrajectory_succ, carrier.event_at member atIndex]
  rfl

/-- Each active syscall invokes the supplied host at its own derived timeline position. -/
theorem GroundingCarrier.trajectory_syscall {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (handler : Machine.ExecutableSyscallHandler) {row : SyscallInstrsChip.Inputs (ZMod p)}
    (member : ExecutionRow.syscall row ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (syscallRowFacts row).statePull = carrier.timeline.start n) :
    carrier.trajectory valid handler (n + 1) = (carrier.trajectory valid handler n).bind
      (handler.withHalt.run (image.toGuestProgram valid) (syscallEventOfRow row)) := by
  unfold trajectory
  rw [eventTrajectory_succ, carrier.event_at member atIndex]
  rfl

/-- A zero-code HALT event parks the PC and preserves every register and memory location. -/
theorem GroundingCarrier.trajectory_halt {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (handler : Machine.ExecutableSyscallHandler) {row : HaltChip.Inputs (ZMod p)}
    (member : ExecutionRow.halt row ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (haltRowFacts row).statePull = carrier.timeline.start n)
    (zero : (haltEventOfRow row).rawCode = 0) :
    carrier.trajectory valid handler (n + 1) = (carrier.trajectory valid handler n).map
      (fun state => { state with regs := state.regs.insert LeanRV64D.Defs.Register.PC Machine.haltPc }) := by
  unfold trajectory
  rw [eventTrajectory_succ, carrier.event_at member atIndex]
  simp only [ExecutionRow.event, Machine.executeEvent?,
    Machine.ExecutableSyscallHandler.withHalt_run_zero _ _ _ _ zero, Option.map_eq_bind,
    Function.comp_def]

end SP1Clean.Soundness.NativeCore
