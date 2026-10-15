import SP1Clean.Soundness.LocalCoreTransport
import SP1Clean.Soundness.WalkTimeline

/-! # Local grounding from the remaining execution facts

The checked source and combined AIR construct the ordered, refresh-free carrier and its timeline.
Complete-source truth, the genesis frontier, all structural row facts, and both balances are internal.
`ground_of_steps` leaves only the original mixed rows' semantic step/frame facts as premises.
It is a grounding combinator, not an unconditional native execution or host-correctness theorem.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The timeline is determined by the carrier's State edges, including wide system rows. -/
noncomputable def GroundingCarrier.timeline {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness) : Timeline :=
  NativeCore.ExecutionCarrier.timeline carrier

/-- The constructed timeline starts at the verifier's public initial clock. -/
theorem GroundingCarrier.timeline_start {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness) :
    carrier.timeline.start 0 = StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) :=
  NativeCore.ExecutionCarrier.timeline_start carrier

/-- Every carrier row advances to the actual successor index of its own timeline. -/
theorem GroundingCarrier.timeStep {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness) :
    ∀ row ∈ carrier.rows, ∀ n, StateMsg.timeNat row.statePull = carrier.timeline.start n →
      StateMsg.timeNat row.statePush = carrier.timeline.start (n + 1) :=
  NativeCore.ExecutionCarrier.timeStep carrier

/-- The public final clock is the timeline's last covered index. -/
theorem GroundingCarrier.finalClock {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness) :
    carrier.timeline.start carrier.rows.length = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) :=
  NativeCore.ExecutionCarrier.finalClock carrier

/-- The derived timeline starts at the complete source's actual clock. -/
theorem GroundingCarrier.timeline_source {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    (balanced : witness.BalancedChannels) :
    carrier.timeline.start 0 = source.clock :=
  carrier.timeline_start.trans (source_state_encoding witness balanced).1

/-- The local verifier supplies initial State truth on every trajectory beginning at the
complete checked source. No boot initialization or semantic boundary premise is supplied. -/
theorem GroundingCarrier.initialStateTruth {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (initial : trajectory 0 = some source.sail.realize) :
    LocalStateTruthG (image.toGuestProgram valid) trajectory carrier.timeline
      (initialBoundaryStateMessage witness.publicInput) :=
  LocalCore.initialStateTruth valid witness balanced trajectory carrier.timeline initial
    (carrier.timeline_source balanced)

/-- The generic engine is fully wired to the local AIR. Its only semantic premises are the
original mixed rows' step/frame facts on a trajectory starting at the checked local source. The final
value conclusion concerns the original physical frontier at the public final State time; it does
not assert that an original refresh timestamp precedes that time. -/
theorem GroundingCarrier.ground_of_steps {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (initial : trajectory 0 = some source.sail.realize)
    (steps : ∀ event ∈ executionRows witness,
      LocalStepFactG (image.toGuestProgram valid) trajectory source.sail.realize carrier.timeline
          (event.facts witness.data) ∧
      FrameFactG (image.toGuestProgram valid) trajectory source.sail.realize carrier.timeline
          (event.facts witness.data)) :
    (∀ row ∈ carrier.rows, GroundedG (image.toGuestProgram valid) trajectory source.sail.realize carrier.timeline row) ∧
      LocalStateTruthG (image.toGuestProgram valid) trajectory carrier.timeline (finalBoundaryStateMessage witness.publicInput) ∧
      (∀ loc message, memoryFinalFrontier witness loc = some message →
        LocalValueAtG trajectory source.sail.realize carrier.timeline loc
          (StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput)) message.value) := by
  have genesis := memoryInitialFrontier_liveOK witness constraints balanced trajectory carrier.timeline initial
  rw [carrier.timeline_start] at genesis
  exact NativeCore.ExecutionCarrier.ground carrier (image.toGuestProgram valid) trajectory source.sail.realize
    (carrier.initialStateTruth valid balanced trajectory initial) genesis steps

end SP1Clean.Soundness.LocalCore
