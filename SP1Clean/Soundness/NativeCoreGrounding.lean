import SP1Clean.Soundness.NativeCoreTransport
import SP1Clean.Soundness.WalkTimeline

/-! # Native grounding from the remaining execution facts

The checked image and combined AIR construct the ordered, refresh-free carrier and its timeline.
Boot truth, the genesis frontier, all structural row facts, and both balances are internal.
`ground_of_steps` leaves only the original mixed rows' semantic step/frame facts as premises.
It is a grounding combinator, not an unconditional native execution or host-correctness theorem.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The timeline is determined by the carrier's State edges, including wide system rows. -/
noncomputable def GroundingCarrier.timeline {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness) : Timeline :=
  ExecutionCarrier.timeline carrier

/-- The constructed timeline starts at the verifier's public initial clock. -/
theorem GroundingCarrier.timeline_start {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness) :
    carrier.timeline.start 0 = StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) :=
  ExecutionCarrier.timeline_start carrier

/-- Every carrier row advances to the actual successor index of its own timeline. -/
theorem GroundingCarrier.timeStep {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness) :
    ∀ row ∈ carrier.rows, ∀ n, StateMsg.timeNat row.statePull = carrier.timeline.start n →
      StateMsg.timeNat row.statePush = carrier.timeline.start (n + 1) :=
  ExecutionCarrier.timeStep carrier

/-- The public final clock is the timeline's last covered index. -/
theorem GroundingCarrier.finalClock {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness) :
    carrier.timeline.start carrier.rows.length = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) :=
  ExecutionCarrier.finalClock carrier

private theorem initial_pc {image : ProgramImage} (valid : image.Valid)
    (publicInput : SP1PublicIO (ZMod p)) (boot : publicInput.BootFor image) :
    StateMsg.pcBits (initialBoundaryStateMessage publicInput) = image.entry := by
  obtain ⟨entry, member, entryEq⟩ := List.any_eq_true.mp valid.2.2.1
  have same : entry.1 = image.entry := by simpa using entryEq
  have bound : image.entry.toNat < 2 ^ 48 := by
    have bounds : 2 ^ 16 ≤ entry.1.toNat ∧ entry.1.toNat + 4 ≤ 2 ^ 48 :=
      (valid.2.1 entry member).2.1
    rw [same] at bounds
    omega
  have high : (BitVec.extractLsb' 48 16 image.entry).toNat = 0 := by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt bound, Nat.zero_mod]
  have wordHigh : (Target.bitVecToWord (p := p) image.entry)[3] = 0 := by
    simp [Target.bitVecToWord, high]
  have full := Target.toBitVec64_bitVecToWord (p := p) image.entry
  rw [Word.toBitVec64, Word.toNat, wordHigh, ZMod.val_zero, zero_mul, add_zero] at full
  simp only [StateMsg.pcBits, initialBoundaryStateMessage, pcBits, boot.2.2.1, boot.2.2.2.1, boot.2.2.2.2]
  exact full

/-- The actual boot verifier supplies initial State truth on every trajectory beginning at the
checked image state. No caller-supplied semantic boundary binding is needed. -/
theorem GroundingCarrier.initialStateTruth {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (initial : trajectory 0 = some image.initialSailState) :
    LocalStateTruthG (image.toGuestProgram valid) trajectory carrier.timeline
      (initialBoundaryStateMessage witness.publicInput) := by
  have boot := image.initialSailState_loaded valid
  have pc := initial_pc valid witness.publicInput (public_boot witness constraints balanced).2
  refine ⟨0, image.initialSailState, initial, carrier.timeline_start.symm, ?_, boot.romLoaded, boot.configured⟩
  change image.initialSailState.regs.get? LeanRV64D.Defs.Register.PC =
    some (StateMsg.pcBits (initialBoundaryStateMessage witness.publicInput))
  rw [pc]
  exact boot.pc

/-- The generic engine is fully wired to the native AIR. Its only semantic premises are the
original mixed rows' step/frame facts on a trajectory starting at the checked image. The final
value conclusion concerns the original physical frontier at the public final State time; it does
not assert that an original refresh timestamp precedes that time. -/
theorem GroundingCarrier.ground_of_steps {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (initial : trajectory 0 = some image.initialSailState)
    (steps : ∀ event ∈ executionRows witness,
      LocalStepFactG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline
          (event.facts witness.data) ∧
      FrameFactG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline
          (event.facts witness.data)) :
    (∀ row ∈ carrier.rows, GroundedG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline row) ∧
      LocalStateTruthG (image.toGuestProgram valid) trajectory carrier.timeline (finalBoundaryStateMessage witness.publicInput) ∧
      (∀ loc message, memoryFinalFrontier witness loc = some message →
        LocalValueAtG trajectory image.initialSailState carrier.timeline loc
          (StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput)) message.value) := by
  have facts := carrier.engineFacts _ trajectory image.initialSailState carrier.timeline steps
  have genesis := memoryInitialFrontier_liveOK witness constraints balanced trajectory carrier.timeline initial
  rw [carrier.timeline_start] at genesis
  have grounded := walkG (image.toGuestProgram valid) trajectory image.initialSailState carrier.timeline
    (StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput))
    (finalBoundaryStateMessage witness.publicInput) carrier.final carrier.rows.length carrier.rows
    (initialBoundaryStateMessage witness.publicInput) (memoryInitialFrontier witness) rfl
    (fun row member => (facts row member).1) (fun row member => (facts row member).2)
    carrier.rowOK carrier.timeStep (carrier.initialStateTruth valid constraints balanced trajectory initial)
    genesis carrier.stateBalance carrier.memoryBalance
  refine ⟨grounded.1, grounded.2.1, ?_⟩
  intro loc message present
  obtain ⟨earlier, earlierPresent, _, value, _⟩ := carrier.finalRewrite loc message present
  have current := (grounded.2.2 loc earlier earlierPresent).2.2.1
  rwa [value] at current

end SP1Clean.Soundness.NativeCore
