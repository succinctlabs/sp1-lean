import SP1Clean.Soundness.LocalCoreMemoryOrder
import SP1Clean.Soundness.CoreRowTransport

/-! # The local mixed carrier after refresh elimination

The carrier passed to grounding keeps every ordinary/HALT/syscall occurrence, rewrites only prior
Memory records, and uses canonical State endpoints. Its complete structural row contract and
semantic step/frame transport are derived from the checked image and raw constraints/balance.
The original rows' actual execution facts remain the next semantic obligation.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow canonicalRow rewrittenRows rewritten_core
  rewriteRows_forall₂ rewritten_memory syscall_readsInWindow_of_committed)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem syscallRows_readsInWindow {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    {row : SyscallInstrsChip.Inputs (ZMod p)}
    (member : row ∈ activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real)) :
    ReadsInWindow (syscallRowFacts row) := by
  obtain ⟨mapped, real⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have committed := syscall_program_committed_of_balance valid witness constraints balanced physicalMem (of_decide_eq_true real)
  exact syscall_readsInWindow_of_committed _ _ committed

/-- All original execution reads lie within their location's pre-effect window, with syscall
read times retained. Operand addresses for system rows come from the checked Program ledger. -/
theorem executionRows_readsInWindow_of_program {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) :
    ReadsInWindow (event.facts witness.data) := by
  simp only [executionRows, List.mem_append, List.mem_map] at member
  rcases member with (⟨decoded, _, rfl⟩ | ⟨halt, _, rfl⟩) | ⟨syscall, member, rfl⟩
  · intro pull pullMem
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp pullMem
    exact ⟨le_rfl, Nat.le_add_right _ _⟩
  · intro pull pullMem
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp pullMem
    exact ⟨le_rfl, Nat.le_add_right _ _⟩
  · exact syscallRows_readsInWindow valid witness constraints balanced member

/-- The complete local AIR supplies Program balance for the original read windows. -/
theorem executionRows_readsInWindow {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) :
    ReadsInWindow (event.facts witness.data) :=
  executionRows_readsInWindow_of_program valid witness constraints
    (balanced _ (by simp [ensemble, PublicVerifier.install, baseEnsemble, sp1Ensemble_channels])) member

private theorem canonical_times {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) :
    StateMsg.timeNat (canonState (event.facts witness.data).statePull) = StateMsg.timeNat (event.facts witness.data).statePull ∧
    StateMsg.pcBits (canonState (event.facts witness.data).statePull) = StateMsg.pcBits (event.facts witness.data).statePull ∧
    StateMsg.timeNat (canonState (event.facts witness.data).statePush) = StateMsg.timeNat (event.facts witness.data).statePush ∧
    StateMsg.pcBits (canonState (event.facts witness.data).statePush) = StateMsg.pcBits (event.facts witness.data).statePush := by
  have good := executionRows_good witness constraints balanced member
  rw [ExecutionRow.edge_eq_facts] at good
  exact ⟨timeNat_canonState good.1.1, pcBits_canonState good.1.2.1 good.1.2.2,
    timeNat_canonState good.2.1, pcBits_canonState good.2.2.1 good.2.2.2⟩

/-- A complete structural carrier for the generic grounding walk. The semantic alignment points
back to the actual event rows, so later step/frame proofs do not depend on refresh implementation. -/
abbrev GroundingCarrier {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :=
  NativeCore.ExecutionCarrier (ExecutionRow.facts witness.data) (executionRows witness)
    (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput)
    (memoryInitialFrontier witness) (memoryFinalFrontier witness)

/-- The checked image and raw AIR construct the final structural carrier. No row order, touch
permutation, prior bounds, refresh order, or semantic boundary is supplied by the caller. -/
theorem grounding_carrier {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    Nonempty (GroundingCarrier witness) := by
  obtain ⟨ordered, rows, touches, final, exhaustive, walk, alignment, chronology,
    rewrite, balance, _, finalRewrite⟩ := memory_refresh_free valid witness constraints balanced
  have paired : List.Forall₂ (fun newer original => WindowAligned newer original ∧
      RowOKCore (StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput)) newer ∧
      newer.statePull = canonState original.statePull ∧ newer.statePush = canonState original.statePush)
      (rewrittenRows rows touches) (ordered.map (ExecutionRow.facts witness.data)) := by
    apply rewriteRows_forall₂ alignment rewrite
    intro row rowMem original originalMem ts localAlignment rewritten
    obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp originalMem
    have active := exhaustive.mem_iff.mp eventMem
    have ok := chronology.rowOK row rowMem
    have canon := canonical_times witness constraints balanced active
    rw [← localAlignment.statePull, ← localAlignment.statePush] at canon
    have semantic := localAlignment.windowAligned
      (executionRows_readsInWindow valid witness constraints balanced active)
      (fun pull member => (executionRows_prior_bounds valid witness constraints balanced event active pull member).1)
    have transported := semantic.pullRewrite ok.touches.length_eq rewritten
    refine ⟨transported.stateRespell canon.1 canon.2.1 canon.2.2.1 canon.2.2.2,
      rowOKCore_stateRespell canon.1 canon.2.2.1
        (rewritten_core ok (fun pull member => (chronology.priorBounds row rowMem pull member).1) rewritten), ?_, ?_⟩
    · exact congrArg canonState localAlignment.statePull
    · exact congrArg canonState localAlignment.statePush
  refine ⟨⟨ordered, rewrittenRows rows touches, final, exhaustive,
    paired.imp (fun _ _ facts => facts.1), ?_, ?_, ?_, ?_, finalRewrite⟩⟩
  · intro row member
    obtain ⟨_, _, facts⟩ := forall₂_exists_right paired row member
    exact facts.2.1
  · have edges := List.forall₂_map_right_iff.mp
      (paired.imp (fun _ _ facts => facts.2.2))
    exact Walk.isWalk_forall₂ (ExecutionRow.canonEdge witness.data)
      (fun row : RowFacts p => (row.statePull, row.statePush))
      (fun event row => row.statePull = canonState (event.facts witness.data).statePull ∧
        row.statePush = canonState (event.facts witness.data).statePush)
      (fun related => by
        dsimp only [ExecutionRow.canonEdge]
        rw [ExecutionRow.edge_eq_facts]
        exact Prod.ext related.1.symm related.2.symm) edges.flip walk
  · rw [ExecutionRow.canonEdge_facts]
    exact walk
  · intro loc
    rw [(rewritten_memory rows touches loc).1, (rewritten_memory rows touches loc).2]
    exact balance loc

/-- The final carrier supplies exactly the generic engine's State multiset equation. -/
theorem GroundingCarrier.stateBalance {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness) :
    initialBoundaryStateMessage witness.publicInput ::ₘ
        (↑(carrier.rows.map (·.statePush)) : Multiset (StateMsg (ZMod p))) =
      finalBoundaryStateMessage witness.publicInput ::ₘ ↑(carrier.rows.map (·.statePull)) :=
  NativeCore.ExecutionCarrier.stateBalance carrier

/-- Per-event step and frame facts transport to the final carrier uniformly, over any trajectory
and timeline. These semantic premises are explicitly separate from carrier construction. -/
theorem GroundingCarrier.engineFacts {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    (program : Target.GuestProgram) (trajectory : Trajectory) (initial : SailState) (timeline : Timeline)
    (facts : ∀ event ∈ executionRows witness,
      LocalStepFactG program trajectory initial timeline (event.facts witness.data) ∧
      FrameFactG program trajectory initial timeline (event.facts witness.data)) :
    ∀ row ∈ carrier.rows, LocalStepFactG program trajectory initial timeline row ∧
      FrameFactG program trajectory initial timeline row :=
  NativeCore.ExecutionCarrier.engineFacts carrier program trajectory initial timeline facts

end SP1Clean.Soundness.LocalCore
