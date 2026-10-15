import SP1Clean.Soundness.LocalCoreBoundaries
import SP1Clean.Soundness.GenericWalk
import SP1Clean.Soundness.TypedState

/-! # Grounding genesis from the checked complete local source

The combined AIR checks the source's platform configuration, ROM, and actual incoming PC/clock.
Its physical source records supply the initial memory frontier. These results initialize the
generic timed engine on any trajectory beginning at that source, including a continuation at a
nonzero clock. A source record's zero timestamp is a local seed, not a claim about its last access
in an earlier shard. The mixed execution walk and complete outgoing boundary remain separate work.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The public verifier's incoming State message names the complete source's actual time and PC. -/
theorem source_state_encoding_of_checks {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (sourceChecks : witness.BalancedChannel (sourceChannel image source)) :
    StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) = source.clock ∧
      StateMsg.pcBits (initialBoundaryStateMessage witness.publicInput) = source.pc := by
  have checked := (source_balanced_iff witness).mp sourceChecks
  exact ⟨checked.2.1.clock checked.1.2.2.1, checked.2.1.pc checked.1.2.2.2⟩

/-- The complete local AIR supplies the installed source-check balance. -/
theorem source_state_encoding {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (balanced : witness.BalancedChannels) :
    StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) = source.clock ∧
      StateMsg.pcBits (initialBoundaryStateMessage witness.publicInput) = source.pc :=
  source_state_encoding_of_checks witness
    (balanced _ (List.mem_append_right _ (List.mem_singleton_self _)))

/-- Complete source validation and AIR binding supply the initial State truth on a local trajectory. -/
theorem initialStateTruth_of_checks {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (sourceChecks : witness.BalancedChannel (sourceChannel image source))
    (trajectory : Trajectory) (timeline : Timeline)
    (initial : trajectory 0 = some source.sail.realize) (start : timeline.start 0 = source.clock) :
    LocalStateTruthG (image.toGuestProgram valid) trajectory timeline
      (initialBoundaryStateMessage witness.publicInput) := by
  have checked := ((source_balanced_iff witness).mp sourceChecks).1
  have encoding := source_state_encoding_of_checks witness sourceChecks
  refine ⟨0, source.sail.realize, initial, encoding.1.trans start.symm, ?_,
    checked.romLoaded, checked.configured⟩
  change source.sail.realize.regs.get? LeanRV64D.Defs.Register.PC =
    some (StateMsg.pcBits (initialBoundaryStateMessage witness.publicInput))
  rw [encoding.2]
  exact checked.pc

/-- The complete local AIR supplies the installed source-check balance. -/
theorem initialStateTruth {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (timeline : Timeline)
    (initial : trajectory 0 = some source.sail.realize) (start : timeline.start 0 = source.clock) :
    LocalStateTruthG (image.toGuestProgram valid) trajectory timeline
      (initialBoundaryStateMessage witness.publicInput) :=
  initialStateTruth_of_checks valid witness
    (balanced _ (List.mem_append_right _ (List.mem_singleton_self _))) trajectory timeline initial start

/-- The initial frontier selects the authentic physical source record for each location. -/
noncomputable def memoryInitialFrontier {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : MemLoc → Option (MemoryMsg (ZMod p)) :=
  fun loc => (((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness)).filter
    (fun message => decide (MemoryMsg.locOf message = loc))).head?

/-- Source-record values are contents of the actual full Sail state used by execution. -/
theorem memoryInitialFrontier_content_of_channels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (sourceChecks : witness.BalancedChannel (sourceChannel image source))
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (membership : ∀ channel ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot,
      witness.BalancedChannel channel)
    {loc : MemLoc} {message : MemoryMsg (ZMod p)}
    (present : memoryInitialFrontier witness loc = some message) :
    MemoryMsg.locOf message = loc ∧ MemoryBoundary.SnapshotSpec source.sail.memorySnapshot message ∧
      locContent source.sail.realize loc = some (Word.toBitVec64 message.value) := by
  have member := List.mem_filter.mp (List.mem_of_head? present)
  have same := of_decide_eq_true member.2
  have authentic := (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records_valid_of_tables
    (sourceWitness witness) (sourceTables_spec_of_channels witness constraints bytes membership) _ member.1
  refine ⟨same, authentic, ?_⟩
  rw [← same]
  exact authentic.locContent ((source_balanced_iff witness).mp sourceChecks).1.memory

/-- The complete local AIR supplies source checks, Byte guarantees, and register membership. -/
theorem memoryInitialFrontier_content {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {loc : MemLoc} {message : MemoryMsg (ZMod p)}
    (present : memoryInitialFrontier witness loc = some message) :
    MemoryMsg.locOf message = loc ∧ MemoryBoundary.SnapshotSpec source.sail.memorySnapshot message ∧
      locContent source.sail.realize loc = some (Word.toBitVec64 message.value) :=
  memoryInitialFrontier_content_of_channels witness constraints
    (balanced _ (List.mem_append_right _ (List.mem_singleton_self _)))
    (fun table member => ((finishedChannel_guarantees image source witness constraints balanced).2 table member).1)
    (fun channel known => balanced channel (by
      simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons,
        List.not_mem_nil, or_false] at known
      rcases known with rfl | rfl <;> simp [ensemble, PublicVerifier.install, baseEnsemble])) present

/-- Source constraints and channel closure supply the complete live-memory invariant at local genesis.
No memory-truth or source-timestamp premise is supplied by the caller. -/
theorem memoryInitialFrontier_liveOK_of_channels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (sourceChecks : witness.BalancedChannel (sourceChannel image source))
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (membership : ∀ channel ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot,
      witness.BalancedChannel channel)
    (trajectory : Trajectory) (timeline : Timeline)
    (initial : trajectory 0 = some source.sail.realize) :
    LiveOKG trajectory source.sail.realize timeline (timeline.start 0) (memoryInitialFrontier witness) := by
  intro loc message present
  obtain ⟨same, authentic, content⟩ :=
    memoryInitialFrontier_content_of_channels witness constraints sourceChecks bytes membership present
  have atStart : LocalValueAtG trajectory source.sail.realize timeline loc (timeline.start 0) message.value :=
    (localValueAtG_stepStart_iff initial).mpr content
  refine ⟨same, ⟨authentic.1, authentic.2.1, ?_⟩, atStart, ?_⟩
  · rw [same, authentic.2.2.1]
    by_cases zero : timeline.start 0 = 0
    · simpa only [zero] using atStart
    · simpa only [LocalValueAtG, microValueG, if_pos (Nat.pos_of_ne_zero zero)] using content
  · rw [authentic.2.2.1]
    exact Nat.zero_le _

/-- The complete local AIR supplies source checks, Byte guarantees, and register membership. -/
theorem memoryInitialFrontier_liveOK {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (timeline : Timeline)
    (initial : trajectory 0 = some source.sail.realize) :
    LiveOKG trajectory source.sail.realize timeline (timeline.start 0) (memoryInitialFrontier witness) :=
  memoryInitialFrontier_liveOK_of_channels witness constraints
    (balanced _ (List.mem_append_right _ (List.mem_singleton_self _)))
    (fun table member => ((finishedChannel_guarantees image source witness constraints balanced).2 table member).1)
    (fun channel known => balanced channel (by
      simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons,
        List.not_mem_nil, or_false] at known
      rcases known with rfl | rfl <;> simp [ensemble, PublicVerifier.install, baseEnsemble]))
    trajectory timeline initial

end SP1Clean.Soundness.LocalCore
