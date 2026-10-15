import SP1Clean.Soundness.CoreMemoryBalance
import SP1Clean.Soundness.GenericWalk

/-! # Actual Memory balance of the authenticated native core

The initial and final inventories delimit the complete physical Memory ledger. The interior
retains ordinary instructions, refreshes, HALT, and syscalls, including active syscall rows.
Constraints force unit signed multiplicities; count-bounded Clean balance then gives an exact
per-location equation with unique authenticated boundary records. No Memory guarantee or
execution-order premise is used to establish this equation.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics
open TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The unchanged physical Memory ledger after the two three-table inventories. -/
noncomputable def memoryInterior {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) : List (TypedInteraction (memoryChannel (p := p))) :=
  (witness.tables.drop 6).flatMap (typedTableInteractionsWith · witness.data memoryChannel)

/-- The interior adapter preserves every raw interaction, including disabled interactions. -/
theorem memoryInterior_raw {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (memoryInterior witness).map TypedInteraction.raw =
      (witness.tables.drop 6).flatMap (·.interactionsWith witness.data memoryChannel.toRaw) := by
  simp only [memoryInterior, List.map_flatMap, typedTableInteractionsWith_raw]

private theorem verifier_memory_silent (image : ProgramImage) (env : Environment (ZMod p)) :
    (ensemble image).verifierOperations.interactionValuesWith memoryChannel.toRaw env = [] := by
  rw [verifier_values_of_registered image env memoryChannel.toRaw
    (by simp [baseEnsemble, sp1Ensemble_channels])]
  change (verifierInteractions image).circuitOperations.interactionValuesWith memoryChannel.toRaw env = []
  simp only [Verifier.Program.circuitOperations, Verifier.Program.operations,
    Operations.interactionValuesWith, Operations.interactionsWith, verifierInteractions_interactions]
  simp [verifierMain, GeneralFormalCircuit.toSubcircuit_interactions, sp1StateVerifier,
    sp1StateVerifierMain, OrderedBoundaryVerifier.circuit, OrderedBoundaryVerifier.main,
    OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
    stateChannel, memoryChannel, byteChannel, exitChannel, circuit_norm]

/-- Exact decomposition of the physical ledger into initial records, final records, and all
remaining interactions. The typed `pushedIfValue (-1)` is the finalizer's negative emission with
`assumeGuarantees = false`; signed message selection places it on the consumed side. -/
theorem memory_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    typedEnsembleInteractionsWith witness memoryChannel =
      (InitialMemoryEnsemble.records (initialWitness witness)).map
        (TypedInteraction.pushedIfValue memoryChannel 1) ++
      (FinalMemoryEnsemble.records (finalWitness witness)).map
        (TypedInteraction.pushedIfValue memoryChannel (-1)) ++
      memoryInterior witness := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedEnsembleInteractionsWith_raw, List.map_append, List.map_append, memoryInterior_raw]
  simp only [List.map_map]
  change witness.interactionsWith memoryChannel.toRaw =
    (InitialMemoryEnsemble.records (initialWitness witness)).map memoryChannel.pushedValue ++
    (FinalMemoryEnsemble.records (finalWitness witness)).map (memoryChannel.emittedValue (-1)) ++ _
  rw [← initial_memory_interactions witness, ← final_memory_interactions witness]
  change (ensemble image).verifierOperations.interactionValuesWith memoryChannel.toRaw
    (Environment.fromInput witness.publicInput witness.data) ++
    witness.tables.flatMap (·.interactionsWith witness.data memoryChannel.toRaw) = _
  rw [verifier_memory_silent, List.nil_append]
  have split := congrArg (List.flatMap (fun t : Table (ZMod p) => t.interactionsWith witness.data memoryChannel.toRaw))
    (List.take_append_drop 3 witness.tables)
  have splitTail := congrArg (List.flatMap (fun t : Table (ZMod p) => t.interactionsWith witness.data memoryChannel.toRaw))
    (List.take_append_drop 3 (witness.tables.drop 3))
  simp only [List.flatMap_append, List.drop_drop] at split splitTail
  rw [← split, ← splitTail, List.append_assoc]

/-- Every interaction of the unchanged interior has signed-unit multiplicity or zero. -/
theorem memoryInterior_signedBinary {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (constraints : witness.Constraints) :
    ∀ interaction ∈ memoryInterior witness,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  intro interaction member
  have rawMem := List.mem_map_of_mem (f := TypedInteraction.raw) member
  rw [memoryInterior_raw] at rawMem
  obtain ⟨table, tableMem, rowMem⟩ := List.mem_flatMap.mp rawMem
  obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp rowMem
  have componentMem := List.mem_map_of_mem (f := fun t : Table (ZMod p) => t.component) tableMem
  rw [List.map_drop, witness.tables_map_component] at componentMem
  change table.component ∈ afterFinalTables image ++ [ramMembership image] at componentMem
  rcases List.mem_append.mp componentMem with componentMem | fixed
  · exact interior_memoryBinary image table.component componentMem witness.data physical
      (constraints table (List.mem_of_mem_drop tableMem)
        physical physicalMem) interaction.raw emitted

  · have silent : table.interactionsWith witness.data memoryChannel.toRaw = [] := by
      apply table.interactionsWith_nil_of_channel_not_mem
      rw [List.mem_singleton.mp fixed]
      change memoryChannel.toRaw ∉ [(InitialMemoryLookup.membership image.initialMemory (2 ^ 48)
        "sp1.native.initial_memory").channel.toRaw]
      simp [memoryChannel, InitialMemoryLookup.membership, StaticTable.channel, Channel.toRaw]
    rw [silent] at rowMem
    exact (List.not_mem_nil rowMem).elim

/-- Raw constraints force signed-unit multiplicities throughout the combined Memory ledger.
This includes both inventories and all active system rows. -/
theorem memory_signedBinary {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (constraints : witness.Constraints) :
    ∀ interaction ∈ typedEnsembleInteractionsWith witness memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  rw [memory_interactions]
  exact memoryBoundary_signedBinary _ _ _ (memoryInterior_signedBinary witness constraints)

/-- Initial records and all interior pushes are a permutation of final records and all interior
pulls, as complete typed messages. Values, locations, and timestamps are preserved together. -/
theorem memory_records_perm {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (InitialMemoryEnsemble.records (initialWitness witness) ++ producedMessages (memoryInterior witness)).Perm
      (FinalMemoryEnsemble.records (finalWitness witness) ++ consumedMessages (memoryInterior witness)) := by
  apply memoryBoundary_records_perm _ _ _ (memoryInterior_signedBinary witness constraints)
  rw [← memory_interactions, typedEnsembleInteractionsWith_raw]
  exact balanced _ (by simp [ensemble, baseEnsemble, sp1Ensemble_channels])

/-- The unique authenticated initial record at each touched location, if present. -/
noncomputable def memoryInitialFrontier {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (loc : MemLoc) : Option (MemoryMsg (ZMod p)) :=
  ((InitialMemoryEnsemble.records (initialWitness witness)).filter
    (fun message => decide (MemoryMsg.locOf message = loc))).head?

/-- The unique final record at each finalized location, without assuming its value is current. -/
noncomputable def memoryFinalFrontier {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (loc : MemLoc) : Option (MemoryMsg (ZMod p)) :=
  ((FinalMemoryEnsemble.records (finalWitness witness)).filter
    (fun message => decide (MemoryMsg.locOf message = loc))).head?

/-- The exact per-location Memory equation needed for timed grounding. Its endpoints are unique
records derived from this assembly's own ordering constraints and balance. No boundary uniqueness,
Memory truth, padding inactivity, or syscall inactivity is assumed. -/
theorem memory_frontier_balance {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (loc : MemLoc) :
    optMS (memoryInitialFrontier witness loc) +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(producedMessages (memoryInterior witness)) : Multiset _) =
      optMS (memoryFinalFrontier witness loc) +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(consumedMessages (memoryInterior witness)) : Multiset _) := by
  exact memoryBoundary_frontier_balance _ _ _ _
    (initial_records_locations_nodup witness constraints balanced)
    (final_records_locations_nodup witness constraints balanced)
    (memory_records_perm witness constraints balanced) loc

/-- A present initial frontier record is authentic at the requested location. -/
theorem memoryInitialFrontier_authentic {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {loc : MemLoc} {message : MemoryMsg (ZMod p)}
    (present : memoryInitialFrontier witness loc = some message) :
    MemoryMsg.locOf message = loc ∧ MemoryBoundary.InitialSpec image message := by
  have member := List.mem_filter.mp (List.mem_of_head? present)
  exact ⟨of_decide_eq_true member.2, initial_records_authentic witness constraints balanced _ member.1⟩

/-- A present final frontier record has the requested canonical location. Currency of its value
and validity of its clock are conclusions still to be supplied by the timed walk. -/
theorem memoryFinalFrontier_canonical {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {loc : MemLoc} {message : MemoryMsg (ZMod p)}
    (present : memoryFinalFrontier witness loc = some message) :
    MemoryMsg.locOf message = loc ∧ MemoryBoundary.CanonicalSpec message := by
  have member := List.mem_filter.mp (List.mem_of_head? present)
  exact ⟨of_decide_eq_true member.2, final_records_canonical witness constraints balanced _ member.1⟩

/-- The authenticated initial inventory supplies the generic timed engine's complete live-memory
invariant at genesis. The trajectory need only start at the configured image state; no future
execution, Memory truth, or caller-supplied semantic boundary binding is assumed. -/
theorem memoryInitialFrontier_liveOK {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (timeline : Timeline)
    (initial : trajectory 0 = some image.initialSailState) :
    LiveOKG trajectory image.initialSailState timeline (timeline.start 0)
      (memoryInitialFrontier witness) := by
  intro loc message present
  obtain ⟨sameLoc, authentic⟩ := memoryInitialFrontier_authentic witness constraints balanced present
  have content := authentic.2.2.2.2.1
  have atStart : LocalValueAtG trajectory image.initialSailState timeline
      (MemoryMsg.locOf message) (timeline.start 0) message.value :=
    (localValueAtG_stepStart_iff initial).mpr content
  refine ⟨sameLoc, ⟨authentic.1, authentic.2.1, ?_⟩, ?_, ?_⟩
  · rw [authentic.2.2.1]
    by_cases zero : timeline.start 0 = 0
    · simpa only [zero] using atStart
    · simpa only [LocalValueAtG, microValueG, if_pos (Nat.pos_of_ne_zero zero)] using content
  · simpa only [sameLoc] using atStart
  · rw [authentic.2.2.1]
    exact Nat.zero_le _

end SP1Clean.Soundness.NativeCore
