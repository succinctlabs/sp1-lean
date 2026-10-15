import SP1Clean.Soundness.LocalCoreOrder
import SP1Clean.Soundness.LocalCoreRowBalance
import SP1Clean.Soundness.CoreTouches

/-! # Aligned touches of the local shard assembly

The checked image fixes register operands; the closed Byte channel fixes access windows and
timestamp differences. Every mixed execution row therefore admits paired Memory touches without
changing its State edge, fetch, or complete Memory multiset. Prior-record timestamp bounds remain
conditional in this local interface; `LocalCoreMemoryOrder` discharges them from Memory balance
and eliminates the actual refresh rows.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow AlignedFacts syscall_operands_of_committed halt_aligned syscall_aligned ordinary_aligned align_rows)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Every active physical syscall fetch belongs to the checked image. -/
theorem syscall_program_committed_of_balance {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    {physical : Array (ZMod p)} (member : physical ∈ (systemTable witness 3).table)
    (real : (syscallInstrsRow witness.data physical).is_real = 1) :
    Target.committedInROM (image.toGuestProgram valid)
      (rowOfMsg (SyscallInstrsChip.programMessage (syscallInstrsRow witness.data physical))) := by
  let row := syscallInstrsRow witness.data physical
  let message := SyscallInstrsChip.programMessage row
  let interaction := programChannel.pulledIfValue row.is_real message
  have emitted : interaction ∈ witness.interactionsWith programChannel.toRaw := by
    apply EnsembleWitness.mem_interactionsWith.mpr
    refine Or.inr ⟨systemTable witness 3, systemTable_mem witness 3, List.mem_flatMap.mpr ⟨physical, member, ?_⟩⟩
    rw [← typedInteractionValuesWith_raw,
      syscallInstrsRow_typedProgram_of_component _ witness.data (systemTable_component witness 3)]
    exact List.mem_cons_self
  exact program_pull_committed_of_balance valid witness constraints balanced message interaction emitted
    (by change -row.is_real = -1; rw [real]) rfl

/-- The complete local AIR authenticates every active physical syscall fetch. -/
theorem syscall_program_committed {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {physical : Array (ZMod p)} (member : physical ∈ (systemTable witness 3).table)
    (real : (syscallInstrsRow witness.data physical).is_real = 1) :
    Target.committedInROM (image.toGuestProgram valid)
      (rowOfMsg (SyscallInstrsChip.programMessage (syscallInstrsRow witness.data physical))) :=
  syscall_program_committed_of_balance valid witness constraints
    (balanced _ (by simp [ensemble, PublicVerifier.install, baseEnsemble, sp1Ensemble_channels])) member real

private theorem syscall_operands {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    {physical : Array (ZMod p)} (member : physical ∈ (systemTable witness 3).table)
    (real : (syscallInstrsRow witness.data physical).is_real = 1) :
    (syscallInstrsRow witness.data physical).op_a = 5 ∧
      (syscallInstrsRow witness.data physical).op_b = 10 ∧
      (syscallInstrsRow witness.data physical).op_c = 11 :=
  syscall_operands_of_committed _ _ (syscall_program_committed_of_balance valid witness constraints balanced member real)

private theorem ordinaryRows_aligned {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (balanced : witness.BalancedChannel programChannel.toRaw)
    {row : DecodedInstructionRow p} (member : row ∈ activeInstructionRows witness) :
    ∃ aligned, AlignedFacts aligned ((ExecutionRow.instruction row).facts witness.data) := by
  obtain ⟨decodedMem, real⟩ := List.mem_filter.mp member
  have active := of_decide_eq_true real
  have chipMem := mem_chip_of_mem_decodeInstructionTables decodedMem
  have checked := instructionRows_constraints witness constraints row decodedMem
  have byte := channelGuarantees_of_mem_decodeInstructionTables witness.data byteChannel.toRaw
    (instructionTables_aligned witness)
    (fun table member => bytes table (instructionTables_mem witness member)) row decodedMem
  have committed := instructionRows_program_committed_of_balance valid witness constraints balanced decodedMem active
  exact ordinary_aligned witness.data row chipMem active checked byte (image.toGuestProgram valid) committed

private theorem haltRows_aligned {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    {row : HaltChip.Inputs (ZMod p)} (member : row ∈ activeSystemRows (systemTable witness 2) (haltRow witness.data) (·.is_real)) :
    ∃ aligned, AlignedFacts aligned ((ExecutionRow.halt row).facts witness.data) := by
  obtain ⟨mapped, real⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have byte := bytes _ (systemTable_mem witness 2)
  exact halt_aligned _ (haltRow_cpuState_bounds_of_component _ witness.data (systemTable_component witness 2)
    byte physicalMem (of_decide_eq_true real))
    (haltRow_accessTimestamp_bounds_of_component _ witness.data (systemTable_component witness 2)
      byte physicalMem (of_decide_eq_true real))

private theorem syscallRows_aligned {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (balanced : witness.BalancedChannel programChannel.toRaw)
    {row : SyscallInstrsChip.Inputs (ZMod p)} (member : row ∈ activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real)) :
    ∃ aligned, AlignedFacts aligned ((ExecutionRow.syscall row).facts witness.data) := by
  obtain ⟨mapped, real⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have byte := bytes _ (systemTable_mem witness 3)
  exact syscall_aligned _ (syscallInstrsRow_cpuState_bounds_of_component _ witness.data (systemTable_component witness 3)
    byte physicalMem (of_decide_eq_true real))
    (syscallInstrsRow_accessTimestamp_bounds_of_component _ witness.data (systemTable_component witness 3)
      byte physicalMem (of_decide_eq_true real))
    (syscall_operands valid witness constraints balanced physicalMem (of_decide_eq_true real))

/-- Alignment needs constraints, Byte guarantees, and Program balance. The enclosing assembly
may retain additional host accesses in its own Memory ledger. -/
theorem executionRows_aligned_of_channels {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (balanced : witness.BalancedChannel programChannel.toRaw)
    {row : ExecutionRow p} (member : row ∈ executionRows witness) :
    ∃ aligned, AlignedFacts aligned (row.facts witness.data) := by
  simp only [executionRows, List.mem_append, List.mem_map] at member
  rcases member with (⟨decoded, member, rfl⟩ | ⟨halt, member, rfl⟩) | ⟨syscall, member, rfl⟩
  · exact ordinaryRows_aligned valid witness constraints bytes balanced member
  · exact haltRows_aligned witness bytes member
  · exact syscallRows_aligned valid witness constraints bytes balanced member

/-- All active event kinds admit aligned touches from raw constraints, balance, and a checked image. -/
theorem executionRows_aligned {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : ExecutionRow p} (member : row ∈ executionRows witness) :
    ∃ aligned, AlignedFacts aligned (row.facts witness.data) :=
  executionRows_aligned_of_channels valid witness constraints
    (fun table member => ((finishedChannel_guarantees image source witness constraints balanced).2 table member).1)
    (balanced _ (by simp [ensemble, PublicVerifier.install, baseEnsemble, sp1Ensemble_channels])) member

/-- Every original interior push has a bounded low clock before any Memory-balance or
received-value premise. This includes active syscall writes and actual refresh records. -/
theorem memoryInterior_push_bound {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (balanced : witness.BalancedChannel programChannel.toRaw) :
    ∀ message ∈ producedMessages (memoryInterior witness), MemoryMsg.ClkBound message := by
  intro message member
  have selected : message ∈ Multiset.filter (fun m => MemoryMsg.locOf m = MemoryMsg.locOf message)
      (↑(producedMessages (memoryInterior witness)) : Multiset _) :=
    Multiset.mem_filter.mpr ⟨Multiset.mem_coe.mpr member, rfl⟩
  rw [← (executionRows_memory_projection witness constraints (MemoryMsg.locOf message)).1] at selected
  rcases Multiset.mem_add.mp selected with event | refresh
  · obtain ⟨row, rowMem, push, _⟩ := mem_pushesAt.mp event
    obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp rowMem
    obtain ⟨aligned, facts⟩ := executionRows_aligned_of_channels valid witness constraints bytes balanced eventMem
    exact facts.pushBound message (facts.memory.pushes.mem_iff.mpr push)
  · obtain ⟨pair, pairMem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp (Multiset.mem_filter.mp refresh).1)
    obtain ⟨row, rowMem, pairMem⟩ := List.mem_flatMap.mp pairMem
    obtain rfl := List.mem_singleton.mp pairMem
    obtain ⟨mapped, real⟩ := List.mem_filter.mp rowMem
    obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
    exact (memoryBump_pushedMessage_clkFacts_of_component _ witness.data (systemTable_component witness 0)
      (systemTable_constraints witness constraints 0) (bytes _ (systemTable_mem witness 0))
      physicalMem (of_decide_eq_true real)).1

/-- One assembly statement: an exhaustive State order and aligned, ledger-preserving Memory rows.
Instruction cases, system-table positions, and per-row touch permutations are internal. -/
theorem ordered_aligned_rows {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ (ordered : List (ExecutionRow p)) (rows : List (RowFacts p)),
      ordered.Perm (executionRows witness) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered ∧
      List.Forall₂ AlignedFacts rows (ordered.map (ExecutionRow.facts witness.data)) ∧
      ∀ loc, optMS (memoryInitialFrontier witness loc) + pushesAt rows loc +
          Multiset.filter (fun message => MemoryMsg.locOf message = loc)
            (↑((memoryRefreshes witness).map Prod.snd) : Multiset _) =
        optMS (memoryFinalFrontier witness loc) + pullsAt rows loc +
          Multiset.filter (fun message => MemoryMsg.locOf message = loc)
            (↑((memoryRefreshes witness).map Prod.fst) : Multiset _) := by
  obtain ⟨ordered, exhaustive, walk⟩ := executionRows_ordered witness constraints balanced
  obtain ⟨rows, alignment⟩ := align_rows witness.data ordered
    (fun row member => executionRows_aligned valid witness constraints balanced (exhaustive.mem_iff.mp member))
  exact ⟨ordered, rows, exhaustive, walk, alignment,
    memory_balance_of_row_projection witness constraints balanced ordered exhaustive rows
      (alignment.imp (fun _ _ aligned => aligned.memory))⟩

end SP1Clean.Soundness.LocalCore
