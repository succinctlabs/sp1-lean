import SP1Clean.Soundness.NativeCoreOrder
import SP1Clean.Soundness.NativeCoreRowBalance
import SP1Clean.Soundness.CoreTouches

/-! # Aligned touches of the authenticated native core

The checked image fixes register operands; the closed Byte channel fixes access windows and
timestamp differences. Every mixed execution row therefore admits paired Memory touches without
changing its State edge, fetch, or complete Memory multiset. Prior-record timestamp bounds remain
conditional in this local interface; `NativeCoreMemoryOrder` discharges them from Memory balance
and eliminates the actual refresh rows.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Every active physical syscall fetch belongs to the checked image. -/
theorem syscall_program_committed {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
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
  exact program_pull_committed valid witness constraints balanced message interaction emitted
    (by change -row.is_real = -1; rw [real]) rfl

private theorem syscall_operands {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {physical : Array (ZMod p)} (member : physical ∈ (systemTable witness 3).table)
    (real : (syscallInstrsRow witness.data physical).is_real = 1) :
    (syscallInstrsRow witness.data physical).op_a = 5 ∧
      (syscallInstrsRow witness.data physical).op_b = 10 ∧
      (syscallInstrsRow witness.data physical).op_c = 11 :=
  syscall_operands_of_committed _ _ (syscall_program_committed valid witness constraints balanced member real)

private theorem ordinaryRows_aligned {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : row ∈ activeInstructionRows witness) :
    ∃ aligned, AlignedFacts aligned ((ExecutionRow.instruction row).facts witness.data) := by
  obtain ⟨decodedMem, real⟩ := List.mem_filter.mp member
  have active := of_decide_eq_true real
  have chipMem := mem_chip_of_mem_decodeInstructionTables decodedMem
  have checked := instructionRows_constraints witness constraints row decodedMem
  have byte := (instructionRows_finished_guarantees witness constraints balanced decodedMem).1
  have committed := instructionRows_program_committed valid witness constraints balanced decodedMem active
  exact ordinary_aligned witness.data row chipMem active checked byte (image.toGuestProgram valid) committed

private theorem haltRows_aligned {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)} (member : row ∈ activeSystemRows (systemTable witness 2) (haltRow witness.data) (·.is_real)) :
    ∃ aligned, AlignedFacts aligned ((ExecutionRow.halt row).facts witness.data) := by
  obtain ⟨mapped, real⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have byte := ((finishedChannel_guarantees image witness constraints balanced).2 _ (systemTable_mem witness 2)).1
  exact halt_aligned _ (haltRow_cpuState_bounds_of_component _ witness.data (systemTable_component witness 2)
    byte physicalMem (of_decide_eq_true real))
    (haltRow_accessTimestamp_bounds_of_component _ witness.data (systemTable_component witness 2)
      byte physicalMem (of_decide_eq_true real))

private theorem syscallRows_aligned {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : SyscallInstrsChip.Inputs (ZMod p)} (member : row ∈ activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real)) :
    ∃ aligned, AlignedFacts aligned ((ExecutionRow.syscall row).facts witness.data) := by
  obtain ⟨mapped, real⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have byte := ((finishedChannel_guarantees image witness constraints balanced).2 _ (systemTable_mem witness 3)).1
  exact syscall_aligned _ (syscallInstrsRow_cpuState_bounds_of_component _ witness.data (systemTable_component witness 3)
    byte physicalMem (of_decide_eq_true real))
    (syscallInstrsRow_accessTimestamp_bounds_of_component _ witness.data (systemTable_component witness 3)
      byte physicalMem (of_decide_eq_true real))
    (syscall_operands valid witness constraints balanced physicalMem (of_decide_eq_true real))

/-- All active event kinds admit aligned touches from raw constraints, balance, and a checked image. -/
theorem executionRows_aligned {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : ExecutionRow p} (member : row ∈ executionRows witness) :
    ∃ aligned, AlignedFacts aligned (row.facts witness.data) := by
  simp only [executionRows, List.mem_append, List.mem_map] at member
  rcases member with (⟨decoded, member, rfl⟩ | ⟨halt, member, rfl⟩) | ⟨syscall, member, rfl⟩
  · exact ordinaryRows_aligned valid witness constraints balanced member
  · exact haltRows_aligned witness constraints balanced member
  · exact syscallRows_aligned valid witness constraints balanced member

/-- One assembly statement: an exhaustive State order and aligned, ledger-preserving Memory rows.
Instruction cases, system-table positions, and per-row touch permutations are internal. -/
theorem ordered_aligned_rows {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
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

end SP1Clean.Soundness.NativeCore
