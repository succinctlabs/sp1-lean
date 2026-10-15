import SP1Clean.Soundness.LocalCoreState
import SP1Clean.Soundness.StateChronology

/-! # Clock ordering of the local shard assembly

Raw constraints and channel balance order every active ordinary, HALT, and syscall row between
the public endpoints. The physical StateBump rows supply canonicalization, and cancel internally.
The order retains every occurrence, including arbitrarily interleaved syscall rows.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow activeSystemRows_member syscall_halt_binary halt_advancing syscall_advancing)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem instructionRows_advancing {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (channels : OrderingChannels witness)
    {row : DecodedInstructionRow p} (member : row ∈ activeInstructionRows witness) :
    StateChronology.Advancing ((ExecutionRow.instruction row).edge witness.data) ∧
      StateMsg.timeNat ((ExecutionRow.instruction row).edge witness.data).2 =
        StateMsg.timeNat ((ExecutionRow.instruction row).edge witness.data).1 + (ExecutionRow.instruction row).duration := by
  obtain ⟨decodedMem, real⟩ := List.mem_filter.mp member
  have active := of_decide_eq_true real
  have byte := channelGuarantees_of_mem_decodeInstructionTables witness.data byteChannel.toRaw
    (instructionTables_aligned witness)
    (fun table tableMem => channels.byte table (instructionTables_mem witness tableMem)) row decodedMem
  have step := row.stateTimeStep_of_byteGuarantees witness.data (witness.tables.drop 7) decodedMem byte active
  refine ⟨⟨?_, rfl, ?_⟩, step⟩
  · change StateMsg.timeNat (decodedStateEdge witness.data row).1 <
      StateMsg.timeNat (decodedStateEdge witness.data row).2
    rw [step]; omega
  · exact supportedChip_statePcClassShape row.chip (mem_chip_of_mem_decodeInstructionTables decodedMem)
      witness.data row.physical byte active

private theorem haltRows_advancing {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (channels : OrderingChannels witness)
    {row : HaltChip.Inputs (ZMod p)} (member : row ∈ activeSystemRows (systemTable witness 2) (haltRow witness.data) (·.is_real)) :
    StateChronology.Advancing ((ExecutionRow.halt row).edge witness.data) ∧
      StateMsg.timeNat ((ExecutionRow.halt row).edge witness.data).2 =
        StateMsg.timeNat ((ExecutionRow.halt row).edge witness.data).1 + (ExecutionRow.halt row).duration := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := activeSystemRows_member _ _ _ member
  exact halt_advancing _ (haltRow_cpuState_bounds_of_component _ witness.data (systemTable_component witness 2)
    (channels.byte _ (systemTable_mem witness 2)) physicalMem real)

private theorem syscallRows_advancing {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness)
    {row : SyscallInstrsChip.Inputs (ZMod p)} (member : row ∈ activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real)) :
    StateChronology.Advancing ((ExecutionRow.syscall row).edge witness.data) ∧
      StateMsg.timeNat ((ExecutionRow.syscall row).edge witness.data).2 =
        StateMsg.timeNat ((ExecutionRow.syscall row).edge witness.data).1 + (ExecutionRow.syscall row).duration := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := activeSystemRows_member _ _ _ member
  exact syscall_advancing _ (syscallInstrsRow_cpuState_bounds_of_component _ witness.data (systemTable_component witness 3)
    (channels.byte _ (systemTable_mem witness 3)) physicalMem real)
    (syscall_halt_binary _ witness.data (systemTable_component witness 3) (systemTable_constraints witness constraints 3) physicalMem)
    real (syscallInstrsRow_pcArm_spec_of_component _ witness.data (systemTable_component witness 3)
      (systemTable_constraints witness constraints 3) physicalMem)

/-- Clock progress and the PC preservation/range-check dichotomy come from each physical row. -/
theorem executionRows_advancing_of_orderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness)
    {row : ExecutionRow p} (member : row ∈ executionRows witness) :
    StateChronology.Advancing (row.edge witness.data) ∧
      StateMsg.timeNat (row.edge witness.data).2 =
        StateMsg.timeNat (row.edge witness.data).1 + row.duration := by
  simp only [executionRows, List.mem_append, List.mem_map] at member
  rcases member with (⟨decoded, member, rfl⟩ | ⟨halt, member, rfl⟩) | ⟨syscall, member, rfl⟩
  · exact instructionRows_advancing witness channels member
  · exact haltRows_advancing witness channels member
  · exact syscallRows_advancing witness constraints channels member

private theorem stateBumps_spec {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness)
    {row : StateBumpChip.Inputs (ZMod p)} (member : row ∈ stateBumps witness) :
    StateBumpChip.Spec row ∧ row.is_real = 1 := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := activeSystemRows_member _ _ _ member
  exact ⟨stateBumpTable_spec_of_component _ witness.data (systemTable_component witness 1)
    (systemTable_constraints witness constraints 1)
    (channels.byte _ (systemTable_mem witness 1)) _ physicalMem, real⟩

/-- Both endpoints of every active event have the bounds needed for semantic canonicalization. -/
theorem executionRows_good_of_orderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness)
    {row : ExecutionRow p} (member : row ∈ executionRows witness) :
    StateChronology.Good (row.edge witness.data).1 ∧ StateChronology.Good (row.edge witness.data).2 := by
  have bounds := (public_contract_of_byte witness channels.sourceChecks channels.verifierByte).1
  have initial := initialBoundaryStateMessage_bounds witness.publicInput bounds
  have final := finalBoundaryStateMessage_bounds witness.publicInput bounds
  exact (StateChronology.good_and_bumps_cancel _ _ _ _ _ (state_endpointBalanced_of_orderingChannels witness constraints channels)
    ⟨initial.1, initial.2.2.2⟩ ⟨final.1, final.2.2.2⟩
    (fun _ member => (executionRows_advancing_of_orderingChannels witness constraints channels member).1)
    (fun _ member => stateBumps_spec witness constraints channels member)).1 row member

/-- Constraints and balance construct an exhaustive ordering of the complete mixed inventory.
No ordering, canonicalization, or system-row inactivity premise is supplied by the caller. -/
theorem executionRows_ordered_of_orderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness) :
    ∃ ordered : List (ExecutionRow p), ordered.Perm (executionRows witness) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered := by
  have bounds := (public_contract_of_byte witness channels.sourceChecks channels.verifierByte).1
  have initial := initialBoundaryStateMessage_bounds witness.publicInput bounds
  have final := finalBoundaryStateMessage_bounds witness.publicInput bounds
  obtain ⟨ordered, walk, exhaustive⟩ := StateChronology.exhaustiveTrail _ _ _ _ _
    (state_endpointBalanced_of_orderingChannels witness constraints channels)
    ⟨initial.1, initial.2.2.2⟩ ⟨final.1, final.2.2.2⟩
    (fun _ member => (executionRows_advancing_of_orderingChannels witness constraints channels member).1)
    (fun _ member => stateBumps_spec witness constraints channels member)
  rw [canonState_eq_self initial.2.1 initial.2.2.1 initial.2.2.2.1,
    canonState_eq_self final.2.1 final.2.2.1 final.2.2.2.1] at walk
  exact ⟨ordered, exhaustive, walk⟩

/-- Every event in an exhaustive State walk keeps the incoming clock residue and its exact duration. -/
theorem ordered_rows_timing_of_orderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness)
    (ordered : List (ExecutionRow p)) (exhaustive : ordered.Perm (executionRows witness))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered) :
    ∀ row ∈ ordered,
      StateMsg.timeNat (row.edge witness.data).1 % 8 =
        StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) % 8 ∧
      StateMsg.timeNat (row.edge witness.data).2 = StateMsg.timeNat (row.edge witness.data).1 + row.duration := by
  have steps : ∀ row ∈ ordered,
      StateMsg.timeNat (row.canonEdge witness.data).2 =
        StateMsg.timeNat (row.canonEdge witness.data).1 + row.duration := by
    intro row member
    have good := executionRows_good_of_orderingChannels witness constraints channels (exhaustive.mem_iff.mp member)
    dsimp only [ExecutionRow.canonEdge]
    rw [timeNat_canonState good.1.1, timeNat_canonState good.2.1]
    exact (executionRows_advancing_of_orderingChannels witness constraints channels (exhaustive.mem_iff.mp member)).2
  have aligned := statePullAlign8_of_durations (ExecutionRow.canonEdge witness.data) ExecutionRow.duration walk
    (fun row _ => by cases row <;> norm_num [ExecutionRow.duration]) steps
  intro row member
  have good := executionRows_good_of_orderingChannels witness constraints channels (exhaustive.mem_iff.mp member)
  have align := aligned row member
  dsimp only [ExecutionRow.canonEdge] at align
  rw [timeNat_canonState good.1.1] at align
  exact ⟨align, (executionRows_advancing_of_orderingChannels witness constraints channels (exhaustive.mem_iff.mp member)).2⟩

/-- The complete witness supplies the smaller State/Byte chronology interface. -/
theorem executionRows_advancing {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : ExecutionRow p} (member : row ∈ executionRows witness) :
    StateChronology.Advancing (row.edge witness.data) ∧
      StateMsg.timeNat (row.edge witness.data).2 =
        StateMsg.timeNat (row.edge witness.data).1 + row.duration :=
  executionRows_advancing_of_orderingChannels witness constraints
    (orderingChannels_of_balanced witness constraints balanced) member

/-- The complete witness supplies the smaller State/Byte chronology interface. -/
theorem executionRows_good {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : ExecutionRow p} (member : row ∈ executionRows witness) :
    StateChronology.Good (row.edge witness.data).1 ∧ StateChronology.Good (row.edge witness.data).2 :=
  executionRows_good_of_orderingChannels witness constraints
    (orderingChannels_of_balanced witness constraints balanced) member

/-- The complete witness supplies the smaller State/Byte chronology interface. -/
theorem executionRows_ordered {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ ordered : List (ExecutionRow p), ordered.Perm (executionRows witness) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered :=
  executionRows_ordered_of_orderingChannels witness constraints
    (orderingChannels_of_balanced witness constraints balanced)

/-- The complete witness supplies the smaller State/Byte chronology interface. -/
theorem ordered_rows_timing {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (ordered : List (ExecutionRow p)) (exhaustive : ordered.Perm (executionRows witness))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered) :
    ∀ row ∈ ordered,
      StateMsg.timeNat (row.edge witness.data).1 % 8 =
        StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) % 8 ∧
      StateMsg.timeNat (row.edge witness.data).2 = StateMsg.timeNat (row.edge witness.data).1 + row.duration :=
  ordered_rows_timing_of_orderingChannels witness constraints
    (orderingChannels_of_balanced witness constraints balanced) ordered exhaustive walk

end SP1Clean.Soundness.LocalCore
