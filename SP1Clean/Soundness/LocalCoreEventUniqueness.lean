import SP1Clean.Soundness.LocalCoreOrder

/-! # Unique event clocks from the actual local State ledger

Every active ordinary, HALT, and syscall occurrence belongs to the exhaustive State walk and
strictly advances its clock. Their incoming clocks are therefore distinct. Padding is absent
from this inventory by the physical decoder, not by an additional execution premise.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat Channels Semantics Model.Core NativeCore

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Constraints and balance rule out two active events at the same natural clock. -/
theorem executionRows_times_nodup_of_orderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness) :
    ((executionRows witness).map fun row => StateMsg.timeNat (row.edge witness.data).1).Nodup := by
  obtain ⟨ordered, exhaustive, walk⟩ := executionRows_ordered_of_orderingChannels witness constraints channels
  have times (row : ExecutionRow p) (member : row ∈ ordered) :
      StateMsg.timeNat (row.canonEdge witness.data).1 = StateMsg.timeNat (row.edge witness.data).1 ∧
      StateMsg.timeNat (row.canonEdge witness.data).2 = StateMsg.timeNat (row.edge witness.data).2 := by
    have good := executionRows_good_of_orderingChannels witness constraints channels (exhaustive.mem_iff.mp member)
    exact ⟨timeNat_canonState good.1.1, timeNat_canonState good.2.1⟩
  have unique := RankedGrounding.sourceRanks_nodup_of_isWalk
    (ExecutionRow.canonEdge witness.data) StateMsg.timeNat walk (fun row member => by
      rw [(times row member).1, (times row member).2]
      exact (executionRows_advancing_of_orderingChannels witness constraints channels (exhaustive.mem_iff.mp member)).1.1)
  have same := List.map_congr_left (fun row member => (times row member).1)
  rw [same] at unique
  exact (exhaustive.map _).nodup_iff.mp unique

/-- The handoff's two field limbs are unique even when the low clock crosses a limb boundary. -/
theorem executionRows_clocks_nodup_of_orderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness) :
    ((executionRows witness).map fun row =>
      ((row.edge witness.data).1.clk_high, (row.edge witness.data).1.clk_low)).Nodup := by
  have unique := executionRows_times_nodup_of_orderingChannels witness constraints channels
  have mapped : (((executionRows witness).map fun row =>
      ((row.edge witness.data).1.clk_high, (row.edge witness.data).1.clk_low)).map
      (fun clock => clkNat clock.1 clock.2)).Nodup := by
    simpa only [List.map_map, Function.comp_def, StateMsg.timeNat] using unique
  exact mapped.of_map _

/-- Complete channel balance supplies the State/Byte ordering interface. -/
theorem executionRows_times_nodup {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((executionRows witness).map fun row => StateMsg.timeNat (row.edge witness.data).1).Nodup :=
  executionRows_times_nodup_of_orderingChannels witness constraints
    (orderingChannels_of_balanced witness constraints balanced)

/-- Every exhaustive CPU walk is strictly ordered by the original incoming event clocks.
Only State balance and Byte guarantees are projected; host Memory effects can remain installed. -/
theorem ordered_times_pairwise {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness)
    {ordered : List (ExecutionRow p)} (exhaustive : ordered.Perm (executionRows witness))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered) :
    (ordered.map fun row => StateMsg.timeNat (row.edge witness.data).1).Pairwise (· < ·) := by
  have times (row : ExecutionRow p) (member : row ∈ ordered) :
      StateMsg.timeNat (row.canonEdge witness.data).1 = StateMsg.timeNat (row.edge witness.data).1 ∧
      StateMsg.timeNat (row.canonEdge witness.data).2 = StateMsg.timeNat (row.edge witness.data).2 := by
    have good := executionRows_good_of_orderingChannels witness constraints channels (exhaustive.mem_iff.mp member)
    exact ⟨timeNat_canonState good.1.1, timeNat_canonState good.2.1⟩
  have sorted := RankedGrounding.sourceRanks_pairwise_of_isWalk
    (ExecutionRow.canonEdge witness.data) StateMsg.timeNat walk (fun row member => by
      rw [(times row member).1, (times row member).2]
      exact (executionRows_advancing_of_orderingChannels witness constraints channels (exhaustive.mem_iff.mp member)).1.1)
  rwa [List.map_congr_left (fun row member => (times row member).1)] at sorted

/-- Complete channel balance supplies the State/Byte ordering interface. -/
theorem executionRows_clocks_nodup {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((executionRows witness).map fun row =>
      ((row.edge witness.data).1.clk_high, (row.edge witness.data).1.clk_low)).Nodup :=
  executionRows_clocks_nodup_of_orderingChannels witness constraints
    (orderingChannels_of_balanced witness constraints balanced)

end SP1Clean.Soundness.LocalCore
