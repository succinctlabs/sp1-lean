import SP1Clean.Soundness.HostLocalCoreRows
import SP1Clean.Soundness.LocalCoreTouches

/-! # Low-clock bounds from the full host Memory ledger

Original instruction and refresh pushes use constraints, Byte guarantees, and Program balance.
The wrapper's extra x12 push uses the same CPU clock checks. Auxiliary pushes remain in the
physical ledger and supply their own local clock bounds. Full record conservation then transfers
these bounds to predecessors; no instruction-only Memory balance is asserted.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((tables image source auxiliary).map (·.circuit.name)).Nodup}

private theorem wrapper_extra_bound
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (bytes : ∀ table ∈ (localWitness witness).tables,
      table.ChannelGuarantees (localWitness witness).data byteChannel.toRaw)
    (physical : Array (ZMod p)) (member : physical ∈ (hostCallTable witness).table)
    (real : (HostCallLedger.input (Environment.fromArray physical witness.data)).instruction.is_real = 1) :
    MemoryMsg.ClkBound (HostCallProjection.extraRead (Environment.fromArray physical witness.data)).pushed := by
  have prefixMem : physical.extract 0 (HostCallProjection.original (p := p)).width ∈
      (LocalCore.systemTable (localWitness witness) 3).table := by
    rw [hostCallTable_prefix]
    exact List.mem_map_of_mem member
  have same : syscallInstrsRow (localWitness witness).data
      (physical.extract 0 (HostCallProjection.original (p := p)).width) =
      (HostCallLedger.input (Environment.fromArray physical witness.data)).instruction :=
    HostCallProjection.input_prefix physical witness.data (localWitness witness).data
  have bounds := syscallInstrsRow_cpuState_bounds_of_component
    (LocalCore.systemTable (localWitness witness) 3) (localWitness witness).data
    (LocalCore.systemTable_component (localWitness witness) 3)
    (bytes _ (LocalCore.systemTable_mem (localWitness witness) 3)) prefixMem (by rw [same]; exact real)
  rw [same] at bounds
  exact MemoryMsg.clkBound_of_cpuState_bounds _ _ 1 1 (ZMod.val_one _) (by decide) bounds.1 bounds.2

private theorem wrapper_push_bound
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ (localWitness witness).tables,
      table.ChannelGuarantees (localWitness witness).data byteChannel.toRaw) :
    ∀ message ∈ producedMessages (wrapperMemory witness), MemoryMsg.ClkBound message := by
  intro message member
  rw [wrapperMemory, List.flatMap_map, producedMessages_flatMap] at member
  obtain ⟨physical, physicalMem, extra⟩ := List.mem_flatMap.mp member
  have checked := constraints _ (hostCallTable_mem witness) physical physicalMem
  rw [hostCallTable_component] at checked
  have binary := HostCallLedger.binary_of_constraints (Environment.fromArray physical witness.data) checked
  have flag := HostCallChip.writeFlag_binary
    (HostCallLedger.input (Environment.fromArray physical witness.data)).instruction.op_a_memory.prev_value
  have zero : signedVal (0 : ZMod p) = 0 := by simp [signedVal]
  rcases binary with inactive | real
  · simp [producedMessages, HostCallProjection.extraRead, HostCallChip.Inputs.read, inactive,
      zero] at extra
  · have bound := wrapper_extra_bound witness bytes physical physicalMem real
    rcases flag with disabled | enabled
    · simp [producedMessages, HostCallProjection.extraRead, HostCallChip.Inputs.read, disabled,
        zero] at extra
    · have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
      have gate : (HostCallProjection.extraRead (Environment.fromArray physical witness.data)).is_real = 1 := by
        simp only [HostCallProjection.extraRead, HostCallChip.Inputs.read, real, enabled, mul_one]
      have pos : signedVal (1 : ZMod p) = 1 := by
        rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
        norm_num
      have neg : signedVal (-1 : ZMod p) = -1 := by
        rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
        norm_num
      simp [producedMessages, gate, pos, neg] at extra
      exact extra ▸ bound

/-- Every physical interior push has a bounded low clock. The exact Memory decomposition
retains original rows, WRITE's x12 read-back and all auxiliary pushes; Memory balance is not assumed. -/
theorem memoryInterior_push_bound (valid : image.Valid)
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (program : (localWitness witness).BalancedChannel programChannel.toRaw)
    (extra : ∀ table ∈ auxiliaryTables witness,
      ∀ message ∈ producedMessages (typedTableInteractionsWith table witness.data memoryChannel),
        MemoryMsg.ClkBound message) :
    ∀ message ∈ producedMessages (memoryInterior witness), MemoryMsg.ClkBound message := by
  have originalBytes := localWitness_byte_of_guarantees witness bytes
  have original := LocalCore.memoryInterior_push_bound valid (localWitness witness)
    (localWitness_constraints witness constraints) originalBytes program
  have perm : (producedMessages (memoryInterior witness)).Perm
      (producedMessages (LocalCore.memoryInterior (localWitness witness) ++
        wrapperMemory witness ++ auxiliaryMemory witness)) :=
    ((memoryInterior_perm witness constraints).filter _).map _
  intro message member
  have selected := perm.mem_iff.mp member
  simp only [producedMessages_append, List.mem_append] at selected
  rcases selected with (old | wrapper) | auxiliary
  · exact original message old
  · exact wrapper_push_bound witness constraints originalBytes message wrapper
  · rw [auxiliaryMemory, producedMessages_flatMap] at auxiliary
    obtain ⟨table, tableMem, emitted⟩ := List.mem_flatMap.mp auxiliary
    exact extra table tableMem message emitted

end SP1Clean.Soundness.HostLocalCore
