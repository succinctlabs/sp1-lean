import SP1Clean.Soundness.SP1Ensemble
import ToClean.Air.TableBuild

/-!
# Every table speaks only on the ensemble's channels

Clean's `Ensemble` carries a `channels` list but does not *constrain* its components to it — nothing
in the structure says a table cannot emit on a channel the ensemble never declared. For `sp1Ensemble`
that constraint holds, and this file proves it.

The fact is load-bearing for any argument that reads the whole ledger at once and then asks which
bus a given key came from. `Interaction.toAccess` puts the emitting channel's own `name` in the key,
so a key already determines a channel *name*; turning that into a channel needs to know the name
ranges over a finite set with no collisions, which is exactly what this file plus
`Model/Channels.lean`'s per-pair distinctness supplies.

Each chip reduces the same way: `circuit.channels` is `channelsWithGuarantees ++
channelsWithRequirements`, the guarantee half goes through the chip's own `elaborated` instance
(which is where the six chips with a *derived* elaborated — Jal, Jalr, Branch, UType, LoadX0,
StoreByte — get theirs computed rather than declared), and the requirement half is a literal field.
Both are definitional, so the whole sweep is `rfl` plus `circuit_norm`.
-/

namespace SP1Clean.Soundness

open SP1Clean
open Air.Flat
open Circuit
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel exitChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## The 25 instruction chips -/

private theorem addChip_channels_subset :
    (AddChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddChip.circuit (p := p)).channelsWithGuarantees =
      (AddChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem addiChip_channels_subset :
    (AddiChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddiChip.circuit (p := p)).channelsWithGuarantees =
      (AddiChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddiChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem addwChip_channels_subset :
    (AddwChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddwChip.circuit (p := p)).channelsWithGuarantees =
      (AddwChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddwChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem subChip_channels_subset :
    (SubChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (SubChip.circuit (p := p)).channelsWithGuarantees =
      (SubChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (SubChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem subwChip_channels_subset :
    (SubwChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (SubwChip.circuit (p := p)).channelsWithGuarantees =
      (SubwChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (SubwChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem bitwiseChip_channels_subset :
    (BitwiseChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (BitwiseChip.circuit (p := p)).channelsWithGuarantees =
      (BitwiseChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (BitwiseChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem ltChip_channels_subset :
    (LtChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LtChip.circuit (p := p)).channelsWithGuarantees =
      (LtChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LtChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem shiftLeftChip_channels_subset :
    (ShiftLeftChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ShiftLeftChip.circuit (p := p)).channelsWithGuarantees =
      (ShiftLeftChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (ShiftLeftChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem shiftRightChip_channels_subset :
    (ShiftRightChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ShiftRightChip.circuit (p := p)).channelsWithGuarantees =
      (ShiftRightChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (ShiftRightChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem jalChip_channels_subset :
    (JalChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (JalChip.circuit (p := p)).channelsWithGuarantees =
      (JalChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (JalChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem jalrChip_channels_subset :
    (JalrChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (JalrChip.circuit (p := p)).channelsWithGuarantees =
      (JalrChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (JalrChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem branchChip_channels_subset :
    (BranchChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (BranchChip.circuit (p := p)).channelsWithGuarantees =
      (BranchChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (BranchChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem uTypeChip_channels_subset :
    (UTypeChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (UTypeChip.circuit (p := p)).channelsWithGuarantees =
      (UTypeChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (UTypeChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem loadByteChip_channels_subset :
    (LoadByteChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadByteChip.circuit (p := p)).channelsWithGuarantees =
      (LoadByteChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadByteChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem loadHalfChip_channels_subset :
    (LoadHalfChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadHalfChip.circuit (p := p)).channelsWithGuarantees =
      (LoadHalfChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadHalfChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem loadWordChip_channels_subset :
    (LoadWordChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadWordChip.circuit (p := p)).channelsWithGuarantees =
      (LoadWordChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadWordChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem loadDoubleChip_channels_subset :
    (LoadDoubleChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadDoubleChip.circuit (p := p)).channelsWithGuarantees =
      (LoadDoubleChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadDoubleChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem loadX0Chip_channels_subset :
    (LoadX0Chip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadX0Chip.circuit (p := p)).channelsWithGuarantees =
      (LoadX0Chip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadX0Chip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem storeByteChip_channels_subset :
    (StoreByteChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreByteChip.circuit (p := p)).channelsWithGuarantees =
      (StoreByteChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreByteChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem storeHalfChip_channels_subset :
    (StoreHalfChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreHalfChip.circuit (p := p)).channelsWithGuarantees =
      (StoreHalfChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreHalfChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem storeWordChip_channels_subset :
    (StoreWordChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreWordChip.circuit (p := p)).channelsWithGuarantees =
      (StoreWordChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreWordChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem storeDoubleChip_channels_subset :
    (StoreDoubleChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreDoubleChip.circuit (p := p)).channelsWithGuarantees =
      (StoreDoubleChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreDoubleChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem mulChip_channels_subset :
    (MulChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MulChip.circuit (p := p)).channelsWithGuarantees =
      (MulChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (MulChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem divRemChip_channels_subset :
    (DivRemChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (DivRemChip.circuit (p := p)).channelsWithGuarantees =
      (DivRemChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (DivRemChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem aluX0Chip_channels_subset :
    (AluX0Chip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AluX0Chip.circuit (p := p)).channelsWithGuarantees =
      (AluX0Chip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AluX0Chip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- **Every instruction chip stays on the ensemble's four buses.** -/
theorem sp1Tables_channels_subset : ∀ c ∈ sp1Tables (p := p),
    c.circuit.channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro c hc
  fin_cases hc
  exacts [addChip_channels_subset, addiChip_channels_subset, addwChip_channels_subset, subChip_channels_subset, subwChip_channels_subset, bitwiseChip_channels_subset, ltChip_channels_subset, shiftLeftChip_channels_subset, shiftRightChip_channels_subset, jalChip_channels_subset, jalrChip_channels_subset, branchChip_channels_subset, uTypeChip_channels_subset, loadByteChip_channels_subset, loadHalfChip_channels_subset, loadWordChip_channels_subset, loadDoubleChip_channels_subset, loadX0Chip_channels_subset, storeByteChip_channels_subset, storeHalfChip_channels_subset, storeWordChip_channels_subset, storeDoubleChip_channels_subset, mulChip_channels_subset, divRemChip_channels_subset, aluX0Chip_channels_subset]

/-! ## The 28 boundary/provider tables, and the verifier row -/

private theorem u8RangeProvider_channels_subset :
    (ByteChip.U8Range.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.U8Range.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.U8Range.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem msbProvider_channels_subset :
    (ByteChip.MSB.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.MSB.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.MSB.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem andProvider_channels_subset :
    (ByteChip.AndByte.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.AndByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.AndByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem orProvider_channels_subset :
    (ByteChip.OrByte.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.OrByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.OrByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem xorProvider_channels_subset :
    (ByteChip.XorByte.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.XorByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.XorByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem ltuProvider_channels_subset :
    (ByteChip.Ltu.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.Ltu.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.Ltu.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem programProvider_channels_subset :
    (ProgramProviderChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ProgramProviderChip.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ProgramProviderChip.circuit (p := p)).channelsWithRequirements = [programChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem memoryInitProvider_channels_subset :
    (MemoryProviderChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryProviderChip.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (MemoryProviderChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem memoryFinalizeProvider_channels_subset :
    (MemoryFinalizeChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryFinalizeChip.circuit (p := p)).channelsWithGuarantees = [memoryChannel.toRaw] from rfl,
    show (MemoryFinalizeChip.circuit (p := p)).channelsWithRequirements = [] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem memoryBumpProvider_channels_subset :
    (MemoryBumpChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryBumpChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, memoryChannel.toRaw] from rfl,
    show (MemoryBumpChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem stateBumpProvider_channels_subset :
    (StateBumpChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StateBumpChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, stateChannel.toRaw] from rfl,
    show (StateBumpChip.circuit (p := p)).channelsWithRequirements = [] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem rangeProvider_channels_subset (width : RangeChip.Width) :
    (RangeChip.circuitFor (p := p) width).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (RangeChip.circuitFor (p := p) width).channelsWithGuarantees = [] from rfl,
    show (RangeChip.circuitFor (p := p) width).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem haltProvider_channels_subset :
    (HaltChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (HaltChip.circuit (p := p)).channelsWithGuarantees
      = [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
         exitChannel.toRaw] from rfl,
    show (HaltChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem verifier_channels_subset :
    (sp1StateVerifier (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (sp1StateVerifier (p := p)).channelsWithGuarantees
      = [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw] from rfl,
    show (sp1StateVerifier (p := p)).channelsWithRequirements = [] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- **Every boundary/provider table stays on the ensemble's five buses.** -/
theorem sp1ProviderTables_channels_subset : ∀ c ∈ sp1ProviderTables (p := p),
    c.circuit.channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro c hc
  rw [sp1ProviderTables_explicit, List.mem_append, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [u8RangeProvider_channels_subset, msbProvider_channels_subset,
      andProvider_channels_subset, orProvider_channels_subset,
      xorProvider_channels_subset, ltuProvider_channels_subset]
  · rw [sp1RangeProviderTables] at hc
    obtain ⟨width, -, rfl⟩ := List.mem_map.mp hc
    exact rangeProvider_channels_subset width
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [programProvider_channels_subset, memoryInitProvider_channels_subset,
      memoryFinalizeProvider_channels_subset, memoryBumpProvider_channels_subset,
      stateBumpProvider_channels_subset, haltProvider_channels_subset]

/-- **The ensemble's tables speak only on the ensemble's channels** — verifier row included.

Clean's `Ensemble` does not impose this, so it is a fact about `sp1Ensemble` specifically. -/
theorem sp1Ensemble_allTables_channels_subset :
    ∀ component ∈ (sp1Ensemble (p := p)).allTables,
      component.circuit.channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro component hc
  rw [Ensemble.allTables, List.mem_cons, sp1Ensemble_tables, List.mem_append] at hc
  rcases hc with rfl | hc | hc
  · exact verifier_channels_subset
  · exact sp1Tables_channels_subset _ hc
  · exact sp1ProviderTables_channels_subset _ hc

/-- **The five buses have five distinct names**, so a channel name identifies its channel.

This is what turns `Interaction.toAccess`'s key — which carries the emitting channel's `name` — into
a statement about *which* channel produced an access. -/
theorem channel_eq_of_name_eq {c₁ c₂ : RawChannel (ZMod p)}
    (h₁ : c₁ ∈ (sp1Ensemble (p := p)).channels) (h₂ : c₂ ∈ (sp1Ensemble (p := p)).channels)
    (hname : c₁.name = c₂.name) : c₁ = c₂ := by
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | (exfalso
         revert hname
         simp only [Channel.toRaw_name, stateChannel, byteChannel, programChannel, memoryChannel,
           exitChannel]
         decide)


/-- **The five buses have five distinct kinds too**, so an access's `InteractionKind` identifies its
channel just as its name does. This is the form the ledger's kind-filter needs. -/
theorem channel_eq_of_kindOf_eq {c₁ c₂ : RawChannel (ZMod p)}
    (h₁ : c₁ ∈ (sp1Ensemble (p := p)).channels) (h₂ : c₂ ∈ (sp1Ensemble (p := p)).channels)
    (hkind : kindOf c₁.name = kindOf c₂.name) : c₁ = c₂ := by
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | (exfalso
         revert hkind
         simp [Channel.toRaw_name, stateChannel, byteChannel, programChannel, memoryChannel,
           exitChannel, kindOf])

/-- **The side condition `Model/CleanLedger.lean`'s kind-filter asks of a table**, discharged for
every table of this ensemble: an interaction whose kind matches a declared channel's *is* on that
channel. Both halves are already proved — the table emits only on the ensemble's channels, and those
five have five distinct kinds. -/
theorem interactions_channel_eq_of_kindOf (table : Table (ZMod p))
    (hcomponent : table.component ∈ (sp1Ensemble (p := p)).allTables)
    (channel : RawChannel (ZMod p)) (hchannel : channel ∈ (sp1Ensemble (p := p)).channels) :
    ∀ i ∈ table.interactions, kindOf i.channel.name = kindOf channel.name →
      i.channel = channel := by
  intro i hi hkind
  exact channel_eq_of_kindOf_eq
    (sp1Ensemble_allTables_channels_subset _ hcomponent
      (Air.Flat.Table.channel_mem_channels_of_mem_interactions table i hi))
    hchannel hkind

/-! ## Exit-channel silence of the non-halt tables

The Exit bus connects exactly two parties: the Halt table's gated hand-off pushes and the
state-boundary verifier's ungated `⟨exit_code⟩` pull.  These lemmas record the silent side,
component by component, reusing each subset lemma's channel-list incantation; the exit-channel
accounting layer (`Soundness/ExitAccounting.lean`) consumes them through the positional table
decompositions. -/

private theorem addChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (AddChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddChip.circuit (p := p)).channelsWithGuarantees =
      (AddChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem addiChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (AddiChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddiChip.circuit (p := p)).channelsWithGuarantees =
      (AddiChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddiChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem addwChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (AddwChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddwChip.circuit (p := p)).channelsWithGuarantees =
      (AddwChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddwChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem subChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (SubChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (SubChip.circuit (p := p)).channelsWithGuarantees =
      (SubChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (SubChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem subwChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (SubwChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (SubwChip.circuit (p := p)).channelsWithGuarantees =
      (SubwChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (SubwChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem bitwiseChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (BitwiseChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (BitwiseChip.circuit (p := p)).channelsWithGuarantees =
      (BitwiseChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (BitwiseChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem ltChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LtChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LtChip.circuit (p := p)).channelsWithGuarantees =
      (LtChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LtChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem shiftLeftChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ShiftLeftChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ShiftLeftChip.circuit (p := p)).channelsWithGuarantees =
      (ShiftLeftChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (ShiftLeftChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem shiftRightChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ShiftRightChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ShiftRightChip.circuit (p := p)).channelsWithGuarantees =
      (ShiftRightChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (ShiftRightChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem jalChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (JalChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (JalChip.circuit (p := p)).channelsWithGuarantees =
      (JalChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (JalChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem jalrChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (JalrChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (JalrChip.circuit (p := p)).channelsWithGuarantees =
      (JalrChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (JalrChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem branchChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (BranchChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (BranchChip.circuit (p := p)).channelsWithGuarantees =
      (BranchChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (BranchChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem uTypeChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (UTypeChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (UTypeChip.circuit (p := p)).channelsWithGuarantees =
      (UTypeChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (UTypeChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem loadByteChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LoadByteChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadByteChip.circuit (p := p)).channelsWithGuarantees =
      (LoadByteChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadByteChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem loadHalfChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LoadHalfChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadHalfChip.circuit (p := p)).channelsWithGuarantees =
      (LoadHalfChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadHalfChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem loadWordChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LoadWordChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadWordChip.circuit (p := p)).channelsWithGuarantees =
      (LoadWordChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadWordChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem loadDoubleChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LoadDoubleChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadDoubleChip.circuit (p := p)).channelsWithGuarantees =
      (LoadDoubleChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadDoubleChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem loadX0Chip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LoadX0Chip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadX0Chip.circuit (p := p)).channelsWithGuarantees =
      (LoadX0Chip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadX0Chip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem storeByteChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (StoreByteChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreByteChip.circuit (p := p)).channelsWithGuarantees =
      (StoreByteChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreByteChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem storeHalfChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (StoreHalfChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreHalfChip.circuit (p := p)).channelsWithGuarantees =
      (StoreHalfChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreHalfChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem storeWordChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (StoreWordChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreWordChip.circuit (p := p)).channelsWithGuarantees =
      (StoreWordChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreWordChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem storeDoubleChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (StoreDoubleChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreDoubleChip.circuit (p := p)).channelsWithGuarantees =
      (StoreDoubleChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreDoubleChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem mulChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (MulChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MulChip.circuit (p := p)).channelsWithGuarantees =
      (MulChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (MulChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem divRemChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (DivRemChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (DivRemChip.circuit (p := p)).channelsWithGuarantees =
      (DivRemChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (DivRemChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem aluX0Chip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (AluX0Chip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AluX0Chip.circuit (p := p)).channelsWithGuarantees =
      (AluX0Chip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AluX0Chip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem u8RangeProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.U8Range.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.U8Range.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.U8Range.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem msbProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.MSB.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.MSB.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.MSB.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem andProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.AndByte.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.AndByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.AndByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem orProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.OrByte.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.OrByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.OrByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem xorProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.XorByte.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.XorByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.XorByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem ltuProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.Ltu.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.Ltu.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.Ltu.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem programProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ProgramProviderChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ProgramProviderChip.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ProgramProviderChip.circuit (p := p)).channelsWithRequirements = [programChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem memoryInitProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (MemoryProviderChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryProviderChip.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (MemoryProviderChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

set_option linter.unusedSectionVars false in
private theorem memoryFinalizeProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (MemoryFinalizeChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryFinalizeChip.circuit (p := p)).channelsWithGuarantees = [memoryChannel.toRaw] from rfl,
    show (MemoryFinalizeChip.circuit (p := p)).channelsWithRequirements = [] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem memoryBumpProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (MemoryBumpChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryBumpChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, memoryChannel.toRaw] from rfl,
    show (MemoryBumpChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem stateBumpProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (StateBumpChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StateBumpChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, stateChannel.toRaw] from rfl,
    show (StateBumpChip.circuit (p := p)).channelsWithRequirements = [] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem rangeProvider_exitChannel_not_mem (width : RangeChip.Width) :
    (exitChannel (p := p)).toRaw ∉ (RangeChip.circuitFor (p := p) width).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (RangeChip.circuitFor (p := p) width).channelsWithGuarantees = [] from rfl,
    show (RangeChip.circuitFor (p := p) width).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

/-- **No instruction chip speaks on the Exit bus.** -/
theorem sp1Tables_exitChannel_not_mem : ∀ c ∈ sp1Tables (p := p),
    (exitChannel (p := p)).toRaw ∉ c.circuit.channels := by
  intro c hc
  fin_cases hc
  exacts [addChip_exitChannel_not_mem, addiChip_exitChannel_not_mem, addwChip_exitChannel_not_mem, subChip_exitChannel_not_mem, subwChip_exitChannel_not_mem, bitwiseChip_exitChannel_not_mem, ltChip_exitChannel_not_mem, shiftLeftChip_exitChannel_not_mem, shiftRightChip_exitChannel_not_mem, jalChip_exitChannel_not_mem, jalrChip_exitChannel_not_mem, branchChip_exitChannel_not_mem, uTypeChip_exitChannel_not_mem, loadByteChip_exitChannel_not_mem, loadHalfChip_exitChannel_not_mem, loadWordChip_exitChannel_not_mem, loadDoubleChip_exitChannel_not_mem, loadX0Chip_exitChannel_not_mem, storeByteChip_exitChannel_not_mem, storeHalfChip_exitChannel_not_mem, storeWordChip_exitChannel_not_mem, storeDoubleChip_exitChannel_not_mem, mulChip_exitChannel_not_mem, divRemChip_exitChannel_not_mem, aluX0Chip_exitChannel_not_mem]

/-- **No provider table before the Halt position speaks on the Exit bus.** -/
theorem sp1ProviderTables_exitChannel_not_mem (k : ℕ)
    (bound : k < (sp1ProviderTables (p := p)).length) (notHalt : k ≠ 28) :
    (exitChannel (p := p)).toRaw ∉ ((sp1ProviderTables (p := p))[k]).circuit.channels := by
  rw [sp1ProviderTables_length] at bound
  interval_cases k
  · exact u8RangeProvider_exitChannel_not_mem
  · exact msbProvider_exitChannel_not_mem
  · exact andProvider_exitChannel_not_mem
  · exact orProvider_exitChannel_not_mem
  · exact xorProvider_exitChannel_not_mem
  · exact ltuProvider_exitChannel_not_mem
  all_goals first
  | exact (notHalt rfl).elim
  | exact rangeProvider_exitChannel_not_mem _
  | exact programProvider_exitChannel_not_mem
  | exact memoryInitProvider_exitChannel_not_mem
  | exact memoryFinalizeProvider_exitChannel_not_mem
  | exact memoryBumpProvider_exitChannel_not_mem
  | exact stateBumpProvider_exitChannel_not_mem

end SP1Clean.Soundness
