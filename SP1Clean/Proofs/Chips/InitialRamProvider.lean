import SP1Clean.Proofs.Chips.SnapshotRamProvider
import Clean.Circuit.StructuralLemmas

/-! # Boot specialization of the snapshot RAM provider

The circuit and constructor are shared with arbitrary local snapshots. Only the semantic contract
is specialized here, using the proved realization of the native image's initial Sail state.
-/

namespace SP1Clean.InitialRamProvider

open Circuit SP1Clean.Model.Core SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

abbrev addressInput := @SnapshotRamProvider.addressInput
abbrev message := @SnapshotRamProvider.message

omit [Fact (2 ^ 17 < p)] in
/-- The pushed RAM record has its canonical value in the actual native boot state. -/
theorem initialSpec (image : ProgramImage) (input : Word (ZMod p))
    (value : Word (ZMod p)) (address : Circuits.Types.AddressOperation (ZMod p))
    (read : InitialMemoryRead.Spec image.initialMemory input value)
    (checked : AddressOperation.Spec (addressInput input) address) :
    MemoryBoundary.InitialAtSpec image (Word.toNat input) (message address value) := by
  have valid := SnapshotRamProvider.snapshotSpec image.memorySnapshot input value address read checked
  exact ⟨valid.1.initial, valid.2⟩

abbrev main (image : ProgramImage) := SnapshotRamProvider.main (p := p) image.memorySnapshot

instance elaborated (image : ProgramImage) :
    ElaboratedCircuit (ZMod p) Word MemoryMsg (main image) :=
  SnapshotRamProvider.elaborated image.memorySnapshot

theorem main_memory_interactions (image : ProgramImage) (input : Var Word (ZMod p)) (offset : ℕ) :
    ((main image input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pushed ((elaborated image).output input offset)).toRaw] :=
  SnapshotRamProvider.main_memory_interactions image.memorySnapshot input offset

def circuit (image : ProgramImage) : GeneralFormalCircuit (ZMod p) Word MemoryMsg where
  name := "sp1.native.memory.initial.ram"
  main := main image
  elaborated := elaborated image
  Spec input output _ := MemoryBoundary.InitialAtSpec image (Word.toNat input) output
  ProverAssumptions input _ _ :=
    InitialMemoryRead.ProverAssumptions input ∧
      AddressOperation.Assumptions (addressInput input)
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := ((SnapshotRamProvider.circuit image.memorySnapshot).weakenSpec
    (fun input output _ => MemoryBoundary.InitialAtSpec image (Word.toNat input) output)
    (fun _ _ _ valid => ⟨valid.1.initial, valid.2⟩)).soundness
  completeness := (SnapshotRamProvider.circuit image.memorySnapshot).completeness

end SP1Clean.InitialRamProvider
