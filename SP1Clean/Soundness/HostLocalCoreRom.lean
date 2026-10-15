import SP1Clean.Soundness.HostLocalCorePermissions
import SP1Clean.Soundness.HostLocalCoreMemory
import SP1Clean.Soundness.ProtectedLocalCoreRom

/-! # Ordinary ROM protection with host RAM effects installed

The decoded instructions retain their physical rows in the extended assembly. Its own permission
ledger authenticates their byte requests, even when host tables consume additional permissions.
The store footprints and instruction case split reuse the existing protected-core proofs.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance instructionLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance instructionLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((tables image source auxiliary).map (·.circuit.name)).Nodup}

private theorem instruction_component (index : Fin 25) :
    (tables (p := p) image source auxiliary)[7 + index.val]'(by rw [tables_length]; omega) =
      (ProtectedLocalCore.tables image source)[7 + index.val]'(by
        rw [ProtectedLocalCore.tables_length]; omega) := by
  rw [core_component image source auxiliary ⟨7 + index.val, by omega⟩,
    if_neg (show ¬58 = 7 + index.val by omega)]

private theorem instructionRows_physical
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    {decoded : DecodedInstructionRow p}
    (member : decoded ∈ LocalCore.instructionRows (localWitness witness)) :
    ∃ index : Fin 25,
      decoded.chip = (supportedChips (p := p))[index.val]'(by rw [supportedChips_length]; exact index.isLt) ∧
      decoded.physical ∈ (witness.tables[7 + index.val]'(by
        rw [← witness.same_length]; change 7 + index.val < (tables image source auxiliary).length
        rw [tables_length]; omega)).table := by
  obtain ⟨index, chipBound, tableBound, same, physical⟩ := position_of_mem_decodeInstructionTables member
  have bound : index < 25 := by simpa only [supportedChips_length] using chipBound
  refine ⟨⟨index, bound⟩, same, ?_⟩
  simp only [LocalCore.instructionTables, List.getElem_take, List.getElem_drop] at physical
  rw [localWitness_table witness ⟨7 + index, by omega⟩ (by change 58 ≠ 7 + index; omega)] at physical
  exact physical

private theorem instruction_write_authorized (index : Fin 25)
    (rowComponent : Component (ZMod p))
    (component : rowComponent = (ProtectedLocalCore.tables image source)[7 + index.val]'(by
      rw [ProtectedLocalCore.tables_length]; omega))
    (env : Environment (ZMod p))
    (permission : ∀ gate address,
      (WritePermissionProvider.channel.pulledIf gate address).toRaw ∈
        rowComponent.operations.interactionsWith WritePermissionProvider.channel.toRaw →
      Expression.eval env gate = 1 →
      WritePermissionProvider.Permitted image (eval env address)) :
    let chip := supportedChipFor (p := p) (InstructionChipId.all[index.val]'index.isLt)
    (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)).is_real = 1 →
      Target.RowWriteAuthorized image (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)) := by
  dsimp only
  intro active
  apply ProtectedLocalCore.supported_write_property (Target.RowWriteAuthorized image)
    (fun row empty write same => by rw [empty] at same; contradiction) _ env ?_ ?_ ?_ ?_ active
  · intro identity real
    have position : index.val = 18 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply ProtectedLocalCore.byte_write_authorized_of_row rowComponent env permission ?_ real
    rw [component]
    simp only [position]
    rfl
  · intro identity real
    have position : index.val = 19 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply ProtectedLocalCore.half_write_authorized_of_row rowComponent env permission ?_ real
    rw [component]
    simp only [position]
    rfl
  · intro identity real
    have position : index.val = 20 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply ProtectedLocalCore.word_write_authorized_of_row rowComponent env permission ?_ real
    rw [component]
    simp only [position]
    rfl
  · intro identity real
    have position : index.val = 21 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply ProtectedLocalCore.double_write_authorized_of_row rowComponent env permission ?_ real
    rw [component]
    simp only [position]
    rfl

/-- The actual extended AIR bounds every ordinary write byte and excludes instruction bytes. -/
theorem instructionRows_write_authorized
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (pulls : ∀ component ∈ auxiliary, WritePermission.Pulls component)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel WritePermissionProvider.channel.toRaw)
    {decoded : DecodedInstructionRow p}
    (member : decoded ∈ LocalCore.instructionRows (localWitness witness))
    (active : (decoded.toChipRow (localWitness witness).data).is_real = 1) :
    Target.RowWriteAuthorized image (decoded.toChipRow (localWitness witness).data).view := by
  obtain ⟨index, same, physicalMem⟩ := instructionRows_physical witness member
  let table := witness.tables[7 + index.val]'(by
    rw [← witness.same_length]; change 7 + index.val < (tables image source auxiliary).length
    rw [tables_length]; omega)
  have tableMem : table ∈ witness.tables := List.getElem_mem _
  have component : table.component = (ProtectedLocalCore.tables image source)[7 + index.val]'(by
      rw [ProtectedLocalCore.tables_length]; omega) := by
    dsimp only [table]
    rw [← witness.same_circuits]
    exact instruction_component index
  change (decoded.toChipRow (localWitness witness).data).view.is_real = 1 at active
  rw [DecodedInstructionRow.toChipRow_setData decoded (localWitness witness).data witness.data,
    DecodedInstructionRow.toChipRow_view] at active ⊢
  rw [same] at active ⊢
  have descriptor : (supportedChips (p := p))[index.val]'(by
      rw [supportedChips_length]; exact index.isLt) =
      supportedChipFor (InstructionChipId.all[index.val]'index.isLt) := List.getElem_map _
  rw [descriptor] at active ⊢
  exact instruction_write_authorized index table.component component
    (Environment.fromArray decoded.physical witness.data)
    (row_pull_permitted witness pulls constraints balanced table tableMem decoded.physical physicalMem) active

/-- ROM exclusion is a consequence of the full bounded byte authorization. -/
theorem instructionRows_write_permitted
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (pulls : ∀ component ∈ auxiliary, WritePermission.Pulls component)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel WritePermissionProvider.channel.toRaw)
    {decoded : DecodedInstructionRow p}
    (member : decoded ∈ LocalCore.instructionRows (localWitness witness))
    (active : (decoded.toChipRow (localWitness witness).data).is_real = 1) :
    Target.RowWritePermitted image (decoded.toChipRow (localWitness witness).data).view := by
  exact (instructionRows_write_authorized witness pulls constraints balanced member active).permitted

end SP1Clean.Soundness.HostLocalCore
