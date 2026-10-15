import SP1Clean.Soundness.HostHintReadBanks
import SP1Clean.Soundness.HostQueueCPUReplay

/-! # Legacy padding has no event in the installed CPU inventory

The strengthened physical component projects to the original execution carrier without losing
its zero-selector assertion. Thus every HALT event in the mixed assembly comes from the full
syscall wrapper and participates in HostCall accounting.
-/

namespace SP1Clean.Soundness.HostHintReadTerminal

open Circuit Air.Flat Channels Model.Core NativeCore HostHintReadLocal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance terminalLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance terminalClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
variable {image : ProgramImage} {source : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}
  {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

private theorem bound
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) : 57 < witness.tables.length := by
  rw [← witness.same_length]
  change 57 < ((HostLocalCore.tables image source _).set 57 _).length
  rw [List.length_set, HostLocalCore.tables_length]
  omega

private theorem projected_rows
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    (LocalCore.systemTable (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) 2).table =
      (witness.tables[57]'(bound witness)).table := by
  change ((HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).tables[57]'_).table = _
  rw [HostLocalCore.localWitness_table _ ⟨57, by decide⟩ (by decide), Table.withComponent_rows]
  change ((witness.tables.set 57 _)[57]'_).table = _
  erw [List.getElem_set_self]
  rfl

/-- The original carrier contains no active legacy HALT row. -/
theorem legacy_rows_nil
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) :
    activeSystemRows (LocalCore.systemTable
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) 2)
      (haltRow (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data) (·.is_real) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row member
  obtain ⟨physical, physicalMem, rfl, real⟩ := activeSystemRows_member _ _ _ member
  rw [projected_rows] at physicalMem
  have checked := constraints _ (List.getElem_mem _) physical physicalMem
  have component : (witness.tables[57]'(bound witness)).component = HaltPaddingChip.component :=
    HaltPadding.table_component witness
  change (witness.tables[57]'(bound witness)).component.operations.ConstraintsHold
    (Environment.fromArray physical witness.data) at checked
  rw [component] at checked
  have zero := ((HaltPaddingChip.constraints _).mp checked).2
  change (valueFromOffset HaltChip.Inputs 0 _).is_real = 0 at zero
  have same : (haltRow (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data
      physical).is_real = 0 := by
    have input := ProvableType.valueFromOffset_congr HaltChip.Inputs 0
      (env := Environment.fromArray physical (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data)
      (env' := Environment.fromArray physical witness.data) (fun _ _ => rfl)
    exact (congrArg HaltChip.Inputs.is_real input).trans zero
  exact zero_ne_one (same.symm.trans real)

end SP1Clean.Soundness.HostHintReadTerminal
