import SP1Clean.Native.Chips.HaltPaddingChip
import ToClean.Air.ComponentReplacement

/-! # Installing the padding-only legacy HALT table

The typed slot identifies the legacy HALT component before adding its zero-selector assertion.
Projection retains every physical row, channel and public input. Its complete canonical data
is unchanged because the wrapper retains the original table name and input layout.
-/

namespace SP1Clean.Soundness.HaltPadding

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
  {PublicIO : TypeMap} [ProvableType PublicIO]

def install (ens : Ensemble (ZMod p) PublicIO)
    (slot : TableSlot ens.tables HaltPaddingChip.original) : Ensemble (ZMod p) PublicIO :=
  ens.replaceComponent slot HaltPaddingChip.component rfl

variable {ens : Ensemble (ZMod p) PublicIO} {slot : TableSlot ens.tables HaltPaddingChip.original}
variable (witness : EnsembleWitness (install ens slot))

theorem bound : slot.index.val < witness.tables.length := by
  rw [← witness.same_length]
  simpa only [install, Ensemble.replaceComponent, List.length_set] using slot.index.isLt

theorem table_component :
    (witness.tables[slot.index.val]'(bound witness)).component = HaltPaddingChip.component := by
  rw [← witness.same_circuits]
  exact List.getElem_set_self (by simpa only [install, Ensemble.replaceComponent, List.length_set] using slot.index.isLt)

/-- Erase only the added assertion, retaining the complete physical table. -/
def project : EnsembleWitness ens :=
  EnsembleWitness.ofTables ens
    (witness.tables.set slot.index.val
      ((witness.tables[slot.index.val]'(bound witness)).withComponent HaltPaddingChip.original
        (by rw [table_component]; rfl) (by rw [table_component]; rfl)))
    witness.publicInput (by
      rw [List.map_set, Table.withComponent_component, witness.tables_map_component]
      change (ens.tables.set slot.index.val HaltPaddingChip.component).set slot.index.val
        HaltPaddingChip.original = ens.tables
      rw [List.set_set]
      simpa only [slot.component_eq] using List.set_getElem_self slot.index.isLt)

/-- Both circuits expose exactly the same derived entry at the same registered name. -/
@[simp] theorem project_data : (project witness).data = witness.data := by
  apply deriveProverData_set witness.tables ⟨slot.index.val, bound witness⟩
  · change HaltPaddingChip.original.circuit.name =
      (witness.tables[slot.index.val]'(bound witness)).component.circuit.name
    rw [table_component]
    rfl
  · intro arity
    simp only [Table.proverRows, Table.withComponent_component, Table.withComponent_rows, table_component]
    rfl

@[simp] theorem project_publicInput : (project witness).publicInput = witness.publicInput := rfl

theorem constraints (checked : witness.Constraints) : (project witness).Constraints := by
  rw [EnsembleWitness.constraints_iff]
  simp only [project_data]
  intro table member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact checked table old
  · apply Table.withComponent_constraints_of
    · rw [table_component]
      exact fun env valid => ((HaltPaddingChip.constraints env).mp valid).1
    · exact checked _ (List.getElem_mem _)

theorem interactions (channel : RawChannel (ZMod p)) :
    (project witness).interactionsWith channel = witness.interactionsWith channel := by
  have row := Table.withComponent_interactions (witness.tables[slot.index.val]'(bound witness))
    HaltPaddingChip.original (by rw [table_component]; rfl) (by rw [table_component]; rfl)
    witness.data channel (by rw [table_component, HaltPaddingChip.interactions])
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.verifierInteractionsWith,
    EnsembleWitness.tableContext, TableContext.interactionsWith, project_data, project_publicInput]
  change ens.verifierOperations.interactionValuesWith channel _ ++
      (witness.tables.set slot.index.val _).flatMap (·.interactionsWith witness.data channel) =
    ens.verifierOperations.interactionValuesWith channel _ ++
      witness.tables.flatMap (·.interactionsWith witness.data channel)
  congr 1
  rw [List.flatMap, List.map_set, row, ← List.getElem_map (l := witness.tables) (i := slot.index.val)
    (f := fun table : Table (ZMod p) => table.interactionsWith witness.data channel), List.set_getElem_self]
  · rfl
  · simpa only [List.length_map] using bound witness

theorem balanced (balance : witness.BalancedChannels) : (project witness).BalancedChannels := by
  intro channel member
  change BalancedInteractions ((project witness).interactionsWith channel)
  rw [interactions]
  exact balance channel member

theorem drop_tables (count : ℕ) (after : slot.index.val < count) :
    (project witness).tables.drop count = witness.tables.drop count :=
  List.drop_set_of_lt after

end SP1Clean.Soundness.HaltPadding
