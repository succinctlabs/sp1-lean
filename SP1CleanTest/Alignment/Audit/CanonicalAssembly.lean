import SP1Clean.Proofs.Completeness.Assembly
import SP1Clean.Composition.CoreEnsemble
import SP1Clean.Model.SP1Field

/-! # Generation inputs cannot supply uncommitted program metadata

The legacy 55-table inventory has no physical table named `sp1.pc_start`. Its canonical data
therefore cannot inherit that entry from witness-generation inputs. This catches the old
shared-data assumption without evaluating a concrete trace or assuming its semantic validity.
Program-binding consumers must use an authenticated boundary instead of that assumption.
-/

namespace SP1CleanTest.CanonicalAssembly

open SP1Clean SP1Clean.Soundness Air.Flat

/-- No witness of this physical inventory contains the legacy initial-PC data entry. -/
theorem legacyInitialPcAbsent (witness : EnsembleWitness (sp1Ensemble (p := SP1Prime))) :
    witness.data "sp1.pc_start" 3 = #[] := by
  have absent : "sp1.pc_start" ∉
      ((sp1Ensemble (p := SP1Prime)).tables.map fun component => component.circuit.name) := by
    decide
  have noTable : ∀ table ∈ witness.tables, table.component.circuit.name ≠ "sp1.pc_start" := by
    intro table member same
    apply absent
    rw [← witness.tables_map_component, List.map_map]
    exact List.mem_map.mpr ⟨table, member, same⟩
  exact deriveProverData_append_of_not_mem [] witness.tables "sp1.pc_start" noTable 3

/-- A nonempty generation-time entry cannot become committed data without a physical table. -/
theorem seedCannotChooseCommittedData (trace : SupportedCoreTraceWitness SP1Prime)
    (nonempty : trace.generationData "sp1.pc_start" 3 ≠ #[]) :
    trace.witness.data ≠ trace.generationData := by
  intro same
  apply nonempty
  rw [← same]
  exact legacyInitialPcAbsent trace.witness

/-- Exact Rust-row transport also rejects generation metadata as a committed program binding. -/
theorem exactSeedCannotChooseCommittedData {Digest : Type}
    (statement : SP1ShardStatement (ZMod SP1Prime) Digest)
    (execution memory : CoreAIR.Witness (CoreAIR.Current.Row SP1Prime))
    (inventory : Composition.CanonicalPreprocessedInventory execution)
    (data : ProverData (ZMod SP1Prime)) (hint : ProverHint (ZMod SP1Prime))
    (nonempty : data "sp1.pc_start" 3 ≠ #[]) :
    (Composition.exactNativeEnsembleWitness statement execution memory inventory data hint).data ≠ data := by
  intro same
  apply nonempty
  rw [← same]
  exact legacyInitialPcAbsent _

end SP1CleanTest.CanonicalAssembly
