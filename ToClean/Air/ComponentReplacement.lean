module

public import ToClean.Air.TableSlot
public import ToClean.Air.EnsembleProjection

/-! # Replacing a registered component without changing its physical rows

Clean has no introduction rule for changing a table's circuit while preserving its complete
rows. This addition requires equal widths and fixed-column contracts. Replacing an ensemble
component uses a typed slot and preserves its name, so the physical inventory remains unique.
Canonical data is preserved only after proving equality of the replacement's derived entries.

These layout and data transport lemmas belong beside Clean's flat tables and ensembles. They
do not construct witnesses or supply another extraction path.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]

/-- Reinterpret complete rows only when both physical layout obligations are preserved. -/
def Table.withComponent (table : Table F) (component : Component F)
    (width : component.width = table.component.width)
    (fixed : component.fixedColumns = table.component.fixedColumns) : Table F where
  component
  table := table.table
  uniform_width := fun row member => (table.uniform_width row member).trans width.symm
  fixed_rows_match := by
    simpa only [Component.fixedRowsMatch, fixed] using table.fixed_rows_match

/-- Changing only the component keeps the literal physical rows. -/
@[simp] theorem Table.withComponent_rows (table : Table F) (component : Component F) (width fixed) :
    (table.withComponent component width fixed).table = table.table := rfl

@[simp] theorem Table.withComponent_component (table : Table F) (component : Component F) (width fixed) :
    (table.withComponent component width fixed).component = component := rfl

/-- Replacing a table by itself retains its width and fixed-column certificates. -/
@[simp] theorem Table.withComponent_self (table : Table F) :
    table.withComponent table.component rfl rfl = table := by
  cases table
  rfl

namespace Table

variable (table : Table F) (component : Component F) (width fixed) (data : ProverData F)

/-- A proved implication between row circuits lifts to all retained physical rows. -/
theorem withComponent_constraints_of
    (preserves : ∀ env, table.component.operations.ConstraintsHold env →
      component.operations.ConstraintsHold env) (checked : table.Constraints data) :
    (table.withComponent component width fixed).Constraints data :=
  fun row member => preserves _ (checked row member)

/-- Identical assertion and lookup systems have identical constraints on retained rows. -/
theorem withComponent_constraints
    (constraints : component.operations.constraints = table.component.operations.constraints)
    (lookups : component.operations.lookups = table.component.operations.lookups) :
    (table.withComponent component width fixed).Constraints data ↔ table.Constraints data := by
  simp only [Constraints, withComponent, Operations.ConstraintsHold, constraints, lookups]

/-- Equal channel operations retain every interaction occurrence in its original order. -/
theorem withComponent_interactions (channel : RawChannel F)
    (same : component.operations.interactionsWith channel = table.component.operations.interactionsWith channel) :
    (table.withComponent component width fixed).interactionsWith data channel =
      table.interactionsWith data channel := by
  simp only [interactionsWith, withComponent, Operations.interactionValuesWith, same]

/-- Channel guarantees transport at the same data, without assuming projected balance. -/
theorem withComponent_channelGuarantees_of (channel : RawChannel F)
    (preserves : ∀ env, table.component.operations.ChannelGuarantees channel env →
      component.operations.ChannelGuarantees channel env)
    (guarantees : table.ChannelGuarantees data channel) :
    (table.withComponent component width fixed).ChannelGuarantees data channel :=
  fun row member => preserves _ (guarantees row member)

end Table

/-- A replacement with the same name and derived entries preserves the complete data function. -/
theorem deriveProverData_set (tables : List (Table F)) (index : Fin tables.length)
    (replacement : Table F)
    (name : replacement.component.circuit.name = tables[index.val].component.circuit.name)
    (entries : ∀ arity, replacement.proverRows arity = tables[index.val].proverRows arity) :
    deriveProverData (tables.set index.val replacement) = deriveProverData tables := by
  induction tables with
  | nil => exact Fin.elim0 index
  | cons table tables ih =>
    rcases index with ⟨index, bound⟩
    cases index with
    | zero =>
      funext key arity
      simp only [List.set_cons_zero, deriveProverData, List.getElem_cons_zero] at name entries ⊢
      rw [name]
      split
      · exact entries arity
      · rfl
    | succ index =>
      have tail := ih ⟨index, by simpa using bound⟩ name entries
      funext key arity
      simp only [List.set_cons_succ, deriveProverData, tail]

variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Replace a registered component, retaining its unique data key. -/
def Ensemble.replaceComponent (ens : Ensemble F PublicIO) {component : Component F}
    (slot : TableSlot ens.tables component) (replacement : Component F)
    (name : replacement.circuit.name = component.circuit.name) : Ensemble F PublicIO :=
  { ens with
    tables := ens.tables.set slot.index.val replacement
    unique_names := by
      rw [List.map_set, name, ← congrArg (fun c : Component F => c.circuit.name) slot.component_eq,
        ← List.getElem_map (l := ens.tables) (f := fun c => c.circuit.name), List.set_getElem_self]
      · exact ens.unique_names
      · simp }

end Air.Flat
