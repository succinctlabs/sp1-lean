import SP1Clean.Model.InteractionProjection
import ToClean.Air.TableBuild

/-! # The literal Clean access ledger of a built table

The bridge from a Clean `Air.Flat.Table` to a `LookupAccessList`: take the table's own evaluated
interactions and project each through `Interaction.toAccess` (`Model/InteractionProjection.lean`).

**Deliberately at the Model stratum.** Nothing here mentions a chip, an oracle, an extracted row, or
faithfulness — the vocabulary is Clean's `Table`/`Component` plus this repository's bus types, and
that is exactly the join `docs/layering.md`'s placement law computes. It lived in
`Faithful/Transport/Table.lean` until 2026-08 because the exact-to-native transport was its first
consumer, which put it out of reach of `Proofs/Completeness/` — the completeness layer needs the same
ledger to recount provider demand, and reaching for it there was the repository's only
`Proofs -> Faithful` import.

Note the `toAccess` here is the **Clean-side** one, over Clean's `Interaction`. The extracted-oracle
ADT has its own same-named projection in `Extracted/InteractionModel.lean`; the two agree on the
`LookupAccess` tuple they produce, and that agreement is the syntactic faithfulness bridge. Do not
conflate them: they sit at different strata, and only this one is stateable at Model.
-/

set_option autoImplicit false

namespace SP1Clean

open Circuit
open Air.Flat (Component Table)

variable {p : ℕ} [Fact p.Prime]

/-- The literal Clean interaction ledger of one table.  Unlike `tableNativeAccesses`, this does
not dualize the Memory or Program signs to match the extracted Rust oracle: it is exactly
`Table.interactions`, evaluated by Clean, followed by the common integer projection.  Native
provider recounting and native channel balance must use this definition. -/
def tableCleanAccesses (table : Table (ZMod p)) : LookupAccessList :=
  table.interactions.map Interaction.toAccess

/-- Concatenate the literal Clean ledgers of a list of tables, preserving table and row order. -/
def tablesCleanAccesses (tables : List (Table (ZMod p))) : LookupAccessList :=
  tables.flatMap tableCleanAccesses

@[simp] theorem tablesCleanAccesses_append (left right : List (Table (ZMod p))) :
    tablesCleanAccesses (left ++ right) =
      tablesCleanAccesses left ++ tablesCleanAccesses right := by
  simp only [tablesCleanAccesses, List.flatMap_append]

/-- Evaluating an abstract interaction and then applying the literal Clean projection is the same
as applying the expression-level projection in its environment.  This is intentionally about
Clean's orientation; it performs none of the Memory/Program dualization used by the Rust-facing
faithfulness vocabulary. -/
theorem interactionToAccess_eval (env : Environment (ZMod p))
    (interaction : AbstractInteraction (ZMod p)) :
    Interaction.toAccess (interaction.eval env) =
      AbstractInteraction.toAccess env interaction := by
  simp only [Interaction.toAccess, AbstractInteraction.toAccess, AbstractInteraction.eval,
    Vector.toList]

/-- Closed form for the literal Clean access ledger of an honestly built table. -/
theorem tableCleanAccesses_build (component : Component (ZMod p))
    (inputs : List (component.Input (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    tableCleanAccesses (Table.build component inputs data hint) =
      inputs.flatMap fun input =>
        component.operations.interactions.map
          (AbstractInteraction.toAccess
            (Environment.fromArray (component.buildRow input data hint) data)) := by
  simp only [tableCleanAccesses, Table.build_interactionValues,
    Operations.interactionValues, List.map_flatMap, List.map_map, Function.comp_def,
    interactionToAccess_eval]

/-- Row-wise singleton specialization of `tableCleanAccesses_build`.  Provider components emit one
literal Clean access per row. -/
theorem tableCleanAccesses_build_map_singleton
    {Row : Type} (component : Component (ZMod p)) (rows : List Row)
    (decode : Row → component.Input (ZMod p)) (access : Row → LookupAccess)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (rowAccess : ∀ row ∈ rows,
      component.operations.interactions.map
          (AbstractInteraction.toAccess
            (Environment.fromArray (component.buildRow (decode row) data hint) data)) =
        [access row]) :
    tableCleanAccesses (Table.build component (rows.map decode) data hint) =
      rows.map access := by
  rw [tableCleanAccesses_build]
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, List.flatMap_cons]
    rw [rowAccess row (by simp), ih (fun r hr => rowAccess r (by simp [hr]))]
    rfl

end SP1Clean
