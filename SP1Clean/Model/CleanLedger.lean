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

/-! ## List-level decomposition

`tablesCleanAccesses` is a `flatMap`, so peeling it needs only the two structural equations. They
were previously done by hand at each of the five sites that needed them (`Closure.lean`,
`ClosureRealization.lean`, `Composition/CoreEnsemble.lean`), each unfolding to `List.flatMap` first;
a per-chip decomposition peels twenty-five times, so they are worth naming. -/

@[simp] theorem tablesCleanAccesses_nil : tablesCleanAccesses ([] : List (Table (ZMod p))) = [] :=
  rfl

theorem tablesCleanAccesses_cons (table : Table (ZMod p)) (tables : List (Table (ZMod p))) :
    tablesCleanAccesses (table :: tables) =
      tableCleanAccesses table ++ tablesCleanAccesses tables := by
  simp only [tablesCleanAccesses, List.flatMap_cons]

/-- The `buildHinted` companion of `tableCleanAccesses_build`.

Seven of the twenty-five instruction chips build through `Table.buildHinted` rather than
`Table.build` — the ones whose witness generation reads a per-row prover hint (the flag one-hots of
Bitwise/Lt/the shifts/Mul/DivRem, and Branch's comparison selector). Without this they are simply
unreachable from the ledger layer. -/
theorem tableCleanAccesses_buildHinted (component : Component (ZMod p))
    (inputs : List (component.Input (ZMod p) × ProverHint (ZMod p)))
    (data : ProverData (ZMod p)) :
    tableCleanAccesses (Table.buildHinted component inputs data) =
      inputs.flatMap fun input =>
        component.operations.interactions.map
          (AbstractInteraction.toAccess
            (Environment.fromArray (component.buildRow input.1 data input.2) data)) := by
  simp only [tableCleanAccesses, Table.buildHinted_interactionValues,
    Operations.interactionValues, List.map_flatMap, List.map_map, Function.comp_def,
    interactionToAccess_eval]

/-! ## One channel's ledger versus the whole table's

Clean's balance obligations are stated per channel (`EnsembleWitness.interactionsWith channel`),
while a provider recount reads the whole table at once. The two are the same accesses, and at any
given key they are the same *sum* — because `Interaction.toAccess` puts the channel's own `name` in
the key's table slot, so a key already determines which channel could have produced it.

What that argument needs, and all it needs, is that the channel name determines the channel among
the ones the table can actually emit on. That is supplied by the caller: it is an ensemble-level
fact (SP1's four buses have four distinct names), not something a single table knows.
-/

private theorem filter_map_eq {α β : Type*} (l : List α) (f : α → β) (q : β → Bool) :
    (l.map f).filter q = (l.filter fun a => q (f a)).map f := by
  induction l with
  | nil => rfl
  | cons head tail ih => by_cases hq : q (f head) <;> simp [hq, ih]

/-- **A table's ledger restricted to one bus IS that bus's own interaction list.**

The multi-bus counterpart of the providers' route. A provider component names exactly one channel,
so `Ledger.OnlyChannel` lets its whole `interactions` list be read as that channel's — an
instruction chip names up to four, so that lemma is unavailable to it. Filtering by
`InteractionKind` is the replacement, and it works because `Interaction.toAccess` reads the kind off
the emitting channel's own `name`: the kind *is* the channel, as long as no two channels the table
can emit on share one.

That last condition is `honly`, and it is the caller's: for `sp1Ensemble` it comes from
`Soundness/EnsembleChannels.lean` (tables emit only on the ensemble's four channels, whose names —
hence kinds — are distinct). Stating it here rather than assuming it keeps this file free of the
ensemble.

Unlike `multiplicitySum_interactionsWith_eq`, which compares the two at a single key, this is a
**list** equality — which is what a permutation obligation needs. -/
theorem tableCleanAccesses_filterKind (table : Table (ZMod p)) (channel : RawChannel (ZMod p))
    (K : InteractionKind) (hkind : kindOf channel.name = K)
    (honly : ∀ i ∈ table.interactions, kindOf i.channel.name = K → i.channel = channel) :
    (tableCleanAccesses table).filter (fun a => a.1 = K) =
      (table.interactionsWith channel).map Interaction.toAccess := by
  rw [tableCleanAccesses, filter_map_eq, Air.Flat.Table.interactionsWith_eq_filter]
  refine congrArg (List.map Interaction.toAccess) (List.filter_congr fun i hi => ?_)
  by_cases hc : i.channel = channel
  · simp only [hc, hkind, decide_true, Interaction.toAccess]
  · have hne : kindOf i.channel.name ≠ K := fun h => hc (honly i hi h)
    simp only [Interaction.toAccess, hne, hc, decide_false]

/-- **A table's ledger at a key is that key's own channel's ledger.** -/
theorem multiplicitySum_interactionsWith_eq (table : Table (ZMod p))
    (channel : RawChannel (ZMod p)) {k : LookupAccessList.LookupKey}
    (honly : ∀ i ∈ table.interactions,
      LookupAccessList.keyOf (Interaction.toAccess i) = k → i.channel = channel) :
    LookupAccessList.multiplicitySum
        ((table.interactionsWith channel).map Interaction.toAccess) k =
      LookupAccessList.multiplicitySum (tableCleanAccesses table) k := by
  rw [Air.Flat.Table.interactionsWith_eq_filter, tableCleanAccesses]
  exact LookupAccessList.multiplicitySum_filter_map_eq _ _ _ _
    fun i hi hkey => by simpa using honly i hi hkey

omit [Fact p.Prime] in
/-- The key an interaction lands on names its own channel, so a key with a different table name
cannot have come from this interaction. -/
theorem channel_name_of_keyOf_toAccess {i : Interaction (ZMod p)}
    {k : LookupAccessList.LookupKey}
    (h : LookupAccessList.keyOf (Interaction.toAccess i) = k) : i.channel.name = k.2.1 := by
  rw [← h]
  rfl

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

/-! ## Reading a built row's input cells back

After a component's `rowOperations` is unfolded its input variables are plain offsets rather than an
occurrence of `rowInput`, so `Component.rowInput_buildRow` cannot rewrite them directly. These two
recover the typed input at a cell. Stated over Clean's `Component`/`ProvableType` and nothing else. -/

/-- A built row keeps its typed input as a literal prefix.  This cell-level form is useful when
normalizing interactions: after a component's `rowOperations` is unfolded, its input variables are
plain offsets rather than an occurrence of `rowInput`, so `Component.rowInput_buildRow` cannot
rewrite them directly. -/
theorem buildRow_input_get (component : Component (ZMod p))
    (input : component.Input (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (i : ℕ) (hi : i < size component.Input) :
    (Environment.fromArray (component.buildRow input data hint) data).get i =
      (toElements input)[i] := by
  have decoded := component.rowInput_buildRow input data data hint
  have atCell := congrArg
    (fun value : component.Input (ZMod p) => (toElements value)[i]) decoded
  simpa only [Component.rowInput, valueFromOffset, ProvableType.toElements_fromElements,
    Vector.getElem_mapRange, Nat.zero_add] using atCell

/-- Expression-level form of `buildRow_input_get`, matching the variables that remain after a
component's interaction list has been normalized without unfolding `Expression.eval`. -/
theorem eval_var_buildRow_input_get (component : Component (ZMod p))
    (input : component.Input (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (i : ℕ) (hi : i < size component.Input) :
    Expression.eval
        (Environment.fromArray (component.buildRow input data hint) data)
        (var ⟨i⟩) = (toElements input)[i] := by
  simpa only [Expression.eval] using buildRow_input_get component input data hint i hi

end SP1Clean
