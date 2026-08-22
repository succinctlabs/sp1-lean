import Clean.Air.FlatEnsemble
import ToClean.Air.TableBuild

/-! # Assembling an `EnsembleWitness` from built tables

`ToClean/Air/TableBuild.lean` builds **one** flat-AIR table from a component and a list of semantic
inputs. This file closes the remaining structural gap between a list of such tables and Clean's
`EnsembleWitness`, so a completeness proof never has to discharge the witness record's indexed
side conditions by hand.

Two pieces:

* `EnsembleWitness.ofTables` — the constructor. Its two positional obligations
  (`same_length` and `same_circuits`, the latter stated *per index*) follow from the single
  list-level equation `tables.map (·.component) = ens.tables`, which for a concrete ensemble and a
  concrete assembly is one `rfl`. Discharging as many indexed goals as the ensemble has tables is
  thereby replaced by one.
* `Component.buildRow_of_localLength_zero` / `verifierTable_eq_build` — the verifier row is a built
  row. Clean defines `EnsembleWitness.verifierTable` by *hand-writing* the array
  `toElements publicInput`, whereas everything else in a completeness proof arrives through
  `Table.build`. Since an ensemble's verifier is required to generate no witness cells
  (`Ensemble.verifier_length_zero`), the two agree, and the bridge lets one `Table.build`-shaped
  constraint theorem serve the verifier row too.

## Gap against upstream

Clean has no way to *construct* an `EnsembleWitness`: `Clean/Air/FlatEnsemble.lean` defines the
record and everything one can conclude from it, but a prover-side assembly must instantiate
`same_length`/`same_circuits` itself. Nothing here is SP1-specific — `ofTables` is the general
introduction rule the record is missing, and `verifierTable_eq_build` says the verifier row is not
a special case of row construction. Both belong beside `Table.build` upstream.
-/

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

namespace Air.Flat
open Circuit

/-- **Assemble an ensemble witness from a list of built tables.** The caller supplies the tables in
the ensemble's own order, the shared committed prover data, and the public input; the one proof
obligation is that the tables' components are the ensemble's components, as a list equation. -/
def EnsembleWitness.ofTables (ens : Ensemble F PublicIO) (tables : List (Table F))
    (data : ProverData F) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables)
    (hdata : ∀ table ∈ tables, table.data = data) : EnsembleWitness ens where
  tables := tables
  data := data
  publicInput := publicInput
  same_length := by rw [← hmap, List.length_map]
  same_circuits := by
    intro i hi
    have hi' : i < (tables.map (·.component)).length := by rw [hmap]; exact hi
    rw [← List.getElem_of_eq hmap hi', List.getElem_map]
  same_data := hdata

@[simp] lemma EnsembleWitness.ofTables_tables (ens : Ensemble F PublicIO) (tables : List (Table F))
    (data : ProverData F) (publicInput : PublicIO F) (hmap : tables.map (·.component) = ens.tables)
    (hdata : ∀ table ∈ tables, table.data = data) :
    (EnsembleWitness.ofTables ens tables data publicInput hmap hdata).tables = tables := rfl

@[simp] lemma EnsembleWitness.ofTables_data (ens : Ensemble F PublicIO) (tables : List (Table F))
    (data : ProverData F) (publicInput : PublicIO F) (hmap : tables.map (·.component) = ens.tables)
    (hdata : ∀ table ∈ tables, table.data = data) :
    (EnsembleWitness.ofTables ens tables data publicInput hmap hdata).data = data := rfl

@[simp] lemma EnsembleWitness.ofTables_publicInput (ens : Ensemble F PublicIO)
    (tables : List (Table F)) (data : ProverData F) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables)
    (hdata : ∀ table ∈ tables, table.data = data) :
    (EnsembleWitness.ofTables ens tables data publicInput hmap hdata).publicInput =
      publicInput := rfl

/-- The assembled witness's full table list, verifier row included, in closed form. This is the
list `EnsembleWitness.Constraints` and the channel balances quantify over. -/
lemma EnsembleWitness.ofTables_allTables (ens : Ensemble F PublicIO) (tables : List (Table F))
    (data : ProverData F) (publicInput : PublicIO F) (hmap : tables.map (·.component) = ens.tables)
    (hdata : ∀ table ∈ tables, table.data = data) :
    (EnsembleWitness.ofTables ens tables data publicInput hmap hdata).allTables =
      (EnsembleWitness.ofTables ens tables data publicInput hmap hdata).verifierTable ::
        tables := rfl

/-! ## The verifier row is a built row -/

namespace Component

/-- **A circuit that generates no witness cells builds exactly the row it was seeded with.** The
generated array has the seed's size (`size_witgenWithData` at `localLength = 0`) and agrees with it
at every index (`getElem?_witgenWithData_of_lt`), so it *is* the seed. -/
theorem buildRow_of_localLength_zero (c : Component F) (input : c.Input F) (data : ProverData F)
    (hint : ProverHint F) (hzero : c.circuit.localLength (varFromOffset c.Input 0) = 0) :
    c.buildRow input data hint = (toElements input).toArray := by
  have hlen : ((c.circuit.main (varFromOffset c.Input 0)).operations (size c.Input)).localLength
      = 0 := by
    rw [show ((c.circuit.main (varFromOffset c.Input 0)).operations (size c.Input)).localLength
      = (c.circuit.main (varFromOffset c.Input 0)).localLength (size c.Input) from rfl,
      c.circuit.localLength_eq, hzero]
  have hsize : (c.buildRow input data hint).size = (toElements input).toArray.size := by
    rw [buildRow, Circuit.size_witgenWithData, Vector.size_toArray, hlen, Nat.add_zero]
  refine Array.ext hsize ?_
  intro i hi hi'
  have hbound : i < ((c.circuit.main (varFromOffset c.Input 0)).witgenWithData data hint
      (toElements input).toArray).size := hi
  have := Circuit.getElem?_witgenWithData_of_lt (c.circuit.main (varFromOffset c.Input 0)) data
    hint (init := (toElements input).toArray) hi'
  rw [Array.getElem?_eq_getElem hbound] at this
  show ((c.circuit.main (varFromOffset c.Input 0)).witgenWithData data hint
    (toElements input).toArray)[i]'hbound = _
  simpa using this

end Component

/-- **Clean's hand-written verifier row is the row `Table.build` produces**, for any assembled
witness. An ensemble's verifier generates no witness cells by definition, so its built row is its
input row — which is exactly the array `EnsembleWitness.verifierTable` writes down. -/
theorem verifierTable_eq_build {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (hint : ProverHint F) :
    witness.verifierTable =
      Table.build ens.verifierTable [witness.publicInput] witness.data hint := by
  have hzero : ens.verifierTable.circuit.localLength
      (varFromOffset ens.verifierTable.Input 0) = 0 := ens.verifier_length_zero _
  rw [Table.ext_iff]
  refine ⟨rfl, ?_, ?_, rfl⟩
  · show size PublicIO = ens.verifierTable.width
    rw [Component.width, GeneralFormalCircuit.size_eq, hzero, Nat.add_zero]
    with_unfolding_all rfl
  · show [(toElements witness.publicInput).toArray] = _
    rw [Table.build_table, List.map_cons, List.map_nil,
      Component.buildRow_of_localLength_zero _ _ _ _ hzero]
    rfl

end Air.Flat
