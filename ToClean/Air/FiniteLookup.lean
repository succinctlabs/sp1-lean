module

public import Clean.Circuit.Lookup

/-! # Finite realizations of Clean lookup predicates

Clean's raw lookup tables expose a predicate without an authenticated finite enumeration.
`FiniteLookup` supplies that enumeration and its equivalence to the original predicate for
every data environment. Static tables supply a canonical instance. This API belongs upstream
beside the lookup definitions; finite checking does not depend on an export format or emitter.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]

/-- A concrete, prover-data-independent realization of a lookup predicate. -/
structure FiniteLookup (F : Type) where
  table : RawTable F
  rows : List (Vector F table.arity)
  realizes : ∀ data row, table.Contains data row ↔ row ∈ rows

omit [FiniteField F] in
/-- A static table contains exactly its listed rows (the `FiniteLookup.ofStatic` witness). -/
theorem staticTable_realizes {Row : TypeMap} [ProvableType Row]
    (table : StaticTable F Row) (data : Array (Vector F (size Row))) (row : Vector F (size Row)) :
    table.toTable.toRaw.Contains data row ↔
      row ∈ List.ofFn (fun index => toElements (table.row index)) := by
  change (∃ index, fromElements row = table.row index) ↔ _
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨index, equal⟩
    exact ⟨index, by simpa only [ProvableType.toElements_fromElements]
      using (congrArg toElements equal).symm⟩
  · rintro ⟨index, equal⟩
    exact ⟨index, by rw [← equal, ProvableType.fromElements_toElements]⟩

/-- Static tables have a canonical finite realization; no witness-provided rows are trusted. -/
def FiniteLookup.ofStatic {Row : TypeMap} [ProvableType Row] (table : StaticTable F Row) :
    FiniteLookup F where
  table := table.toTable.toRaw
  rows := List.ofFn (fun index => toElements (table.row index))
  realizes := staticTable_realizes table

end Air.Flat
