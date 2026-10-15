module

public import Clean.Circuit.Lookup

/-! # Static lookup tables from concrete rows

## Gap against upstream

Clean's `StaticTable` asks each caller for an indexed row function and a proof that its image
equals the table specification. There is no constructor for an already computed finite list.
`ofRows` supplies that common case with literal list membership as its specification and an
executable index search. Its defining predicate is independent of prover data.
-/

@[expose] public section

namespace StaticTable

variable {F : Type} {Row : TypeMap} [ProvableType Row] [DecidableEq (Row F)]

/-- A static table containing exactly the supplied rows. Duplicate rows are permitted. -/
def ofRows (name : String) (rows : List (Row F)) : StaticTable F Row where
  name
  length := rows.length
  row index := rows[index]
  index row := rows.findIdx (fun candidate => decide (candidate = row))
  Spec row := row ∈ rows
  contains_iff row := by
    constructor
    · rintro ⟨index, rfl⟩
      exact List.getElem_mem index.isLt
    · intro member
      obtain ⟨index, equal⟩ := List.mem_iff_get.mp member
      exact ⟨index, equal.symm⟩

end StaticTable
