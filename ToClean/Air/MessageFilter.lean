module

public import ToClean.Air.TransitionView

/-! # Selecting complete message classes and physical rows

Clean exposes channel balance and physical tables, but has no transport from global balance to
a subset selected solely by message contents. This addition preserves the characteristic count
bound, provides a typed selector for raw payloads, and selects physical rows at an explicit
shared data environment. A selection must preserve the component's fixed-column contract; it
does not claim that the selected rows derive the original ensemble's data. The intended upstream homes are
`Clean/Air/Balance.lean` and `Clean/Air/FlatComponent.lean`.
-/

@[expose] public section

variable {F : Type}

section Balance
variable [FiniteField F]

/-- Selecting by payload retains either every occurrence of a message or none of them. -/
theorem balanceOf_filter_messages (interactions : List (Interaction F)) (keep : Array F → Bool)
    (message : Array F) :
    balanceOf (interactions.filter fun interaction => keep interaction.msg) message =
      if keep message then balanceOf interactions message else 0 := by
  induction interactions with
  | nil => simp [balanceOf]
  | cons head rest ih =>
    by_cases same : head.msg = message
    · simp only [List.filter_cons, balanceOf_cons, same]
      cases selected : keep message <;> simp [selected, balanceOf_cons, same, ih]
    · cases selected : keep head.msg <;> cases wanted : keep message <;>
        simp [selected, wanted, balanceOf_cons, same, ih]

/-- Global balance restricts to any class of complete payloads, with its count guard intact. -/
theorem BalancedInteractions.filter_messages {interactions : List (Interaction F)}
    (balanced : BalancedInteractions interactions) (keep : Array F → Bool) :
    BalancedInteractions (interactions.filter fun interaction => keep interaction.msg) := by
  refine ⟨?_, ?_⟩
  · exact balanced.1.imp (lt_of_le_of_lt (List.length_filter_le ..)) id
  · intro message
    rw [balanceOf_filter_messages, balanced.2]
    simp

end Balance

namespace ProvableType

variable {Message : TypeMap} [ProvableType Message]

/-- Decode only correctly sized payloads when selecting a typed message class. -/
def selectMessage (keep : Message F → Bool) (message : Array F) : Bool :=
  if bound : message.size = size Message then keep (fromElements ⟨message, bound⟩) else false

theorem selectMessage_toElements (keep : Message F → Bool) (message : Message F) :
    selectMessage keep (toElements message).toArray = keep message := by
  simp only [selectMessage, Vector.size_toArray, ↓reduceDIte]
  exact congrArg keep (fromElements_toElements message)

end ProvableType

namespace Air.Flat.Table

variable [FiniteField F]

/-- Retain complete physical rows at shared data, with the fixed-column contract checked for
the selected row sequence. No new canonical prover-data agreement is asserted. -/
def filterRows (table : Table F) (data : ProverData F) (keep : Environment F → Bool)
    (fixed : table.component.fixedRowsMatch
      (table.table.filter fun row => keep (Environment.fromArray row data))) : Table F :=
  { table with
    table := table.table.filter fun row => keep (Environment.fromArray row data)
    uniform_width := fun row member => table.uniform_width row (List.mem_filter.mp member).1
    fixed_rows_match := fixed }

theorem filterRows_spec (table : Table F) (data : ProverData F) (keep : Environment F → Bool)
    (fixed : table.component.fixedRowsMatch
      (table.table.filter fun row => keep (Environment.fromArray row data)))
    (valid : table.Spec data) : (table.filterRows data keep fixed).Spec data := by
  intro row member
  exact valid row (List.mem_filter.mp member).1

/-- A homogeneous row is retained exactly when its actual interactions are selected. -/
theorem filterRows_interactions (table : Table F) (data : ProverData F) (channel : RawChannel F)
    (keep : Environment F → Bool)
    (fixed : table.component.fixedRowsMatch
      (table.table.filter fun row => keep (Environment.fromArray row data)))
    (select : Array F → Bool)
    (homogeneous : ∀ row ∈ table.table, ∀ interaction ∈
      table.component.operations.interactionValuesWith channel (Environment.fromArray row data),
      select interaction.msg = keep (Environment.fromArray row data)) :
    (table.filterRows data keep fixed).interactionsWith data channel =
      (table.interactionsWith data channel).filter (fun interaction => select interaction.msg) := by
  simp only [interactionsWith, filterRows]
  clear fixed
  generalize table.table = rows at homogeneous ⊢
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have same := homogeneous row (List.mem_cons_self ..)
    have rest := ih (fun other member => homogeneous other (List.mem_cons_of_mem _ member))
    have selected :
        (table.component.operations.interactionValuesWith channel (Environment.fromArray row data)).filter
          (fun interaction => select interaction.msg) =
        if keep (Environment.fromArray row data) then
          table.component.operations.interactionValuesWith channel (Environment.fromArray row data) else [] := by
      rw [List.filter_congr (fun interaction present => same interaction present)]
      cases keep (Environment.fromArray row data) <;> simp
    simp only [List.filter_cons, List.flatMap_cons, List.filter_append]
    rw [selected]
    obtain hk | hk := Bool.eq_false_or_eq_true (keep (Environment.fromArray row data)) <;>
      simp [hk, rest]

end Air.Flat.Table

namespace Air.Flat.TransitionView

variable [FiniteField F]
variable {Index : Type*}

/-- A transition preserving a message class can be selected as a whole physical row. -/
theorem filterRows_interactions {Message : TypeMap} [ProvableType Message] {channel : Channel F Message}
    (view : TransitionView channel) (table : Table F) (data : ProverData F) (aligned : view.component = table.component)
    (keep : Message F → Bool)
    (fixed : table.component.fixedRowsMatch
      (table.table.filter fun row => keep (view.edge (Environment.fromArray row data)).1))
    (preserved : ∀ env, keep (view.edge env).2 = keep (view.edge env).1) :
    (table.filterRows data (fun env => keep (view.edge env).1) fixed).interactionsWith data channel.toRaw =
      (table.interactionsWith data channel.toRaw).filter
        (fun interaction => ProvableType.selectMessage keep interaction.msg) := by
  apply table.filterRows_interactions
  intro physical _ interaction member
  rw [← aligned, view.interactions] at member
  rcases List.mem_cons.mp member with equal | member
  · rw [equal]
    exact ProvableType.selectMessage_toElements _ _
  · rw [List.mem_singleton.mp member]
    exact (ProvableType.selectMessage_toElements _ _).trans (preserved _)

/-- Select a row class separately in each registered component, retaining empty tables.
Each selected sequence must still realize its component's fixed columns. -/
def selectTables (indices : List Index) (tables : List (Table F)) (data : ProverData F)
    (keep : Index → Environment F → Bool)
    (fixed : ∀ index table, (index, table) ∈ indices.zip tables →
      table.component.fixedRowsMatch
        (table.table.filter fun row => keep index (Environment.fromArray row data))) : List (Table F) :=
  match indices, tables with
  | index :: indices, table :: tables =>
    table.filterRows data (keep index) (fixed index table (List.mem_cons_self ..)) ::
      selectTables indices tables data keep
        (fun index table member => fixed index table (List.mem_cons_of_mem _ member))
  | _, _ => []

theorem selectTables_aligned (indices : List Index) (tables : List (Table F)) (data : ProverData F)
    (component : Index → Component F) (keep : Index → Environment F → Bool)
    (fixed : ∀ index table, (index, table) ∈ indices.zip tables →
      table.component.fixedRowsMatch
        (table.table.filter fun row => keep index (Environment.fromArray row data)))
    (aligned : List.Forall₂ (fun index table => component index = table.component) indices tables) :
    List.Forall₂ (fun index table => component index = table.component) indices
      (selectTables indices tables data keep fixed) := by
  induction aligned with
  | nil => exact .nil
  | cons same _ ih => exact .cons same (ih _)

theorem selectTables_spec (indices : List Index) (tables : List (Table F)) (data : ProverData F)
    (keep : Index → Environment F → Bool)
    (fixed : ∀ index table, (index, table) ∈ indices.zip tables →
      table.component.fixedRowsMatch
        (table.table.filter fun row => keep index (Environment.fromArray row data)))
    (valid : ∀ table ∈ tables, table.Spec data) :
    ∀ table ∈ selectTables indices tables data keep fixed, table.Spec data := by
  induction indices generalizing tables with
  | nil => simp [selectTables]
  | cons index indices ih =>
    cases tables with
    | nil => simp [selectTables]
    | cons table tables =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | member
      · exact table.filterRows_spec data (keep index) _ (valid table (List.mem_cons_self ..))
      · exact ih tables _ (fun other present => valid other (List.mem_cons_of_mem _ present)) selected member

/-- Selection commutes with decoding and preserves physical occurrences and their order. -/
theorem readIndexedRows_selectTables (indices : List Index) (tables : List (Table F)) (data : ProverData F)
    (keep : Index → Environment F → Bool)
    (fixed : ∀ index table, (index, table) ∈ indices.zip tables →
      table.component.fixedRowsMatch
        (table.table.filter fun row => keep index (Environment.fromArray row data))) :
    readIndexedRows indices (selectTables indices tables data keep fixed) data =
      (readIndexedRows indices tables data).filter (fun (index, env) => keep index env) := by
  induction indices generalizing tables with
  | nil => simp [readIndexedRows, selectTables]
  | cons index indices ih =>
    cases tables with
    | nil => simp [readIndexedRows, selectTables]
    | cons table tables =>
      simp only [selectTables, readIndexedRows, List.zip_cons_cons, List.flatMap_cons,
        List.filter_append] at ih ⊢
      rw [ih]
      congr 1
      simp only [Table.filterRows, List.filter_map, Function.comp_def]

/-- Selecting physical rows preserves the source of every interaction, on any channel. -/
theorem selectTables_interactions_sublist (indices : List Index) (tables : List (Table F))
    (data : ProverData F) (component : Index → Component F) (keep : Index → Environment F → Bool)
    (fixed : ∀ index table, (index, table) ∈ indices.zip tables →
      table.component.fixedRowsMatch
        (table.table.filter fun row => keep index (Environment.fromArray row data)))
    (channel : RawChannel F)
    (aligned : List.Forall₂ (fun index table => component index = table.component) indices tables) :
    ((selectTables indices tables data keep fixed).flatMap (·.interactionsWith data channel)).Sublist
      (tables.flatMap (·.interactionsWith data channel)) := by
  rw [readIndexedRows_interactions indices component _ data channel
    (selectTables_aligned indices tables data component keep fixed aligned),
    readIndexedRows_interactions indices component tables data channel aligned,
    readIndexedRows_selectTables]
  exact List.filter_sublist.flatMap _

end Air.Flat.TransitionView
