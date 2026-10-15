module

public import ToClean.Air.TransitionView

/-! # Reading unit receivers from physical AIR tables

Clean exposes raw interaction lists but has no adapter from heterogeneous unit receiver
components to their complete typed message inventory. `ReceiverView` records the row-local
ledger equation; `messages_interactions` lifts it over physically aligned tables. The shared
indexed-row reader retains every occurrence, and the sublist theorem transports global message
uniqueness to any registered table. These are pure additions for `Clean/Air/FlatComponent.lean`.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

/-- One physical row consumes exactly one complete typed message. -/
structure ReceiverView (channel : Channel F Message) where
  component : Component F
  message : Environment F → Message F
  interactions : ∀ env, component.operations.interactionValuesWith channel.toRaw env =
    [channel.pulledValue (message env)]

namespace ReceiverView

variable {channel : Channel F Message}

def tableMessages (view : ReceiverView channel) (table : Table F) (data : ProverData F) : List (Message F) :=
  table.table.map fun physical => view.message (Environment.fromArray physical data)

/-- Read every physical occurrence, preserving the registered component identity. -/
def messages (views : List (ReceiverView channel)) (tables : List (Table F)) (data : ProverData F) : List (Message F) :=
  (TransitionView.readIndexedRows views tables data).map fun (view, env) => view.message env

theorem messages_cons (view : ReceiverView channel) (views : List (ReceiverView channel))
    (table : Table F) (tables : List (Table F)) (data : ProverData F) :
    messages (view :: views) (table :: tables) data = tableMessages view table data ++ messages views tables data := by
  simp only [messages, TransitionView.readIndexedRows, List.zip_cons_cons, List.flatMap_cons,
    List.map_append, List.map_map, Function.comp_def, tableMessages]

/-- Split the physical receiver inventory at a registration boundary. -/
theorem messages_take_drop (views : List (ReceiverView channel)) (tables : List (Table F)) (data : ProverData F) (n : ℕ) :
    messages views tables data = messages (views.take n) (tables.take n) data ++
      messages (views.drop n) (tables.drop n) data := by
  unfold messages TransitionView.readIndexedRows
  conv_lhs => rw [← List.take_append_drop n (views.zip tables)]
  simp only [List.zip_eq_zipWith, List.take_zipWith, List.drop_zipWith,
    List.flatMap_append, List.map_append]

theorem aligned_of_map_eq (views : List (ReceiverView channel)) (tables : List (Table F))
    (aligned : views.map (·.component) = tables.map (·.component)) :
    List.Forall₂ (fun view table => view.component = table.component) views tables := by
  have equal : List.Forall₂ (· = ·) (views.map (·.component)) (tables.map (·.component)) := by
    simpa only [List.forall₂_eq_eq_eq] using aligned
  simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using equal

/-- The typed inventory is exactly the complete physical ledger, including multiplicities. -/
theorem messages_interactions (views : List (ReceiverView channel)) (tables : List (Table F)) (data : ProverData F)
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables) :
    tables.flatMap (·.interactionsWith data channel.toRaw) = (messages views tables data).map channel.pulledValue := by
  rw [TransitionView.readIndexedRows_interactions views (·.component) tables data channel.toRaw aligned]
  simp only [interactions, messages, List.map_map, Function.comp_def]
  exact List.flatMap_pure_eq_map _ _

/-- An actual unit pull identifies its complete typed message in the receiver inventory. -/
theorem message_mem_of_pull_mem (views : List (ReceiverView channel)) (tables : List (Table F)) (data : ProverData F)
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (message : Message F)
    (member : channel.pulledValue message ∈ tables.flatMap (·.interactionsWith data channel.toRaw)) :
    message ∈ messages views tables data := by
  rw [messages_interactions views tables data aligned] at member
  obtain ⟨other, present, equal⟩ := List.mem_map.mp member
  have encoded := Vector.toArray_inj.mp (congrArg Interaction.msg equal)
  have same : other = message := by
    simpa only [ProvableType.fromElements_toElements] using congrArg fromElements encoded
  exact same ▸ present

/-- A registered receiver's physical occurrences form a sublist of the complete inventory. -/
theorem tableMessages_sublist (views : List (ReceiverView channel)) (tables : List (Table F)) (data : ProverData F)
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (index : ℕ) (bound : index < views.length) :
    (tableMessages views[index] (tables[index]'(by rw [← aligned.length_eq]; exact bound)) data).Sublist
      (messages views tables data) := by
  induction aligned generalizing index with
  | nil => simp at bound
  | @cons view table views tables same aligned ih =>
    cases index with
    | zero =>
      simp only [List.getElem_cons_zero, messages_cons]
      exact List.sublist_append_left _ _
    | succ index =>
      simp only [List.getElem_cons_succ, messages_cons]
      exact (ih index (by simpa using bound)).trans (List.sublist_append_right _ _)

/-- Global message-key uniqueness applies to every physical row of any registered receiver. -/
theorem tableMessages_keys_nodup {Key : Type*} (views : List (ReceiverView channel))
    (tables : List (Table F)) (data : ProverData F)
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (key : Message F → Key) (unique : ((messages views tables data).map key).Nodup)
    (index : ℕ) (bound : index < views.length) :
    ((tableMessages views[index] (tables[index]'(by rw [← aligned.length_eq]; exact bound)) data).map key).Nodup :=
  unique.sublist ((tableMessages_sublist views tables data aligned index bound).map key)

end ReceiverView
end Air.Flat
