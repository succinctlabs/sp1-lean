import SP1Clean.Proofs.Completeness.Assembly

/-!
# Chronological events and registry-indexed table buckets

The semantic compiler produces one instruction occurrence per located Sail transition, in
execution order.  The physical ensemble stores those occurrences table-by-table.  This file is
the single bridge between the two views: `RoutedEvent` is one dependent event paired with its
canonical `InstructionChipId`, and `EventBuckets.ofChronological` is a stable `filterMap` into the
registry-indexed family consumed by `SupportedCoreTraceWitness`.

The bucket family is derived, not stored beside the chronological list.  Consequently there is no
second routing table and no proof obligation saying two independently maintained representations
agree.  The lemmas below expose the exact membership and length properties needed by the compiler
and footprint arguments.
-/

namespace SP1Clean.TraceGen

/-- One semantic instruction event together with the native table selected for it. -/
structure RoutedEvent where
  id : InstructionChipId
  event : id.Event

namespace RoutedEvent

/-- Project a routed event at one requested registry identity.  A mismatched identity is absent;
on a match the dependent payload is transported along the proved identity equality. -/
def forId? (routed : RoutedEvent) (requested : InstructionChipId) :
    Option requested.Event :=
  if h : routed.id = requested then
    some (cast (congrArg InstructionChipId.Event h) routed.event)
  else
    none

@[simp] theorem forId?_self (id : InstructionChipId) (event : id.Event) :
    (RoutedEvent.mk id event).forId? id = some event := by
  simp [forId?]

theorem forId?_eq_none_of_ne (routed : RoutedEvent) {requested : InstructionChipId}
    (ne : routed.id ≠ requested) : routed.forId? requested = none := by
  simp [forId?, ne]

theorem forId?_eq_some_iff {routed : RoutedEvent} {requested : InstructionChipId}
    {event : requested.Event} :
    routed.forId? requested = some event ↔
      ∃ h : routed.id = requested,
        cast (congrArg InstructionChipId.Event h) routed.event = event := by
  unfold forId?
  split
  · rename_i h
    simp only [Option.some.injEq]
    exact ⟨fun eq => ⟨h, eq⟩, fun ⟨_, eq⟩ => eq⟩
  · rename_i h
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨eq, _⟩
      exact (h eq).elim

end RoutedEvent

/-- Registry-indexed event lists in physical instruction-table order. -/
abbrev EventBuckets := (id : InstructionChipId) → List id.Event

namespace EventBuckets

/-- Stable partition of a chronological routed stream into native instruction tables. -/
def ofChronological (events : List RoutedEvent) : EventBuckets :=
  fun id => events.filterMap fun routed => routed.forId? id

@[simp] theorem ofChronological_nil (id : InstructionChipId) :
    ofChronological [] id = [] := rfl

@[simp] theorem ofChronological_cons (routed : RoutedEvent) (events : List RoutedEvent)
    (id : InstructionChipId) :
    ofChronological (routed :: events) id =
      (routed.forId? id).toList ++ ofChronological events id := by
  unfold ofChronological
  cases projected : routed.forId? id <;> simp [List.filterMap, projected]

@[simp] theorem ofChronological_cons_self (id : InstructionChipId) (event : id.Event)
    (events : List RoutedEvent) :
    ofChronological (RoutedEvent.mk id event :: events) id =
      event :: ofChronological events id := by
  simp [ofChronological]

theorem mem_ofChronological_iff {events : List RoutedEvent} {id : InstructionChipId}
    {event : id.Event} :
    event ∈ ofChronological events id ↔
      ∃ routed ∈ events, routed.forId? id = some event := by
  simp [ofChronological, List.mem_filterMap]

/-- Every bucket member comes from one chronological occurrence with the requested route. -/
theorem exists_chronological_of_mem {events : List RoutedEvent} {id : InstructionChipId}
    {event : id.Event} (member : event ∈ ofChronological events id) :
    ∃ routed ∈ events, ∃ h : routed.id = id,
      cast (congrArg InstructionChipId.Event h) routed.event = event := by
  rw [mem_ofChronological_iff] at member
  obtain ⟨routed, routedMem, projected⟩ := member
  exact ⟨routed, routedMem, RoutedEvent.forId?_eq_some_iff.mp projected⟩

/-- Stable bucketing never creates more occurrences than the chronological compiler emitted. -/
theorem length_le (events : List RoutedEvent) (id : InstructionChipId) :
    (ofChronological events id).length ≤ events.length := by
  induction events with
  | nil => simp [ofChronological]
  | cons routed events ih =>
      rw [ofChronological_cons]
      cases routed.forId? id <;> simp <;> omega

/-- Bucketing commutes with chronological concatenation. -/
theorem ofChronological_append (left right : List RoutedEvent) (id : InstructionChipId) :
    ofChronological (left ++ right) id =
      ofChronological left id ++ ofChronological right id := by
  simp [ofChronological]

end EventBuckets

end SP1Clean.TraceGen
