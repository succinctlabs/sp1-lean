import SP1Clean.Soundness.HostHintReadHandoff
import SP1Clean.Proofs.Operations.HintQueueWordSource
import ToClean.Air.Authentication

/-! # Immutable hint-record source contracts

Fixed source lookups establish both canonical representations and binding to the complete
source queue. Binding survives persistent store extension. Unit consumers cannot supply records
of their own. Dynamic allocation providers use the physical-table authentication interface,
which can consume prior grounding facts rather than demanding a proof from raw constraints
alone. Neither current queue heads nor RAM predecessor currency is assumed here.
-/

namespace SP1Clean.Soundness.HostHintRecordSources

open Circuit Air.Flat Model.Core Model.Core.HintQueue HostHintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Only sources must prove canonical, immutable contents; pulls and padding impose no content premise. -/
structure Authenticates (store : Store) (component : Component (ZMod p)) : Prop where
  node : component.Authenticates nodeChannel (fun record => record.Valid ∧ record.Binds store)
  word : component.Authenticates wordChannel (fun record => record.Valid ∧ record.Binds store)

omit [Fact (2 ^ 25 < p)] in
theorem Authenticates.extend {old new : Store} {component : Component (ZMod p)}
    (extension : Extends old new) (authenticated : Authenticates old component) :
    Authenticates new component :=
  ⟨authenticated.node.mono (fun _ valid => ⟨valid.1, valid.2.extend extension⟩),
    authenticated.word.mono (fun _ valid => ⟨valid.1, valid.2.extend extension⟩)⟩

omit [Fact (2 ^ 25 < p)] in
private theorem lookup_spec {Row : TypeMap} [ProvableType Row] (table : StaticTable (ZMod p) Row)
    (input : Var Row (ZMod p)) (env : Environment (ZMod p))
    (checked : (⟨table.toTable.toRaw, toElements (M := Row) input⟩ : Lookup (ZMod p)).Contains env) :
    table.Spec (eval env input) := by
  apply table.contains_iff _ |>.mp
  change (∃ index, fromElements (M := Row) ((toElements (M := Row) input).map (Expression.eval env)) = table.row index) at checked
  rwa [ProvableType.fromElements_eval_toElements] at checked

theorem source_node_checked (hints : List Bytes) (env : Environment (ZMod p))
    (checked : ({ circuit := HostHintQueue.source hints } : Component (ZMod p)).operations.ConstraintsHold env) :
    (valueFromOffset NodeRecord 0 env).Valid ∧ (valueFromOffset NodeRecord 0 env).Binds (ofList hints).1 := by
  apply sourceTable_sound hints
  rw [← eval_varFromOffset_valueFromOffset NodeRecord 0 env]
  apply lookup_spec
  rw [Component.constraintsHold_iff] at checked
  simpa only [Component.rowOperations, HostHintQueue.source, sourceMain, circuit_norm] using checked

theorem source_word_checked (hints : List Bytes) (env : Environment (ZMod p))
    (checked : ({ circuit := sourceWord hints } : Component (ZMod p)).operations.ConstraintsHold env) :
    (valueFromOffset WordRecord 0 env).Valid ∧ (valueFromOffset WordRecord 0 env).Binds (ofList hints).1 := by
  apply sourceWordTable_sound hints
  rw [← eval_varFromOffset_valueFromOffset WordRecord 0 env]
  apply lookup_spec
  rw [Component.constraintsHold_iff] at checked
  simpa only [Component.rowOperations, sourceWord, sourceWordMain, circuit_norm] using checked

theorem source_node_authenticates (hints : List Bytes) :
    Authenticates (ofList hints).1 ({ circuit := HostHintQueue.source (p := p) hints } : Component (ZMod p)) := by
  constructor
  · intro env checked interaction member _ _
    rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
    change interaction ∈ ((sourceMain hints (varFromOffset NodeRecord 0)).operations
      (size NodeRecord)).interactionValuesWith nodeChannel.toRaw env at member
    rw [source_node_values, eval_varFromOffset_valueFromOffset] at member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨valueFromOffset NodeRecord 0 env, rfl, source_node_checked hints env checked⟩
  · apply Component.Authenticates.of_silent
    change wordChannel.toRaw ∉ [nodeChannel.toRaw]
    simp [nodeChannel, wordChannel, Channel.toRaw]

theorem source_word_authenticates (hints : List Bytes) :
    Authenticates (ofList hints).1 ({ circuit := sourceWord (p := p) hints } : Component (ZMod p)) := by
  constructor
  · apply Component.Authenticates.of_silent
    change nodeChannel.toRaw ∉ [wordChannel.toRaw]
    simp [nodeChannel, wordChannel, Channel.toRaw]
  · intro env checked interaction member _ _
    rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
    change interaction ∈ ((sourceWordMain hints (varFromOffset WordRecord 0)).operations
      (size WordRecord)).interactionValuesWith wordChannel.toRaw env at member
    rw [source_word_values, eval_varFromOffset_valueFromOffset] at member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨valueFromOffset WordRecord 0 env, rfl, source_word_checked hints env checked⟩

theorem handler_authenticates (store : Store) :
    Authenticates store (HostHintReadCoverage.handler (p := p)) := by
  constructor
  · apply Component.Authenticates.of_pulls
    intro env _ interaction member
    rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
    change interaction ∈ (((HostHintReadChip.main (varFromOffset HostHintReadChip.Inputs 0)).operations
      (size HostHintReadChip.Inputs)).interactionsWith nodeChannel.toRaw).map _ at member
    rw [HostHintReadChip.main_node_interactions] at member
    obtain rfl := List.mem_singleton.mp member
    exact Or.inr (by simp only [Channel.eval_pulled, Channel.pulledValue])
  · apply Component.Authenticates.of_pulls
    intro env _ interaction member
    rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
    change interaction ∈ (((HostHintReadChip.main (varFromOffset HostHintReadChip.Inputs 0)).operations
      (size HostHintReadChip.Inputs)).interactionsWith wordChannel.toRaw).map _ at member
    rw [HostHintReadChip.main_word_interactions] at member
    obtain rfl := List.mem_singleton.mp member
    exact Or.inr (by simp only [Channel.eval_pulled, Channel.pulledValue])

theorem word_consumer_authenticates (store : Store) (last : Bool) :
    Authenticates store (HintReadCoverage.view (p := p) last).component := by
  constructor
  · apply Component.Authenticates.of_silent
    intro used
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    cases last <;> change false = true at present <;> contradiction
  · apply Component.Authenticates.of_pulls
    intro env _ interaction member
    rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
    change interaction ∈ (((HintReadWordChip.main last (varFromOffset HintReadWordChip.Inputs 0)).operations
      (size HintReadWordChip.Inputs)).interactionsWith wordChannel.toRaw).map _ at member
    rw [HintReadWordChip.main_word_interactions] at member
    obtain rfl := List.mem_singleton.mp member
    exact Or.inr (by simp only [Channel.eval_pulled, Channel.pulledValue])

theorem hint_length_authenticates (store : Store) (empty : Bool) :
    Authenticates store (HostCallReceivers.hintLength (p := p) empty).component := by
  constructor
  · apply Component.Authenticates.of_pulls
    intro env _ interaction member
    rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
    change interaction ∈ ((HostHintLengthChip.main empty (varFromOffset HostHintLengthChip.Inputs 0)).operations
      (size HostHintLengthChip.Inputs)).interactionValuesWith nodeChannel.toRaw env at member
    rw [HostHintLengthChip.node_values] at member
    cases empty
    · obtain rfl := List.mem_singleton.mp member
      exact Or.inr rfl
    · contradiction
  · apply Component.Authenticates.of_silent
    intro used
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    cases empty <;> change false = true at present <;> contradiction

private theorem control_authenticates (store : Store) (component : Component (ZMod p))
    (member : component ∈ ([HostCallReceivers.halt, HostCallReceivers.enter] ++
      (List.ofFn fun slot => HostCallReceivers.commit false slot) ++
      (List.ofFn fun slot => HostCallReceivers.commit true slot)).map
        (fun view : HostLocalHandoff.Receiver (p := p) => view.component)) :
    Authenticates store component := by
  have checked : (([HostCallReceivers.halt, HostCallReceivers.enter] ++
      (List.ofFn fun slot => HostCallReceivers.commit (p := p) false slot) ++
      (List.ofFn fun slot => HostCallReceivers.commit true slot)).map
        (fun view : HostLocalHandoff.Receiver (p := p) => view.component)).all (fun component : Component (ZMod p) =>
        !(component.circuit.channels.map RawChannel.name).contains (nodeChannel (p := p)).toRaw.name &&
        !(component.circuit.channels.map RawChannel.name).contains (wordChannel (p := p)).toRaw.name) = true := rfl
  have silent := List.all_eq_true.mp checked component member
  simp only [Bool.and_eq_true] at silent
  constructor
  all_goals
    apply Component.Authenticates.of_silent
    intro used
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    simp only [present, Bool.not_true, Bool.false_eq_true, false_and, and_false] at silent

theorem available_authenticates (store : Store) (component : Component (ZMod p))
    (member : component ∈ (HostCallReceivers.available (p := p)).map (·.component)) :
    Authenticates store component := by
  change component ∈ (([HostCallReceivers.halt, HostCallReceivers.enter] ++
    (List.ofFn fun slot => HostCallReceivers.commit false slot) ++
    (List.ofFn fun slot => HostCallReceivers.commit true slot)) ++
      [HostCallReceivers.hintLength false, HostCallReceivers.hintLength true]).map
        (fun view : HostLocalHandoff.Receiver (p := p) => view.component) at member
  rw [List.map_append, List.mem_append] at member
  rcases member with control | length
  · exact control_authenticates store component control
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at length
    rcases length with rfl | rfl
    · exact hint_length_authenticates store false
    · exact hint_length_authenticates store true

end SP1Clean.Soundness.HostHintRecordSources
