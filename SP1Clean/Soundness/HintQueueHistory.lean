import SP1Clean.Model.Core.HintQueueEvent
import SP1Clean.Proofs.Operations.HintQueueCursor
import SP1Clean.Soundness.Walk

/-! # Lifting a queue-token path to byte-level history

The invariant records the complete current bytes and allocation frontier at every prefix.
Stores may grow along the path while preserving every prior node and remaining inside an
authenticated final inventory. The lifting theorem is independent of the handler registry;
allocating handlers must eventually supply the same local advance proof as observations/pops.
-/

namespace SP1Clean.Soundness.HintQueueHistory

open Model.Core Model.Core.HintQueue HostHintQueue

variable {p : ℕ} {Row : Type*}

/-- Prefix replay fixes the actual current queue, not merely some authentic node in a later store. -/
def Prefixes (edge : Row → State (ZMod p) × State (ZMod p)) (event : Row → Event)
    (path : List Row) (initialStore finalStore : Store) (initialHints : List Bytes) : Prop :=
  ∀ prior row suffix, path = prior ++ row :: suffix →
    ∃ store hints, Extends initialStore store ∧ Extends store finalStore ∧
      replay? (prior.map event) initialHints = some hints ∧ (edge row).1.Binds store hints

/-- A local row may extend the persistent inventory; it must preserve all existing nodes. -/
def Advances (edge : Row → State (ZMod p) × State (ZMod p)) (event : Row → Event)
    (upper : Store) (row : Row) : Prop :=
  ∀ store hints, Extends store upper → (edge row).1.Binds store hints →
    ∃ nextStore nextHints, Extends store nextStore ∧ Extends nextStore upper ∧
      (event row).apply? hints = some nextHints ∧ (edge row).2.Binds nextStore nextHints

/-- The same induction handles identities, observations, pops, and future authenticated allocations. -/
theorem of_walk (edge : Row → State (ZMod p) × State (ZMod p)) (event : Row → Event)
    (path : List Row) (initial final : State (ZMod p)) (store upper : Store) (hints : List Bytes)
    (walk : Walk.IsWalk edge initial final path) (current : initial.Binds store hints)
    (bounded : Extends store upper) (steps : ∀ row ∈ path, Advances edge event upper row) :
    ∃ finalStore finalHints, Extends store finalStore ∧ Extends finalStore upper ∧
      final.Binds finalStore finalHints ∧ replay? (path.map event) hints = some finalHints ∧
      Prefixes edge event path store finalStore hints := by
  induction path generalizing initial store hints with
  | nil =>
    refine ⟨store, hints, .refl _, bounded, ?_, rfl, ?_⟩
    · exact walk ▸ current
    · intro prior row suffix same
      have sizes := congrArg List.length same
      simp only [List.length_nil, List.length_append, List.length_cons] at sizes
      omega
  | cons first rest ih =>
    obtain ⟨nextStore, nextHints, extended, nextBounded, applied, next⟩ :=
      steps first (List.mem_cons_self ..) store hints bounded (walk.1.symm ▸ current)
    obtain ⟨finalStore, finalHints, finalExtends, finalBounded, finalBinding, replayed, prefixes⟩ :=
      ih (edge first).2 nextStore nextHints walk.2 next nextBounded
        (fun row member => steps row (List.mem_cons_of_mem _ member))
    refine ⟨finalStore, finalHints, extended.trans finalExtends, finalBounded, finalBinding, ?_, ?_⟩
    · rw [List.map_cons, replay?_cons, applied, Option.bind_some, replayed]
    · intro prior row suffix same
      cases prior with
      | nil =>
        have rowEq := (List.cons.inj same).1
        refine ⟨store, hints, .refl _, extended.trans finalExtends, rfl, ?_⟩
        exact rowEq ▸ (walk.1.symm ▸ current)
      | cons previous prior =>
        have equal := List.cons.inj same
        obtain ⟨atStore, atHints, atExtends, atBounded, atReplay, atBinding⟩ :=
          prefixes prior row suffix equal.2
        refine ⟨atStore, atHints, extended.trans atExtends, atBounded, ?_, atBinding⟩
        rw [List.map_cons, replay?_cons, ← equal.1, applied, Option.bind_some, atReplay]

end SP1Clean.Soundness.HintQueueHistory
