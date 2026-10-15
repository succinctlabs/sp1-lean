module

public import Mathlib.Data.List.Forall2

/-! # Pointwise meaning of successful optional list traversal

## Gap against upstream

Lean supplies `List.mapM_cons`, and Mathlib supplies `List.Forall₂` and its indexed
characterizations. The equivalence between a successful optional traversal and pointwise
successful observations is missing. It lets readers reason about byte sequences without
unfolding nested option binds at each consumer.
-/

public section

namespace List

theorem mapM_option_eq_some_iff {α β : Type*} (f : α → Option β) (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔ Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih =>
      cases found : f x <;> cases ys <;>
        simp [mapM_cons, found, Option.bind_eq_some_iff, ih, and_comm]

end List
