import SP1Operations.Compare.IsZeroOperation.Constraints

namespace IsZeroOperation

@[grind →, aesop safe forward]
lemma spec
  {a : Fin KB}
  {cols : IsZeroOperation (Fin KB)} :
  List.Forall SP1Constraint.toProp (constraints a cols 1) →
    cols.result = if (a = 0) then 1 else 0
  := by simp [constraints]; grind

/-- Polymorphic counterpart of `spec` over `ZMod p`. Demonstrates that
the `toProp_poly` lift (sub-phase B.4 of `docs/FIELD_GENERIC.md`) lets
operation iff lemmas state field-genericity at `Field`/`ZMod p` level
without pinning to `Fin KB`. -/
@[grind →, aesop safe forward]
lemma spec_poly {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
  {a : ZMod p}
  {cols : IsZeroOperation (ZMod p)} :
  List.Forall SP1Constraint.toProp_poly (constraints a cols 1) →
    cols.result = if (a = 0) then 1 else 0
  := by simp [constraints]; grind

end IsZeroOperation
