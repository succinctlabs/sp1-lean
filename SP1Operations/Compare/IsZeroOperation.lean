import SP1Operations.Compare.IsZeroOperation.Constraints

namespace IsZeroOperation

@[grind →, aesop safe forward]
lemma spec_poly {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
  {a : ZMod p}
  {cols : IsZeroOperation (ZMod p)} :
  List.Forall SP1Constraint.toProp_poly (constraints a cols 1) →
    cols.result = if (a = 0) then 1 else 0
  := by simp [constraints]; grind

end IsZeroOperation
