import SP1Operations.Compare.IsZeroWordOperation.Constraints

namespace IsZeroWordOperation

attribute [local simp ← high] Word.eq_pointwise

@[grind →, aesop safe forward]
lemma spec_poly {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
  {a : Word (ZMod p)}
  {cols : IsZeroWordOperation (ZMod p)} :
  List.Forall SP1Constraint.toProp (constraints a cols 1) →
    cols.result = if a = #v[(0 : ZMod p), (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] then 1 else 0
  := by simp [constraints]; grind

end IsZeroWordOperation
