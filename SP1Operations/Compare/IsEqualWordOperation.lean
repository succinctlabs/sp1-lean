import SP1Operations.Compare.IsEqualWordOperation.Constraints

namespace IsEqualWordOperation

@[grind →, aesop safe forward]
lemma spec
  {a b : Word (Fin BB)}
  {cols : IsEqualWordOperation} :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    cols.is_diff_zero.result = if a = b then 1 else 0
  := by simp [constraints]; grind

end IsEqualWordOperation
