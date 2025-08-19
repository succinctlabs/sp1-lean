import SP1Operations.Compare.IsZeroOperation.Constraints

namespace IsZeroOperation

@[grind →, aesop safe forward]
lemma spec
  {a : Fin BB}
  {cols : IsZeroOperation} :
  List.Forall SP1Constraint.toProp (constraints a cols 1) →
    cols.result = if (a = 0) then 1 else 0
  := by simp [constraints]; grind

end IsZeroOperation
