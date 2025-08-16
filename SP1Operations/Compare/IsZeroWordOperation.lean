import SP1Operations.Compare.IsZeroWordOperation.Constraints

namespace IsZeroWordOperation

attribute [simp ← high] Word.eq_pointwise

@[grind →, aesop safe forward]
lemma spec
  {a : Word (Fin BB)}
  {cols : IsZeroWordOperation} :
  List.Forall SP1Constraint.toProp (constraints a cols 1) →
    cols.result = if a = #v[(0 : Fin BB), (0 : Fin BB), (0 : Fin BB), (0 : Fin BB)] then 1 else 0
  := by simp [constraints]; grind

end IsZeroWordOperation
