import SP1Operations.Compare.IsEqualWordOperation.Constraints

namespace IsEqualWordOperation

attribute [local simp ← high] Word.eq_pointwise

@[grind →, aesop safe forward]
lemma spec
  {a b : Word (Fin BB)}
  {cols : IsEqualWordOperation} :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    cols.is_diff_zero.result = if a = b then 1 else 0
  := by simp [constraints]; grind

lemma spec.gen
  {a b : Word (Fin BB)}
  {cols : IsEqualWordOperation}
  {is_real : Fin BB} :
  List.Forall SP1Constraint.toProp (constraints a b cols is_real) →
    is_real = (1 : Fin BB) →
      cols.is_diff_zero.result = if a = b then 1 else 0
  := by simp [constraints]; grind

end IsEqualWordOperation
