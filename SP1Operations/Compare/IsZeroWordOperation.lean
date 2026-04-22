import SP1Operations.Compare.IsZeroWordOperation.Constraints

namespace IsZeroWordOperation

attribute [local simp ← high] Word.eq_pointwise

@[grind →, aesop safe forward]
lemma spec
  {a : Word (Fin KB)}
  {cols : IsZeroWordOperation} :
  List.Forall SP1Constraint.toProp (constraints a cols 1) →
    cols.result = if a = #v[(0 : Fin KB), (0 : Fin KB), (0 : Fin KB), (0 : Fin KB)] then 1 else 0
  := by simp [constraints]; grind

lemma spec.gen
  {a : Word (Fin KB)}
  {cols : IsZeroWordOperation}
  {is_real : Fin KB} :
  List.Forall SP1Constraint.toProp (constraints a cols is_real) →
    is_real = 1 →
      cols.result = if a = #v[(0 : Fin KB), (0 : Fin KB), (0 : Fin KB), (0 : Fin KB)] then 1 else 0
  := by simp [constraints]; intros; subst_vars; grind

end IsZeroWordOperation
