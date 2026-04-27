import SP1Operations.Compare.IsZeroWordOperation.Constraints

namespace IsZeroWordOperation

attribute [local simp ← high] Word.eq_pointwise

@[grind →, aesop safe forward]
lemma spec
  {a : Word (Fin KB)}
  {cols : IsZeroWordOperation (Fin KB)} :
  List.Forall SP1Constraint.toProp (constraints a cols 1) →
    cols.result = if a = #v[(0 : Fin KB), (0 : Fin KB), (0 : Fin KB), (0 : Fin KB)] then 1 else 0
  := by simp [constraints]; grind

lemma spec.gen
  {a : Word (Fin KB)}
  {cols : IsZeroWordOperation (Fin KB)}
  {is_real : Fin KB} :
  List.Forall SP1Constraint.toProp (constraints a cols is_real) →
    is_real = 1 →
      cols.result = if a = #v[(0 : Fin KB), (0 : Fin KB), (0 : Fin KB), (0 : Fin KB)] then 1 else 0
  := by simp [constraints]; intros; subst_vars; grind

/-- Polymorphic counterpart of `spec` over `ZMod p`. Pure field-equality
reasoning carries verbatim from the `Fin KB` proof. -/
@[grind →, aesop safe forward]
lemma spec_poly {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
  {a : Word (ZMod p)}
  {cols : IsZeroWordOperation (ZMod p)} :
  List.Forall SP1Constraint.toProp_poly (constraints a cols 1) →
    cols.result = if a = #v[(0 : ZMod p), (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] then 1 else 0
  := by simp [constraints]; grind

end IsZeroWordOperation
