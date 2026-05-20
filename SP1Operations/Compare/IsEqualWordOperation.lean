import SP1Operations.Compare.IsEqualWordOperation.Constraints

namespace IsEqualWordOperation

attribute [local simp ← high] Word.eq_pointwise

@[grind →, aesop safe forward]
lemma spec_poly {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
  {a b : Word (ZMod p)}
  {cols : IsEqualWordOperation (ZMod p)} :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    cols.is_diff_zero.result = if a = b then 1 else 0
  := by simp [constraints]; grind

lemma spec.gen_poly {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
  {a b : Word (ZMod p)}
  {cols : IsEqualWordOperation (ZMod p)}
  {is_real : ZMod p} :
  List.Forall SP1Constraint.toProp (constraints a b cols is_real) →
    is_real = 1 →
      cols.is_diff_zero.result = if a = b then 1 else 0 := by
  intros h hir
  subst hir
  exact spec_poly h

end IsEqualWordOperation
