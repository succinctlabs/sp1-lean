import SP1Operations.Compare.U16CompareOperation.Operation
import SP1Operations.Compare.U16CompareOperation.Constraints

namespace U16CompareOperation

@[grind →, aesop safe forward]
lemma spec
  (a b : Fin BB)
  (cols : U16CompareOperation)
  (h_a_isU16 : (a : ℕ) < 65536)
  (h_b_isU16 : (b : ℕ) < 65536) :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    (cols.bit = if (a : ℕ) < b then 1 else 0)
  := by simp [constraints]; grind

end U16CompareOperation
