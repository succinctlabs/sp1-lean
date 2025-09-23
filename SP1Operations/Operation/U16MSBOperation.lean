import SP1Foundations
import SP1Operations.Operation.U16MSBOperation.Operation
import SP1Operations.Operation.U16MSBOperation.Constraints

namespace U16MSBOperation

lemma allHold_constraints_iff
  {a : Fin KB}
  {cols : U16MSBOperation}
  {is_real : Fin KB} :
  List.Forall SP1Constraint.toProp (constraints a cols is_real) ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (cols.msb = 0 ∨ cols.msb = 1) ∧
    (¬is_real = 0 → 2 * a - cols.msb * 65536 < 65536)
  := by simp [constraints]; grind

@[grind →, aesop safe forward]
lemma spec
  {a : Fin KB}
  {cols : U16MSBOperation}
  (h_a_isU16 : a < 65536) :
  List.Forall SP1Constraint.toProp (constraints a cols 1) →
    cols.msb = if a >= 32768 then 1 else 0
  := by simp [constraints]; grind

lemma spec.U64
  {w : Word (Fin KB)}
  {cols : U16MSBOperation}
  (h_w_isU64 : w.isU64) :
  List.Forall SP1Constraint.toProp (constraints w[3] cols 1) →
    cols.msb = if w.isNegative then 1 else 0
  := by simp [constraints]; grind

section gen


lemma spec.gen
  {a : Fin KB}
  {cols : U16MSBOperation}
  {is_real : Fin KB}
  (h_a_isU16 : a < 65536) :
  List.Forall SP1Constraint.toProp (constraints a cols is_real) →
    is_real = 1 →
      cols.msb = if a >= 32768 then 1 else 0
  := by simp [constraints]; grind

end gen

end U16MSBOperation
