import SP1Foundations.Field
import SP1Foundations.ByteOpcode

inductive SP1Constraint where
  /-- Assertion that a particular value is real. -/
  | assertZero (x : BabyBear)
  /-- Sending air interactions with `kind == byte` -/
  | sendAirInteraction_byte (op : ByteOpcode)
      (x y z : BabyBear) (mult : ℕ)
  -- TODO: other air interactions

namespace SP1Constraint

def toProp : SP1Constraint → Prop
  | .assertZero x => (x = 0)
  | .sendAirInteraction_byte op x y z mult =>
      -- Is this saying enough?
      (mult ≠ 0 → ByteOpcode.constrain op x y z)

@[simp] lemma toProp_assertZero (x : BabyBear) :
    (assertZero x).toProp ↔ x = 0 := Iff.rfl

@[simp] lemma toProp_sendAirInteration_byte (op : ByteOpcode)
    (x y z : BabyBear) (mult : ℕ) :
    (sendAirInteraction_byte op x y z mult).toProp ↔
      (mult ≠ 0 → ByteOpcode.constrain op x y z) := Iff.rfl

end SP1Constraint

@[reducible] def constraintList_toProp (cs : List SP1Constraint) : Prop :=
  ∀ constraint ∈ cs, constraint.toProp

@[simp] lemma constraintList_toProp_nil :
    constraintList_toProp [] = True := by
  simp [constraintList_toProp]

@[simp] lemma constraintList_toProp_cons (c : SP1Constraint) (cs : List SP1Constraint) :
    constraintList_toProp (c :: cs) = (c.toProp ∧ constraintList_toProp cs) := by
  simp [constraintList_toProp]
