import SP1Foundations.Field
import SP1Foundations.ByteOpcode

inductive SP1Constraint where
  /-- Assertion that a particular value is real. -/
  | assertZero (x : BabyBear)
  /-- Sending air interactions with `kind == byte` -/
  | sendAirInteraction_byte (op : ByteOpcode)
      (x y z : BabyBear) (mult : ℕ)
  -- TODO: other air interactions

def SP1Constraint.toProp : SP1Constraint → Prop
  | .assertZero x => (x = 0)
  | .sendAirInteraction_byte op x y z mult =>
      (mult ≠ 0 → ByteOpcode.constrain op x y z)

def constraintList_toProp (cs : List SP1Constraint) : Prop :=
  ∀ constraint ∈ cs, constraint.toProp
