import SP1Foundations.Field
import SP1Foundations.ByteOpcode
import SP1Foundations.SailM

inductive AirInteraction where
  | byte (op : ByteOpcode) (a b c : Fin BB)
  | memory (shard clk addr n m limb0 limb1 limb2 limb3 : Fin BB)
  | state (shard clk pc0 pc1 pc2 : Fin BB)
  deriving DecidableEq

inductive SP1Constraint where
  /-- Assertion that a particular value is zero. -/
  | assertZero (x : Fin BB)
  /-- Sending an air interaction -/
  | send (interaction : AirInteraction) (mult : Fin BB)
  /-- Receiving an air interaction -/
  | receive (interaction : AirInteraction) (mult : Fin BB)
  -- | ofList (cs : List SP1Constraint) : SP1Constraint
  deriving DecidableEq

namespace SP1Constraint

section toProp

def toProp : SP1Constraint → Prop
  | .assertZero x => (x = 0)
  | .send (.byte op a b c) mult => mult ≠ 0 → op.constrain a b c
  -- dt: the other send/recv interactions should also imply bounds
  -- should be based on only running "trusted" programs and what that entails.
  | _ => True

@[simp] lemma toProp_assertZero (x : Fin BB) :
    (assertZero x).toProp ↔ x = 0 := Iff.rfl

@[simp] lemma toProp_send_byte (op : ByteOpcode) (a b c : Fin BB) (mult : Fin BB) :
    (send (.byte op a b c) mult).toProp ↔ (mult ≠ 0 → op.constrain a b c) := Iff.rfl

-- dt: change this back once airs work
@[simp] lemma toProp_recv (air : AirInteraction) (mult : Fin BB) :
    (receive air mult).toProp ↔ True := Iff.rfl

end toProp

end SP1Constraint

section constraintList

/-- Wrapper for lists of constraints. Mainly used to namespace lemmas. -/
@[reducible] def SP1ConstraintList := List SP1Constraint

@[simp] protected def SP1ConstraintList.allHold (xs : SP1ConstraintList) : Prop :=
  List.Forall SP1Constraint.toProp xs

lemma allHold_nil : SP1ConstraintList.allHold [] := True.intro

lemma allHold_singleton (c : SP1Constraint) :
    SP1ConstraintList.allHold [c] ↔ c.toProp := Iff.rfl

lemma allHold_cons (c : SP1Constraint) (cs : SP1ConstraintList) :
    SP1ConstraintList.allHold (c :: cs) ↔ c.toProp ∧ SP1ConstraintList.allHold cs :=
  List.forall_cons _ _ _

lemma allHold_append (cs cs' : SP1ConstraintList) :
    SP1ConstraintList.allHold (cs ++ cs') ↔ cs.allHold ∧ cs'.allHold :=
  List.forall_append

end constraintList
