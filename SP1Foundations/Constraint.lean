import SP1Foundations.Field
import SP1Foundations.ByteOpcode

inductive AirInteraction.Kind where
  | BYTE
  | MEMORY
  | PROGRAM
  | STATE

inductive SP1Constraint where
  /-- Assertion that a particular value is zero. -/
  | assertZero (x : BabyBear)
  /-- Sending air interactions with `kind == byte` -/
  | sendAirInteraction_byte (op : ByteOpcode) (x y z : BabyBear) (mult : ℕ)
  -- TODO: other air interactions

instance : DecidableEq SP1Constraint
  | (SP1Constraint.assertZero x), (SP1Constraint.assertZero y) => sorry
  | _, _ => sorry

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

section constraintSet

-- TODO: should this exist? maybe even as `abbrev`?
@[reducible] def constraintSet := Finset SP1Constraint

/-- Covert a set of constraints to a single proposition stating that they all hold. -/
def constraintSet_toProp (cs : Finset SP1Constraint) : Prop :=
  ∀ constraint ∈ cs, constraint.toProp

@[simp] lemma constraintSet_toProp_empty : constraintSet_toProp ∅ = True := by
  simp [constraintSet_toProp]

@[simp] lemma constraintSet_toProp_singleton (c : SP1Constraint) : constraintSet_toProp {c} = c.toProp := by
  simp [constraintSet_toProp]

@[simp] lemma constraintSet_toProp_insert (c : SP1Constraint) (cs : Finset SP1Constraint) :
    constraintSet_toProp (insert c cs) = (c.toProp ∧ constraintSet_toProp cs) := by
  simp [constraintSet_toProp]

lemma toProp_of_mem_constraintSet (cs : Finset SP1Constraint) (c : SP1Constraint) :
    c ∈ cs → constraintSet_toProp cs → c.toProp := by
  sorry

/-- A larger set of constraints `cs'` implies a smaller set of constraints `cs`. -/
lemma toProp_imp_of_constraintSet_subset' (cs cs' : Finset SP1Constraint)
    (h : cs ⊆ cs') : constraintSet_toProp cs' → constraintSet_toProp cs := by
  refine fun csp c h' => csp c (h h')

end constraintSet
