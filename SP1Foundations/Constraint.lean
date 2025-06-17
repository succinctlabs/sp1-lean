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
  /-- Assert a constraint from an operation evaluation. -/
  | assertOperationEval (p : Prop)
  | mkOutput (i : ℕ) (x : BabyBear) -- Note: no type polymorphism, only outputs baby bears
  /-- Sending air interactions with `kind == byte` -/
  | sendAirInteraction_byte (op : ByteOpcode) (x y z : BabyBear) (mult : ℕ)
  -- TODO: other air interactions

/-- TODO: this isn't actually true anymore, because of `assertOperationEval`.
Would require adding `Decidable p` which makes litterally everywhere else worse. -/
instance : DecidableEq SP1Constraint
  | .assertZero _, .assertZero _ => by
      simp
      infer_instance
  | .assertZero _, .sendAirInteraction_byte _ _ _ _ _ => by
      simp
      exact instDecidableFalse
  | .sendAirInteraction_byte _ _ _ _ _, .assertZero _ => by
      simp
      exact instDecidableFalse
  | _, _ => sorry

namespace SP1Constraint

section toProp

def toProp : SP1Constraint → Prop
  | .assertZero x => x = 0
  | .assertOperationEval p => p
  | .mkOutput i x => True
  | .sendAirInteraction_byte op x y z mult =>
      -- Is this saying enough?
      (mult ≠ 0 → ByteOpcode.constrain op x y z)

/-- Convert a constraint to a `Prop`, relative to some potential list of outputs.
Note that this doesn't "generate" the outputs at this point. -/
def toPropWithOutputs (outputs : List BabyBear) : SP1Constraint → Prop
  | .assertZero x => x = 0
  | .assertOperationEval p => p
  | .mkOutput i x => outputs[i]? = some x -- The `i`th output must be `x` and must exist
  | .sendAirInteraction_byte op x y z mult =>
      -- Is this saying enough?
      (mult ≠ 0 → ByteOpcode.constrain op x y z)

@[simp] lemma toProp_assertZero (x : BabyBear) :
    (assertZero x).toProp ↔ x = 0 := Iff.rfl

@[simp] lemma toProp_assertOperationEval (p : Prop) :
    (assertOperationEval p).toProp ↔ p := Iff.rfl

@[simp] lemma toProp_sendAirInteration_byte (op : ByteOpcode)
    (x y z : BabyBear) (mult : ℕ) :
    (sendAirInteraction_byte op x y z mult).toProp ↔
      (mult ≠ 0 → ByteOpcode.constrain op x y z) := Iff.rfl

end toProp

end SP1Constraint

section SP1ConstraintSet

-- TODO: should this exist? maybe just as `abbrev`?
@[reducible] def SP1ConstraintSet := Finset SP1Constraint

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

end SP1ConstraintSet
