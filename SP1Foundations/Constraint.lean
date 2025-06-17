import SP1Foundations.Field
import SP1Foundations.ByteOpcode

inductive AirInteraction.Kind where
  | BYTE
  | MEMORY
  | PROGRAM
  | STATE

inductive AirInteraction where
  | byte (op : ByteOpcode) (a b c : BabyBear)
  /--
  Represents an InteractionKind::Memory.
  shard -> clk -> addr -> low_limb -> high_limb
  -/
  | memory (shard clk addr low_limb high_limb : BabyBear)
  /--
  Represents an InteractionKind::State
  shard -> clk -> pc
  -/
  | state (shard clk pc : BabyBear)
  deriving DecidableEq

inductive SP1Constraint where
  /-- Assertion that a particular value is zero. -/
  | assertZero (x : BabyBear)
  /-- Sending an air interaction -/
  | send (interaction : AirInteraction) (mult : BabyBear)
  /-- Receiving an air interaction -/
  | receive (interaction : AirInteraction) (mult : BabyBear)
  | funcall (res : List SP1Constraint)
  /- deriving DecidableEq -/

namespace SP1Constraint

def toProp : SP1Constraint → Prop
  | .assertZero x => (x = 0)
  | .send (.byte op a b c) (mult) => mult = 1 → op.constrain a b c
  | .receive (.memory _ _ _ low_limb high_limb) (mult) =>
      mult = 1 → (low_limb < 65536 ∧ high_limb < 65536)
  | .funcall lst => List.Forall toProp lst
  | _ => 1 = 1

/- @[simp] lemma toProp_assertZero (x : BabyBear) : -/
/-     (assertZero x).toProp ↔ x = 0 := Iff.rfl -/
/--/
/- @[simp] lemma toProp_sendAirInteration_byte (op : ByteOpcode) -/
/-     (a b c mult : BabyBear) : -/
/-     (send (.byte op a b c) mult).toProp ↔ -/
/-       (mult = 1 → ByteOpcode.constrain op a b c) := Iff.rfl -/

end SP1Constraint

-- section constraintSet
-- 
-- -- TODO: should this exist? maybe even as `abbrev`?
-- @[reducible] def constraintSet := Finset SP1Constraint
-- 
-- /-- Covert a set of constraints to a single proposition stating that they all hold. -/
-- def constraintSet_toProp (cs : Finset SP1Constraint) : Prop :=
--   ∀ constraint ∈ cs, constraint.toProp
-- 
-- @[simp] lemma constraintSet_toProp_empty : constraintSet_toProp ∅ = True := by
--   simp [constraintSet_toProp]
-- 
-- @[simp] lemma constraintSet_toProp_singleton (c : SP1Constraint) : constraintSet_toProp {c} = c.toProp := by
--   simp [constraintSet_toProp]
-- 
-- @[simp] lemma constraintSet_toProp_insert (c : SP1Constraint) (cs : Finset SP1Constraint) :
--     constraintSet_toProp (insert c cs) = (c.toProp ∧ constraintSet_toProp cs) := by
--   simp [constraintSet_toProp]
-- 
-- lemma toProp_of_mem_constraintSet (cs : Finset SP1Constraint) (c : SP1Constraint) :
--     c ∈ cs → constraintSet_toProp cs → c.toProp := by
--   aesop
-- 
-- /-- A larger set of constraints `cs'` implies a smaller set of constraints `cs`. -/
-- lemma toProp_imp_of_constraintSet_subset' (cs cs' : Finset SP1Constraint)
--     (h : cs ⊆ cs') : constraintSet_toProp cs' → constraintSet_toProp cs := by
--   refine fun csp c h' => csp c (h h')
-- 
-- end constraintSet
