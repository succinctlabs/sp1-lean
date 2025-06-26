import SP1Foundations.Field
import SP1Foundations.ByteOpcode
import SP1Foundations.SailM

import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

inductive AirInteraction where
  | byte (op : ByteOpcode) (a b c : BabyBear)
  | memory (shard clk addr low_limb high_limb : BabyBear)
  | state (shard clk pc : BabyBear)
  deriving DecidableEq

inductive SP1Constraint where
  /-- Assertion that a particular value is zero. -/
  | assertZero (x : BabyBear)
  /-- Sending an air interaction -/
  | send (interaction : AirInteraction) (mult : BabyBear)
  /-- Receiving an air interaction -/
  | receive (interaction : AirInteraction) (mult : BabyBear)
  -- | ofList (cs : List SP1Constraint) : SP1Constraint
  deriving DecidableEq

namespace SP1Constraint

section toProp

def toProp : SP1Constraint → Prop
  | .assertZero x => (x = 0)
  | .send (.byte op a b c) mult => mult ≠ 0 → op.constrain a b c
  | .send (.memory shard clk addr low_limb high_limb) mult =>
      mult ≠ 0 → ((rX_bits (.Regidx <| BitVec.ofNat 5 addr.val) = pure (BitVec.ofNat 32 (low_limb + high_limb * 65536)))
        ∧ (low_limb < 65536 ∧ high_limb < 65536 ∧ addr < 32))
  | .receive (.memory shard clk addr low_limb high_limb) (mult) =>
      mult ≠ 0 → (low_limb < 65536 ∧ high_limb < 65536 ∧ addr < 32)
  | _ => True

@[simp] lemma toProp_assertZero (x : BabyBear) :
    (assertZero x).toProp ↔ x = 0 := Iff.rfl

@[simp] lemma toProp_send_byte (op : ByteOpcode) (a b c mult : BabyBear) :
    (send (AirInteraction.byte op a b c) mult).toProp ↔
      (mult ≠ 0 → op.constrain a b c) := Iff.rfl

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

/-- State for arithmetic chip verification is a program counter and register assignment map. -/
abbrev SP1State := BitVec 32 × (regidx → BitVec 32)

/-- Add `4` to the current program counter state. -/
@[reducible] def incrementPC : StateM SP1State Unit :=
  do modify (.map (· + (BitVec.ofNat _ 4)) id)

/-- Modify the register map state -/
@[reducible] def update_reg (idx : regidx) (v : BitVec 32) : StateM SP1State Unit :=
  do modify (.map id (Function.update · idx v))
