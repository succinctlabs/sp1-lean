import SP1Foundations.Field
import SP1Foundations.ByteOpcode
import SP1Foundations.SailM
import SP1Foundations.SP1State

import LeanRV32IM.RiscvInstsEnd
import LeanRV32IM.Defs

open LeanRV32IM.Functions Sail

inductive AirInteraction where
  | byte (op : ByteOpcode) (a b c : Fin BB)
  | memory (shard clk addr low_limb high_limb : Fin BB)
  | state (shard clk pc : Fin BB)
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
  | .send (.memory _shard _clk addr low_limb high_limb) mult =>
      mult ≠ 0 → (low_limb < 65536 ∧ high_limb < 65536 ∧ addr < 32)
  | .receive (.memory _shard _clk addr low_limb high_limb) (mult) =>
      mult ≠ 0 → (low_limb < 65536 ∧ high_limb < 65536 ∧ addr < 32)
  | _ => True

@[simp] lemma toProp_assertZero (x : Fin BB) :
    (assertZero x).toProp ↔ x = 0 := Iff.rfl

@[simp] lemma toProp_send_byte (op : ByteOpcode) (a b c mult : Fin BB) :
    (send (AirInteraction.byte op a b c) mult).toProp ↔
      (mult ≠ 0 → op.constrain a b c) := Iff.rfl

end toProp

section toStateProp

def toStateProp (cstr : SP1Constraint) (s : SP1State) : Prop := 
  match cstr with
  | (.send (.memory _shard _clk addr low_limb high_limb) mult) =>
      mult ≠ 0
      → s.snd (.Regidx addr.val) = BitVec.ofNat 32 (low_limb + high_limb * 65536)
  | _ => True

end toStateProp

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

@[simp] protected def SP1ConstraintList.initialState (xs : SP1ConstraintList) (s : SP1State) : Prop :=
  List.Forall (SP1Constraint.toStateProp · s) xs

section initialState

variable {s : SP1State}

lemma initialState_nil : SP1ConstraintList.initialState [] s := True.intro

lemma initialState_singleton (c : SP1Constraint) :
    SP1ConstraintList.initialState [c] s ↔ c.toStateProp s := Iff.rfl

lemma initialState_cons (c : SP1Constraint) (cs : SP1ConstraintList) :
    SP1ConstraintList.initialState (c :: cs) s ↔ c.toStateProp s ∧ SP1ConstraintList.initialState cs s :=
  List.forall_cons _ _ _

lemma initialState_append (cs cs' : SP1ConstraintList) :
    SP1ConstraintList.initialState (cs ++ cs') s ↔ cs.initialState s ∧ cs'.initialState s :=
  List.forall_append

end initialState
  
end constraintList
