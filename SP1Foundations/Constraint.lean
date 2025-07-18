import SP1Foundations.Field
import SP1Foundations.Word
import SP1Foundations.ByteOpcode
import SP1Foundations.SailM
import SP1Foundations.Opcode

import LeanRV64IM.Defs

inductive AirInteraction where
  | byte (op : ByteOpcode) (a b c : Fin BB)
  | memory (clk_high clk_low addr0 addr1 addr2 limb0 limb1 limb2 limb3: Fin BB)
  | state (clk_high clk_low pc0 pc1 pc2: Fin BB)
  | program
      (pc0 pc1 pc2 : Fin BB)
      (opcode : Opcode)
      (op_a
      op_b_0 op_b_1 op_b_2 op_b_3 
      op_c_0 op_c_1 op_c_2 op_c_3
      op_a_0
      imm_b
      imm_c 
      instr_const0 instr_const1 instr_const2 : Fin BB)
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
  | (.send (.memory _clk_high _clk_low _addr0 _addr1 _addr2 limb0 limb1 limb2 limb3) mult) =>
      mult ≠ 0 → Word.isU64 #v[limb0, limb1, limb2, limb3]
  | .send
      (.program
      pc0 pc1 pc2
      opcode
      op_a
      op_b_0 op_b_1 op_b_2 op_b_3 
      op_c_0 op_c_1 op_c_2 op_c_3
      op_a_0
      imm_b
      imm_c 
      _instr_const0 _instr_const1 _instr_const2)
      mult =>
        mult ≠ 0
        -> opcode.trusted_instr op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3
           ∧ op_a < 32 
           ∧ (op_b_0 < 65536 ∧ op_b_1 < 65536 ∧ op_b_2 < 65536 ∧ op_b_3 < 65536)
           ∧ (op_c_0 < 65536 ∧ op_c_1 < 65536 ∧ op_c_2 < 65536 ∧ op_c_3 < 65536)
           ∧ (op_a_0 = 0 ∨ op_a_0 = 1)
           ∧ (imm_b = 0 ∨ imm_b = 1)
           ∧ (imm_c = 0 ∨ imm_c = 1)
           ∧ (pc0 % 4 = 0 ∧ (pc0 < 65536 ∧ pc1 < 65536 ∧ pc2 < 65536))
  | _ => True

@[simp] lemma toProp_assertZero (x : Fin BB) :
    (assertZero x).toProp ↔ x = 0 := Iff.rfl

@[simp] lemma toProp_send_byte (op : ByteOpcode) (a b c : Fin BB) (mult : Fin BB) :
    (send (.byte op a b c) mult).toProp ↔ (mult ≠ 0 → op.constrain a b c) := Iff.rfl

-- dt: change this back once airs work
@[simp] lemma toProp_recv (air : AirInteraction) (mult : Fin BB) :
    (receive air mult).toProp ↔ True := Iff.rfl

end toProp

section toStateProp

open PreSail

def toStateProp (cstr : SP1Constraint) (s : SailState) : Prop := 
  match cstr with
  | (.send (.memory _clk_high _clk_low addr0 addr1 addr2 limb0 limb1 limb2 limb3) mult) =>
      mult ≠ 0
      → if h_addrs : addr0 < 32 ∧ addr1 = 0 ∧ addr2 = 0 then
          s.get_reg? (BitVec.ofNatLT addr0.val h_addrs.left)
            = some (Word.toBitVec64 #v[limb0, limb1, limb2, limb3])
        else
          True -- TODO(gzgz): this is reading from memory
  | (.receive (.state _clk_high _clk_low pc0 pc1 pc2) mult) =>
      mult ≠ 0
      → s.regs.get? Register.PC
        = some (BitVec.ofNat 64 (pc0.val + pc1.val * 65536 + pc2.val * 4294967296))
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

@[simp] protected def SP1ConstraintList.initialState (xs : SP1ConstraintList) (s : SailState) : Prop :=
  List.Forall (SP1Constraint.toStateProp · s) xs

section initialState

variable {s : SailState}

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

