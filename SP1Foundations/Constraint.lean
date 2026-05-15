import SP1Foundations.ByteOpcode
import SP1Foundations.Assumptions

import LeanRV64D

/-- Field-generic AIR interaction. The inductive only stores field elements; the
specific typeclass requirements live on `SP1Constraint.toProp_poly` /
`SP1Constraint.toStateProp_poly`. -/
inductive AirInteraction (F : Type*) where
  | byte (op : ByteOpcode) (a b c : F)
  | memory (clk_high clk_low addr0 addr1 addr2 limb0 limb1 limb2 limb3 : F)
  | state (clk_high clk_low pc0 pc1 pc2 : F)
  | program
      (pc0 pc1 pc2 : F)
      (opcode : Opcode)
      (op_a
      op_b_0 op_b_1 op_b_2 op_b_3
      op_c_0 op_c_1 op_c_2 op_c_3
      op_a_0
      imm_b
      imm_c : F)
  deriving DecidableEq

/-- Field-generic SP1 constraint. See `AirInteraction` for the field-genericity
note. -/
inductive SP1Constraint (F : Type*) where
  /-- Assertion that a particular value is zero. -/
  | assertZero (x : F)
  /-- Sending an air interaction -/
  | send (interaction : AirInteraction F) (mult : F)
  /-- Receiving an air interaction -/
  | receive (interaction : AirInteraction F) (mult : F)
  -- | ofList (cs : List SP1Constraint) : SP1Constraint
  deriving DecidableEq

namespace SP1Constraint

section toProp_poly

/-- Constraint-level prop over a generic prime field `ZMod p`. -/
def toProp_poly {p : ℕ} [NeZero p] : SP1Constraint (ZMod p) → Prop
  | .assertZero x => (x = 0)
  | .send (.byte op a b c) mult => mult ≠ 0 → op.constrain_poly a b c
  | (.send (.memory _clk_high _clk_low _addr0 _addr1 _addr2 limb0 limb1 limb2 limb3) mult) =>
      mult ≠ 0 → Word.isU64_poly #v[limb0, limb1, limb2, limb3]
  | .send
      (.program
      pc0 pc1 pc2
      opcode
      op_a
      op_b_0 op_b_1 op_b_2 op_b_3
      op_c_0 op_c_1 op_c_2 op_c_3
      op_a_0
      imm_b
      imm_c)
      mult =>
        mult ≠ 0
        -> opcode.trusted_instr_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
           ∧ op_a < 32
           ∧ (op_b_0 < 65536 ∧ op_b_1 < 65536 ∧ op_b_2 < 65536 ∧ op_b_3 < 65536)
           ∧ (op_c_0 < 65536 ∧ op_c_1 < 65536 ∧ op_c_2 < 65536 ∧ op_c_3 < 65536)
           ∧ (op_a_0 = 0 ∨ op_a_0 = 1)
           ∧ (op_a_0 = 1 ↔ op_a = 0)
           ∧ (imm_b = 0 ∨ imm_b = 1)
           ∧ (imm_c = 0 ∨ imm_c = 1)
           ∧ (pc0 % 4 = 0 ∧ (pc0 < 65536 ∧ pc1 < 65536 ∧ pc2 < 65536))
  | _ => True

@[simp] lemma toProp_poly_assertZero {p : ℕ} [NeZero p] (x : ZMod p) :
    (assertZero (F := ZMod p) x).toProp_poly ↔ x = 0 := Iff.rfl

@[simp] lemma toProp_poly_send_byte {p : ℕ} [NeZero p]
    (op : ByteOpcode) (a b c mult : ZMod p) :
    (send (F := ZMod p) (.byte op a b c) mult).toProp_poly ↔
      (mult ≠ 0 → op.constrain_poly a b c) := Iff.rfl

end toProp_poly

section toStateProp_poly

open PreSail

/-- State-prop projection over `SP1Constraint (ZMod p)`. The address bound
is phrased as `addr0.val < 32` (Nat-level) so the proof witness for
`BitVec.ofNatLT` is directly available regardless of `p`'s specific value. -/
def toStateProp_poly {p : ℕ} [NeZero p]
    (cstr : SP1Constraint (ZMod p)) (s : SailState) : Prop :=
  match cstr with
  | .send (.memory _ _ addr0 addr1 addr2 limb0 limb1 limb2 limb3) mult => mult ≠ 0 →
      if h_addrs : addr0.val < 32 ∧ addr1 = 0 ∧ addr2 = 0 then
        s.get_reg? (BitVec.ofNatLT addr0.val h_addrs.left) =
          some (Word.toBitVec64_poly #v[limb0, limb1, limb2, limb3])
      else
        s.mem[Word.toNat_poly #v[addr0, addr1, addr2, 0]]? = some (BitVec.ofNat 8 limb0.val) ∧
        s.mem[Word.toNat_poly #v[addr0 + 1, addr1, addr2, 0]]? = some (BitVec.ofNat 8 (limb0.val >>> 8)) ∧
        s.mem[Word.toNat_poly #v[addr0 + 2, addr1, addr2, 0]]? = some (BitVec.ofNat 8 limb1.val) ∧
        s.mem[Word.toNat_poly #v[addr0 + 3, addr1, addr2, 0]]? = some (BitVec.ofNat 8 (limb1.val >>> 8)) ∧
        s.mem[Word.toNat_poly #v[addr0 + 4, addr1, addr2, 0]]? = some (BitVec.ofNat 8 limb2.val) ∧
        s.mem[Word.toNat_poly #v[addr0 + 5, addr1, addr2, 0]]? = some (BitVec.ofNat 8 (limb2.val >>> 8)) ∧
        s.mem[Word.toNat_poly #v[addr0 + 6, addr1, addr2, 0]]? = some (BitVec.ofNat 8 limb3.val) ∧
        s.mem[Word.toNat_poly #v[addr0 + 7, addr1, addr2, 0]]? = some (BitVec.ofNat 8 (limb3.val >>> 8))
  | .receive (.state _ _ pc0 pc1 pc2) mult => mult ≠ 0 →
      s.regs.get? Register.PC = some (Word.toBitVec64_poly #v[pc0, pc1, pc2, 0])
  | _ => True

end toStateProp_poly

end SP1Constraint

section constraintList

/-- Wrapper for lists of constraints. Mainly used to namespace lemmas. -/
@[reducible] def SP1ConstraintList (F : Type*) := List (SP1Constraint F)

@[reducible] protected def SP1ConstraintList.allHold_poly {p : ℕ} [NeZero p]
    (xs : SP1ConstraintList (ZMod p)) : Prop :=
  List.Forall SP1Constraint.toProp_poly xs

@[simp] protected def SP1ConstraintList.initialState_poly {p : ℕ} [NeZero p]
    (xs : SP1ConstraintList (ZMod p)) (s : SailState) : Prop :=
  List.Forall (SP1Constraint.toStateProp_poly · s) xs

end constraintList
