import SP1Foundations.Field
import SP1Foundations.ByteOpcode

import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

-- inductive AirInteraction.Kind where
--   | BYTE
--   | MEMORY
--   | PROGRAM
--   | STATE

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

section toSailM

/-- Naive version of conversion to `SailM` monad without clock sorting. -/
def SP1ConstraintList.toSailM : SP1ConstraintList → SailM Unit
  | (.receive (.memory _ _ addr low_limb high_limb) _) :: cs => do
      wX_bits (.Regidx <| BitVec.ofNat 5 addr.val)
        (BitVec.ofNat 32 (low_limb + high_limb * 65536));
      SP1ConstraintList.toSailM cs
  | _ :: cs => SP1ConstraintList.toSailM cs
  | _ => pure ()

example (x y : SailM Unit) : x = y := by
  refine EStateM.ext ?_
  sorry

-- def SP1ConstraintList.toRegInit : SP1ConstraintList → SailM Unit
--   | (.send (.memory _ _ addr low_limb high_limb) _) :: cs => do
--       rX_bits (.Regidx <| BitVec.ofNat 5 addr.val)
--         (BitVec.ofNat 32 (low_limb + high_limb * 65536));
--       SP1ConstraintList.toSailM cs
--   | _ :: cs => SP1ConstraintList.toSailM cs
--   | _ => pure ()

end toSailM

section toReg

-- def SP1Constraint.getClk : SP1Constraint → Option BabyBear
--   | .send (.memory shard clk addr low_limb high_limb) mult => some clk
--   | .receive (.memory shard clk addr low_limb high_limb) mult => some clk
--   | _ => none

-- noncomputable def SP1ConstraintList.sortClock (cs : SP1ConstraintList) : SP1ConstraintList :=
--   cs.mergeSort (fun c1 c2 => open Classical in if c1.getClk ≤ c2.getClk then true else false)

-- def toSailM' : SP1Constraint → SailM Unit
--   | .send (.memory shard clk addr low_limb high_limb) mult => do
--       wX_bits (.Regidx <| BitVec.ofNat 5 addr.val)
--         (BitVec.ofNat 32 (low_limb + high_limb * 65536))
--   | _ => pure ()

-- noncomputable def constraints_to_SailM (cs : SP1ConstraintList) : SailM Unit :=
--   do let _ ← List.mapM toSailM cs.sortClock

section sailboats

#check EStateM.Result

lemma reg_map_ext (rmap rmap' : PreSail.SequentialState RegisterType trivialChoiceSource)
    (hreg : rmap.regs = rmap'.regs)
    (hcs : rmap.choiceState = rmap'.choiceState)
    (hmem : rmap.mem = rmap'.mem)
    (hcc : rmap.cycleCount = rmap'.cycleCount)
    (hout : rmap.sailOutput = rmap'.sailOutput) :
    rmap = rmap' := by
  refine match rmap with | ⟨regs, cs, mem, (), cc, so⟩ => ?_
  refine match rmap' with | ⟨regs', cs', mem', (), cc', so'⟩ => ?_
  simp_all

lemma wX_bits_rX_bits' (rs : regidx) (v : BitVec 32) (cont : BitVec 32 → SailM α) :
    (do let _ ← wX_bits rs v; let v' ← rX_bits rs; cont v') =
      (do let _ ← wX_bits rs v; cont v) := by
  refine EStateM.ext fun reg_map => ?_
  simp
  rw [EStateM.run]
  sorry

lemma wX_bits_rX_bits (rs : regidx) (v : BitVec 32) :
    (do let _ ← wX_bits rs v; rX_bits rs) =
      (do let _ ← wX_bits rs v; pure v) := by
  refine EStateM.ext fun reg_map => ?_
  simp
  rw [EStateM.run]
  sorry

lemma rX_bits_rX_bits_swap (cont : BitVec 32 → BitVec 32 → SailM α)
    {rs rs' : regidx} (h : rs ≠ rs') :
    (do let bv ← rX_bits rs; let bv' ← rX_bits rs'; cont bv bv') =
      (do let bv' ← rX_bits rs'; let bv ← rX_bits rs; cont bv bv') := by
  sorry

lemma wX_bits_rX_bits_swap (cont : Unit → BitVec 32 → SailM α)
    {rs rs' : regidx} (h : rs ≠ rs') (bv : BitVec 32) :
    (do let u ← wX_bits rs bv; let bv' ← rX_bits rs'; cont u bv') =
      (do let bv' ← rX_bits rs'; let _ ← wX_bits rs bv; cont () bv') := by
  sorry

lemma rX_bits_wX_bits_swap (cont : BitVec 32 → Unit → SailM α)
    {rs rs' : regidx} (h : rs ≠ rs') (bv : BitVec 32) :
    (do let bv ← rX_bits rs; let u ← wX_bits rs' bv; cont bv u) =
      (do let _ ← wX_bits rs' bv; let bv ← rX_bits rs; cont bv ()) := by
  sorry

lemma wX_bits_wX_bits_swap (cont : Unit → Unit → SailM α)
    {rs rs' : regidx} (h : rs ≠ rs') (bv bv' : BitVec 32) :
    (do let u ← wX_bits rs bv; let u' ← wX_bits rs' bv'; cont u u') =
      (do let _ ← wX_bits rs' bv'; let _ ← wX_bits rs bv; cont () ()) := by
  sorry

end sailboats
