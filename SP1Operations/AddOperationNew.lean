import SP1Foundations
import LeanRV32D.RiscvInstsEnd
import LeanRV32D.RiscvRegs

-- Probably good to still namespace things
namespace AddOperation

/-- Representation of extracted constraints:
{
    Expr(0) = Input(6) - 1
    Expr(2) = Input(6) * Expr(0)
    Expr(4) = Input(0) + Input(2)
    Expr(6) = Expr(4) - Input(4)
    Expr(8) = Expr(6) + 0
    Expr(10) = Expr(8) * 2013235201
    Expr(12) = Expr(10) - 1
    Expr(14) = Expr(10) * Expr(12)
    Expr(16) = Input(6) * Expr(14)
    Expr(18) = Input(1) + Input(3)
    Expr(20) = Expr(18) - Input(5)
    Expr(22) = Expr(20) + Expr(10)
    Expr(24) = Expr(22) * 2013235201
    Expr(26) = Expr(24) - 1
    Expr(28) = Expr(24) * Expr(26)
    Expr(30) = Input(6) * Expr(28)
    Assert(Expr(2) == 0)
    Assert(Expr(16) == 0)
    Assert(Expr(30) == 0)
    Send(multiplicity: Input(6), scope: Local, values: [6, Input(4), 16, 0])
    Send(multiplicity: Input(6), scope: Local, values: [6, Input(5), 16, 0])
}
-/
def AddOperationConstraints
    (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear) : Finset SP1Constraint :=
  let Expr0 := Input6 - 1
  let Expr2 := Input6 * Expr0
  let Expr4 := Input0 + Input2
  let Expr6 := Expr4 - Input4
  let Expr8 := Expr6 + 0
  let Expr10 := Expr8 * 2013235201
  let Expr12 := Expr10 - 1
  let Expr14 := Expr10 * Expr12
  let Expr16 := Input6 * Expr14
  let Expr18 := Input1 + Input3
  let Expr20 := Expr18 - Input5
  let Expr22 := Expr20 + Expr10
  let Expr24 := Expr22 * 2013235201
  let Expr26 := Expr24 - 1
  let Expr28 := Expr24 * Expr26
  let Expr30 := Input6 * Expr28
  {
    .assertZero Expr2,
    .assertZero Expr16,
    .assertZero Expr30,
    .sendAirInteraction_byte (.ofNat 6) Input4 16 0 Input6,
    .sendAirInteraction_byte (.ofNat 6) Input5 16 0 Input6
  }

/- Nicer description of contraints in terms of a proposition. -/
def AddOperationConstraintProp
    (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear) : Prop :=
  let carry0 : BabyBear := 0
  let carry1 : BabyBear := (Input0 + Input2 - Input4 + carry0) * (baseInv : BabyBear)
  let carry2 : BabyBear := (Input1 + Input3 - Input5 + carry1) * (baseInv : BabyBear)
  Input6 = 0 ∨ (
    Input6 = 1 ∧
    (carry1 = 0 ∨ carry1 = 1) ∧
    (carry2 = 0 ∨ carry2 = 1) ∧
    (Input4.val < 65536) ∧
    (Input5.val < 65536)
  )

/-- Equivalence between the two versions of the constraints. -/
lemma AddOperationConstraints_iff
    (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear) :
    constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6) ↔
      AddOperationConstraintProp Input0 Input1 Input2 Input3 Input4 Input5 Input6 := by
  simp [AddOperationConstraints, AddOperationConstraintProp, ByteOpcode.constrain, sub_eq_zero]
  tauto

/-- Expected behavior of the add operation. Note that we assume first inputs are `U16` -/
def AddOperationSpec
    (Input0 Input1 Input2 Input3 : U16)
    (Input4 Input5 Input6 : BabyBear) : Prop :=
  (Input6 = 0 ∨ Input6 = 1) ∧
  (Input6 ≠ 0 → (
    (Input4.val < 65536) ∧ (Input5.val < 65536) ∧
    ((Input0.val + Input1.val * 65536) + (Input2.val + Input3.val * 65536)) % 4294967296 = (Input4.val + Input5.val * 65536)
  ))

theorem AddOperationSpec_of_AddOperationConstraintSet
    (Input0 Input1 Input2 Input3 : U16) (Input4 Input5 Input6 : BabyBear)
    (h : constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6)) :
    AddOperationSpec Input0 Input1 Input2 Input3 Input4 Input5 Input6 := by
  rw [AddOperationConstraints_iff, AddOperationConstraintProp] at h
  -- Handle the case that `is_real` is `0`
  cases h with | inl h => simp [AddOperationSpec, h] | inr h => ?_
  -- Handle the trivial proofs about bounding ranges
  simp [sub_eq_zero] at h
  obtain ⟨h6, hcarry1, hcarry2, ⟨h4, h5⟩⟩ := h
  refine ⟨Or.inr h6, fun h6' => ⟨h4, h5, ?_⟩⟩
  -- Split cases depending if the lower limb addition caused a carry
  cases hcarry1 with
  | inl hcarry1 =>
    -- Substitute the value of the carry
    rw [hcarry1] at hcarry2
    -- Simplify the definition of field arithmetic
    simp [Fin.mul_def, Fin.sub_def, Fin.add_def] at *
    -- Simplify the two new carry expressions
    simp [Fin.ext_iff] at hcarry1 hcarry2
    -- Aesop can solve now with help from omega
    aesop (add 50% tactic (by omega))
  | inr hcarry1 =>
    rw [hcarry1] at hcarry2
    simp [Fin.mul_def, Fin.sub_def, Fin.add_def, BabyBearPrime] at *
    simp [Fin.ext_iff] at hcarry1 hcarry2
    aesop (add 50% tactic (by omega))

section corollary

variable {Input0 Input1 Input2 Input3 : U16} {Input4 Input5 Input6 : BabyBear}

@[aesop unsafe forward]
protected lemma lt_of_constraintSet
    (h : constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6))
    (h' : Input6 ≠ 0) : Input4.val < 65536 := by
  have := (AddOperationSpec_of_AddOperationConstraintSet _ _ _ _ _ _ _ h).2 h'
  tauto

@[aesop unsafe forward]
protected lemma lt_of_constraintSet'
    (h : constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6))
    (h' : Input6 ≠ 0) : Input5.val < 65536 := by
  have := (AddOperationSpec_of_AddOperationConstraintSet _ _ _ _ _ _ _ h).2 h'
  tauto

open BitVec

/-- Version that doesn't auto-synthesize the proof (allowing reverse `rw` but being annoying forward).
Similar issue as `ENNReal.tsum_prod` vs `ENNReal.tsum_prod'`-/
lemma bitVecAdd_of_addOperationConstraintSet'
    (h : constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6))
    (h' : Input6 ≠ 0) (pf : Input4.val + Input5.val * 65536 < 2^32) :
    (BitVec.ofU16 Input0 Input1) + (BitVec.ofU16 Input2 Input3) =
        (Input4.val + Input5.val * 65536)#'pf := by
  have := (AddOperationSpec_of_AddOperationConstraintSet _ _ _ _ _ _ _ h).2 h'
  simp [BitVec.ofU16]
  rw [← BitVec.toNat_inj, BitVec.toNat_add]
  simp [BitVec.toNat_ofNatLT]
  exact this.2.2

lemma bitVecAdd_of_addOperationConstraintSet
    (h : constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6))
    (h' : Input6 ≠ 0) :
    have pf : Input4.val + Input5.val * 65536 < 2^32 := by
      have := AddOperation.lt_of_constraintSet h h'
      have := AddOperation.lt_of_constraintSet' h h'
      omega
    (BitVec.ofU16 Input0 Input1) + (BitVec.ofU16 Input2 Input3) =
      (Input4.val + Input5.val * 65536)#'pf := by
  exact bitVecAdd_of_addOperationConstraintSet' h h' _

end corollary

end AddOperation

namespace Add

-- Add below imports to the top of the file
/- import LeanRV32D.RiscvInstsEnd -/
/- import LeanRV32D.RiscvRegs -/

open LeanRV32D.Functions
open Sail
open PreSail (SequentialState)

open AddOperation

def AddChipConstraints
    (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear) : Finset SP1Constraint :=
  AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6

def sp1_add
  -- All the columns used for `AddChip` (currently includes only those from `add_operation`)
  (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear)
  (constraints :
    constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6))
  -- the following 4 proofs will come from the spec/constraints of `RTypeReader`
  -- adding in manually for now
  (read_b0_constraint : Input0.val < 65536) 
  (read_b1_constraint : Input1.val < 65536)
  (read_c0_constraint : Input2.val < 65536)
  (read_c1_constraint : Input3.val < 65536)
  -- ensures this is not a padding row (we're actually running the instruction)
  (h' : Input6 ≠ 0)
  -- registers to read/write
  (rd rs1 rs2 : regidx)
  : SailM Unit := 
  -- the human part of the code generation is to fill out the `pf`s
  let Input0 : U16 := ⟨Input0, read_b0_constraint⟩
  let Input1 : U16 := ⟨Input1, read_b1_constraint⟩
  let Input2 : U16 := ⟨Input2, read_c0_constraint⟩
  let Input3 : U16 := ⟨Input3, read_c1_constraint⟩
  let hh :=
    AddOperationSpec_of_AddOperationConstraintSet Input0 Input1 Input2 Input3 _ _ _ constraints
  let pf : Input4.val + Input5.val * 65536 < 2^32 := by
    have ⟨hb, ⟨hc, _⟩⟩ := (hh.right h')
    omega

  -- below will be auto-generated
  do
    writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
    let _ ← rX_bits rs1
    let _ ← rX_bits rs2
    -- at code-gen time, we don't know whether `Input4 + Input5 * 65536` will
    -- be in `u32` range, so we leave out the placeholder for us to manually
    -- fill in
    wX_bits rd (BitVec.ofNatLT (Input4.val + Input5.val * 65536) pf)

/- noncomputable -/ def spec_add (rd rs1 rs2 : regidx) : SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  /- let _ ← execute (.RTYPE ⟨rs2, rs1, rd, rop.ADD⟩) -/ -- `execute` is uncomputable...?
  let _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

theorem sp1_add_implies_spec_add
  (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear)
  (constraints :
    constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6))
  -- the following 4 proofs will come from the spec/constraints of `RTypeReader`
  -- adding in manually for now
  (read_b0_constraint : Input0.val < 65536) 
  (read_b1_constraint : Input1.val < 65536)
  (read_c0_constraint : Input2.val < 65536)
  (read_c1_constraint : Input3.val < 65536)
  -- ensures this is not a padding row (we're actually running the instruction)
  (h_is_real : Input6 ≠ 0)
  (rd rs1 rs2 : regidx)
  (read_b_fun : rX_bits rs1 = pure (BitVec.ofU16 ⟨Input0, read_b0_constraint⟩ ⟨Input1, read_b1_constraint⟩))
  (read_c_fun : rX_bits rs2 = pure (BitVec.ofU16 ⟨Input2, read_c0_constraint⟩ ⟨Input3, read_c1_constraint⟩))
  (s : PreSail.SequentialState RegisterType trivialChoiceSource)
  : let res := (sp1_add _ _ _ _ _ _ _ constraints read_b0_constraint read_b1_constraint read_c0_constraint read_c1_constraint h_is_real rd rs1 rs2).run s 
    let res_spec := (spec_add rd rs1 rs2).run s
  res = res_spec :=
  by
    let Input0 : U16 := ⟨Input0, read_b0_constraint⟩
    let Input1 : U16 := ⟨Input1, read_b1_constraint⟩
    let Input2 : U16 := ⟨Input2, read_c0_constraint⟩
    let Input3 : U16 := ⟨Input3, read_c1_constraint⟩
    simp [EStateM.run]
    simp [sp1_add, spec_add, /- execute, -/ execute_RTYPE]
    let h_bv :=
      bitVecAdd_of_addOperationConstraintSet
      (Input0 := Input0)
      (Input1 := Input1)
      (Input2 := Input2)
      (Input3 := Input3)
      constraints
      h_is_real
    rw [←h_bv]
    rw [read_b_fun, read_c_fun]
    clear h_bv read_b_fun read_c_fun
    rw [pure_bind, pure_bind]
    rfl

end Add
