import SP1Foundations

<<<<<<< HEAD
namespace AddOperation

/- @[simp] lemma value_mk (value : Word U16) : (AddOperation.mk value).value = value := rfl -/

def spec
  (a0 a1 : U16)
  (b0 b1 : U16)
  (c0 c1 : U16)
  (is_real : U1) : Prop :=
    is_real = 1 → BitVec.ofU16 a0 a1 = BitVec.ofU16 b0 b1 + BitVec.ofU16 c0 c1

def constraints
  (I : Vector BabyBear 7)
  : List SP1Constraint :=
  let E0 := I[6] - 1
  let E2 := I[6] * E0
  let E4 := I[0] + I[2]
  let E6 := E4 - I[4]
  let E8 := E6 + 0
  let E10 := E8 * 2013235201
  let E12 := E10 - 1
  let E14 := E10 * E12
  let E16 := I[6] * E14
  let E18 := I[1] + I[3]
  let E20 := E18 - I[5]
  let E22 := E20 + E10
  let E24 := E22 * 2013235201
  let E26 := E24 - 1
  let E28 := E24 * E26
  let E30 := I[6] * E28
  [ .assertZero E2
  , .assertZero E16
  , .assertZero E30
  , .send (.byte (ByteOpcode.ofNat 6) I[4] 16 0) I[6]
  , .send (.byte (ByteOpcode.ofNat 6) I[5] 16 0) I[6]
  ]

def constraints'
  (I : Vector BabyBear 7)
  : Prop :=
  let carry0  : BabyBear := 0
  let carry1  : BabyBear := (I[0] + I[2] - I[4] + carry0) * (baseInv : BabyBear)
  let carry2  : BabyBear := (I[1] + I[3] - I[5] + carry1) * (baseInv : BabyBear)
  I[6] = 0 ∨ (
    I[6] = 1 ∧
    (carry1 = 0 ∨ carry1 = 1) ∧
    (carry2 = 0 ∨ carry2 = 1) ∧
    (I[4] < 65536) ∧
    (I[5] < 65536)
  )

def constraints_iff_constraints'
  (I : Vector BabyBear 7)
  : List.Forall SP1Constraint.toProp (constraints I) ↔ constraints' I := by
  simp [constraints, constraints']
  simp [ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain]
  simp [sub_eq_zero]
  sorry

theorem correct
  (a0 a1 : U16)
  (b0 b1 : U16)
  (c0 c1 : U16)
  (is_real : U1) :
    List.Forall SP1Constraint.toProp (constraints #v[b0, b1, c0, c1, a0, a1, is_real]) →
    spec a0 a1 b0 b1 c0 c1 is_real := by
  rw [constraints_iff_constraints' (#v[b0, b1, c0, c1, a0, a1, is_real])]
  simp [constraints', spec]
  intro q1

  intro h_is_real
  simp [h_is_real] at q1

  let ⟨qq1, ⟨qq2, ⟨qq3, aa4⟩⟩⟩ := q1
  clear q1
  simp [sub_eq_zero, mul_eq_zero] at qq1 qq2
  simp [BitVec.ofU16, BitVec.ofNatLT]

  let i0 := c0.in_range
  let i1 := c1.in_range
  let i2 := b0.in_range
  let i3 := b1.in_range

  cases qq1 with
  | inl qqq1 =>
      rw [qqq1] at qq2
      simp [Fin.mul_def, Fin.sub_def, Fin.add_def, Fin.ext_iff, BabyBearPrime] at *
      rw [Fin.lt_def] at qq3 aa4
      aesop (add 50% tactic (by omega))
  | inr qqq1 =>
      rw [qqq1] at qq2
      simp [Fin.mul_def, Fin.sub_def, Fin.add_def, Fin.ext_iff, BabyBearPrime] at *
      rw [Fin.lt_def] at qq3 aa4
      aesop (add 50% tactic (by omega))
=======
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
>>>>>>> 997c41403074de8dd357722fd646b205687876b6

end AddOperation
