import SP1Foundations

/-- Representation of these extracted constraints:
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

/- Nicer description of the above constraints. -/
def AddOperationConstraints'
    (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear) : Prop :=
  let carry0 : BabyBear := 0
  let carry1 : BabyBear := (Input0 + Input2 - Input4 + carry0) * (baseInv : BabyBear)
  let carry2 : BabyBear := (Input1 + Input3 - Input5 + carry1) * (baseInv : BabyBear)
  (Input6 * (Input6 - 1)) = 0 ∧
  (Input6 * carry1 * (carry1 - 1)) = 0 ∧
  (Input6 * carry2 * (carry2 - 1)) = 0 ∧
  (Input6 ≠ 0 → Input4 < 65536) ∧
  (Input6 ≠ 0 → Input5 < 65536)

/-- Equivalence between the two versions of constraints. -/
lemma AddOperationConstraints_iff
    (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear) :
    constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6) ↔
      AddOperationConstraints' Input0 Input1 Input2 Input3 Input4 Input5 Input6 := by
  simp [AddOperationConstraints, AddOperationConstraints', sub_eq_zero, ByteOpcode.constrain]
  intro h
  cases h with
  | inl h => simp [h]
  | inr h => simp [h]

def BabyBear.U32_of_U16_of_U16 (x y : U16) : ℕ := x.val + y.val * 65536

/-- Expected behavior of the add operation. -/
def AddOperationSpec
    (Input0 Input1 Input2 Input3 : U16)
    (Input4 Input5 Input6 : BabyBear) : Prop :=
  Input6 ≠ 0 → (Input0.val + Input1.val * 65536 + Input2.val + Input3.val * 65536) % 4294967296 = (Input4.val + Input5.val * 65536)

theorem AddOperationCorrect
    (Input0 Input1 Input2 Input3 : U16)
    (Input4 Input5 Input6 : BabyBear) :
    constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6) →
      AddOperationSpec Input0 Input1 Input2 Input3 Input4 Input5 Input6 := by
  rw [AddOperationConstraints_iff, AddOperationConstraints']
  intro h h_is_real
  simp [h_is_real, sub_eq_zero] at h
  obtain ⟨h6, hcarry1, hcarry2, ⟨h4, h5⟩⟩ := h
  have _ : Input0.val < 65536 := Input0.in_range
  have _ : Input1.val < 65536 := Input1.in_range
  have _ : Input2.val < 65536 := Input2.in_range
  have _ : Input3.val < 65536 := Input3.in_range
  cases hcarry1 with
  | inl hcarry1 =>
    rw [hcarry1] at hcarry2
    simp at *
    simp [Fin.mul_def, Fin.sub_def, Fin.add_def, BabyBearPrime] at *
    simp [Fin.ext_iff] at hcarry1 hcarry2
    rw [Fin.lt_iff_val_lt_val, BabyBear.val_65536] at h4 h5
    omega
  | inr hcarry1 =>
    rw [hcarry1] at hcarry2
    simp at *
    simp [Fin.mul_def, Fin.sub_def, Fin.add_def, BabyBearPrime] at *
    simp [Fin.ext_iff] at hcarry1 hcarry2
    rw [Fin.lt_iff_val_lt_val, BabyBear.val_65536] at h4 h5
    omega
