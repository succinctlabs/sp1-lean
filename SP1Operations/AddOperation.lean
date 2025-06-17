import SP1Foundations

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

end AddOperation
