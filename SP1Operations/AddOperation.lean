import SP1Foundations

structure AddOperation where
  value : Word BabyBear

namespace AddOperation

def constraints
  (a : Word BabyBear)
  (b : Word BabyBear)
  (cols : AddOperation)
  (is_real : BabyBear)
  : SP1ConstraintList :=
  let E0 : BabyBear := is_real - 1
  let E1 : BabyBear := is_real * E0
  let E2 : BabyBear := a[0] + b[0]
  let E3 : BabyBear := E2 - cols.value[0]
  let E4 : BabyBear := E3 + 0
  let E5 : BabyBear := E4 * 2013235201
  let E6 : BabyBear := E5 - 1
  let E7 : BabyBear := E5 * E6
  let E8 : BabyBear := is_real * E7
  let E9 : BabyBear := a[1] + b[1]
  let E10 : BabyBear := E9 - cols.value[1]
  let E11 : BabyBear := E10 + E5
  let E12 : BabyBear := E11 * 2013235201
  let E13 : BabyBear := E12 - 1
  let E14 : BabyBear := E12 * E13
  let E15 : BabyBear := is_real * E14
  [
    .assertZero E1,
    .assertZero E8,
    .assertZero E15,
    .send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real,
    .send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real
  ]

def constraintsProp
  (a : Word BabyBear)
  (b : Word BabyBear)
  (cols : AddOperation)
  (is_real : BabyBear)
  : Prop :=
  let carry0  : BabyBear := 0
  let carry1  : BabyBear := (a[0] + b[0] - cols.value[0] + carry0) * (baseInv : BabyBear)
  let carry2  : BabyBear := (a[1] + b[1] - cols.value[1] + carry1) * (baseInv : BabyBear)
  is_real = 0 ∨ (
    is_real = 1 ∧
    (carry1 = 0 ∨ carry1 = 1) ∧
    (carry2 = 0 ∨ carry2 = 1) ∧
    (cols.value[0] < 65536) ∧
    (cols.value[1] < 65536)
  )

def constraints_iff_constraintsProp
  (a : Word BabyBear)
  (b : Word BabyBear)
  (cols : AddOperation)
  (is_real : BabyBear)
  : (constraints a b cols is_real).allHold ↔ constraintsProp a b cols is_real := by
  by_cases h : is_real = 0
  · simp [constraints, constraintsProp, h]
  · by_cases h' : is_real = 1 <;> simp [constraints, constraintsProp, h, h', sub_eq_zero]

-- Note that `a`, `b` are in U16 because that's part of our assumption.
-- `AddOperation` should only be used when `a`, `b` are U16s, which is
-- concretized here.
--
-- `cols` is still in BabyBear because that's what we're trying to prove.
def spec
  (a b : Word U16)
  (cols : AddOperation)
  (is_real : U1) : Prop :=
    is_real = 1 → cols.value.toBV32 = a.toBV32_U16 + b.toBV32_U16

theorem correct
  (a b : Word U16)
  (cols : AddOperation)
  (is_real : U1) :
    (constraints a b cols is_real).allHold →
    spec a b cols is_real := by
      rw [constraints_iff_constraintsProp a b cols is_real]
      simp [constraintsProp, spec]
      intro q1

      intro h_is_real
      simp [h_is_real] at q1

      let ⟨qq1, ⟨qq2, ⟨qq3, aa4⟩⟩⟩ := q1
      clear q1
      simp [sub_eq_zero, mul_eq_zero] at qq1 qq2
      simp [Word.toBV32_U16, Word.toBV32, BitVec.ofNatLT, BitVec.ofNat]

      cases qq1 with
      | inl qqq1 =>
          rw [qqq1] at qq2
          simp [Fin.mul_def, Fin.sub_def, Fin.add_def, Fin.ext_iff, BabyBearPrime] at *
          simp [Fin.lt_def] at qq3 aa4
          aesop (add 50% tactic (by omega))
      | inr qqq1 =>
          rw [qqq1] at qq2
          simp [Fin.mul_def, Fin.sub_def, Fin.add_def, Fin.ext_iff, BabyBearPrime] at *
          simp [Fin.lt_def] at qq3 aa4
          aesop (add 50% tactic (by omega))

open BitVec

lemma lt_of_constraintsAllHold
    (h : (constraints a b cols is_real).allHold)
    (h_is_real : is_real = 1) : cols.value[0] < 65536 := by
  rw [constraints_iff_constraintsProp] at h
  rw [constraintsProp] at h
  simp at h
  subst h_is_real
  tauto

lemma lt_of_constraintsAllHold'
    (h : (constraints a b cols is_real).allHold)
    (h_is_real : is_real = 1) : cols.value[1] < 65536 := by
  rw [constraints_iff_constraintsProp] at h
  rw [constraintsProp] at h
  simp at h
  subst h_is_real
  tauto

/-- Version of correctness using specific bitvecs.
To get good rewrites we allow arbitrary proofs on the left (should do the reverse for ← rw to work)-/
lemma correct'
    (a b : Word U16)
    (cols : AddOperation)
    (is_real : U1)
    (h : (constraints a b cols is_real).allHold)
    (h_is_real : is_real = 1)
    (pf : cols.value[0].val + cols.value[1].val * 65536 < 2 ^ 32) :
    (cols.value[0].val + cols.value[1].val * 65536)#'pf =
      (a.toBV32_U16 + b.toBV32_U16) := by
  -- TODO(gzgz): don't use aesop
  let c0' : U16 := ⟨cols.value[0], lt_of_constraintsAllHold h (by aesop)⟩
  let c1' : U16 := ⟨cols.value[1], lt_of_constraintsAllHold' h (by aesop)⟩
  rw [BitVec.ofNatLT_eq_ofNat pf]
  refine correct a b { value := #v[c0', c1'] } is_real h h_is_real

end AddOperation
