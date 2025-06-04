import SP1Foundations

-- AddOperaton is not parameterized by a type `T` with `value` being `Word T`
-- because AddOperation is used only under the assumption that its input and
-- output limbs are all U16s.
@[aesop safe cases]
structure AddOperation where
  value : Word U16

namespace AddOperation

def spec
  (cols : AddOperation)
  (a : Word U16)
  (b : Word U16)
  (is_real : U2) : Prop :=
    is_real = U2.one →
    a.toFin32_U16 + b.toFin32_U16 = cols.value.toFin32_U16

def constraints (cols : AddOperation)
    (a b : Word U16) (is_real : U2) : List SP1Constraint :=
  [
    .assertZero (is_real * ((((a[0].val + b[0].val) - cols.value[0].val) + (0 : BabyBear)) * (2013235201 : BabyBear)) * (((((a[0].val + b[0].val) - cols.value[0].val) + 0) * 2013235201) - 1)),
    .assertZero (is_real * ((((a[1].val + b[1].val) - cols.value[1].val) + ((((a[0].val + b[0].val) - cols.value[0].val) + (0 : BabyBear)) * (2013235201 : BabyBear))) * (2013235201 : BabyBear)) * (((((a[1].val + b[1].val) - cols.value[1].val) + ((((a[0].val + b[0].val) - cols.value[0].val) + 0) * 2013235201)) * 2013235201) - 1))
  ]

def constraints'
    (cols : AddOperation)
    (a : Word U16)
    (b : Word U16)
    (is_real : U2): Prop :=
  let carry0 : BabyBear := 0
  let carry1 : BabyBear := (a[0] + b[0] - cols.value[0] + carry0) * (baseInv : BabyBear)
  let carry2 : BabyBear := (a[1] + b[1] - cols.value[1] + carry1) * (baseInv : BabyBear)
  (is_real.val * carry1 * (carry1 - 1)) = 0 ∧
  (is_real.val * carry2 * (carry2 - 1)) = 0

def constraints_iff_constraints'
    (cols : AddOperation)
    (a : Word U16)
    (b : Word U16)
    (is_real : U2) :
    constraintList_toProp (cols.constraints a b is_real) ↔ cols.constraints' a b is_real:= by
  simp [constraints, constraints']

theorem correct
  (cols : AddOperation)
  (a : Word U16)
  (b : Word U16)
  (is_real : U2)
  : cols.constraints' a b is_real → cols.spec a b is_real :=
    by
      intro ⟨q1, q2⟩

      -- Since is_real = 1, substitute and apply 1 * x = x to get original constraints
      intro h_is_real
      simp [is_real.eq_one_iff.1 h_is_real, sub_eq_zero, mul_eq_zero] at q1 q2
      simp [Word.toFin32_U16]

      -- Cases on whether the lower limb led to a carry or not
      cases q1 with | inl qq1 => ?_ | inr qq1 => ?_
      all_goals
      · rw [qq1] at q2
        simp only [Fin.mul_def, Fin.sub_def, Fin.add_def, Fin.ext_iff, BabyBearPrime, UInt32.size] at *
        -- Run `aesop` with semi-safe access to the `omega` tactic
        aesop (add 50% tactic (by omega))

end AddOperation
