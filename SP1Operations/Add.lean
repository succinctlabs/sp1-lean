import SP1Foundations

structure AddOperation where
  value : Word U16

def AddOperation.spec
  (cols : AddOperation)
  (a : Word U16)
  (b : Word U16)
  (is_real : U2) : Prop :=
    is_real = U2.one →
    a.toFin32_U16 + b.toFin32_U16 = cols.value.toFin32_U16

def AddOperation.constraints
    (cols : AddOperation)
    (a : Word U16)
    (b : Word U16)
    (is_real : U2): Prop :=
    (is_real * ((((a[0].val + b[0].val) - cols.value[0].val) + (0 : BabyBear)) * (2013235201 : BabyBear)) * (((((a[0].val + b[0].val) - cols.value[0].val) + 0) * 2013235201) - 1)) = 0 ∧
    (is_real * ((((a[1].val + b[1].val) - cols.value[1].val) + ((((a[0].val + b[0].val) - cols.value[0].val) + (0 : BabyBear)) * (2013235201 : BabyBear))) * (2013235201 : BabyBear)) * (((((a[1].val + b[1].val) - cols.value[1].val) + ((((a[0].val + b[0].val) - cols.value[0].val) + 0) * 2013235201)) * 2013235201) - 1)) = 0

def AddOperation.constraints'
    (cols : AddOperation)
    (a : Word U16)
    (b : Word U16)
    (is_real : U2): Prop :=
    let carry0 : BabyBear := 0
    let carry1 : BabyBear := (a[0] + b[0] - cols.value[0] + carry0) * (baseInv : BabyBear)
    let carry2 : BabyBear := (a[1] + b[1] - cols.value[1] + carry1) * (baseInv : BabyBear)
    (is_real.val * carry1 * (carry1 - 1)) = 0 ∧
    (is_real.val * carry2 * (carry2 - 1)) = 0

def AddOperation.constraints_iff_constraints'
  (cols : AddOperation)
  (a : Word U16)
  (b : Word U16)
  (is_real : U2)
  : AddOperation.constraints cols a b is_real ↔ AddOperation.constraints' cols a b is_real:=
  by
    simp [AddOperation.constraints, AddOperation.constraints']

theorem AddOperation.correct
  (cols : AddOperation)
  (a : Word U16)
  (b : Word U16)
  (is_real : U2)
  : cols.constraints a b is_real → cols.spec a b is_real :=
    by
      rw [cols.constraints_iff_constraints' a b is_real]
      intro ⟨q1, q2⟩

      -- Since is_real = 1, substitute and apply 1 * x = x to get original constraints
      intro h_is_real
      have is_real_val_eq_one : is_real.val = 1 := by aesop
      rw [is_real_val_eq_one] at q1 q2

      simp [Word.toFin32_U16]
      let _ : a[0].val.val < 65536 := a[0].in_range
      let _ : a[1].val.val < 65536 := a[1].in_range
      let _ : b[0].val.val < 65536 := b[0].in_range
      let _ : b[1].val.val < 65536 := b[1].in_range
      let _ : cols.value[0].val.val < 65536 := cols.value[0].in_range
      let _ : cols.value[1].val.val < 65536 := cols.value[1].in_range

      -- do basic arithmetic simplification
      simp [sub_eq_zero, mul_eq_zero] at q1 q2
      cases q1 with | inl qq1 => ?_ | inr qq1 => ?_
      all_goals
      · rw [qq1] at q2
        simp [Fin.mul_def, Fin.sub_def, Fin.add_def, Fin.ext_iff] at *
        simp [BabyBearPrime, UInt32.size] at *
        rw [fin_val_simp (show 65536 < BabyBearPrime by linarith)] at *
        omega
