import SP1Foundations

structure Add4Operation where
  value : Word U16

def Add4Operation.spec
  (cols : Add4Operation)
  (a : Word U16)
  (b : Word U16)
  (cc : Word U16)
  (d : Word U16)
  (is_real : U2) : Prop :=
    is_real = U2.one →
    a.toFin32_U16 + b.toFin32_U16 + cc.toFin32_U16 + d.toFin32_U16 = cols.value.toFin32_U16

def Add4Operation.constraints
    (cols : Add4Operation)
    (a : Word U16)
    (b : Word U16)
    (cc : Word U16)
    (d : Word U16)
    (is_real : U2): Prop :=
    (is_real = U2.one → ((((((a[0].val + b[0].val) + cc[0].val) + d[0].val) - cols.value[0].val) + 0) * 2013235201) < 256) -- checking this is < 8 bytes
    ∧ (is_real = U2.one → ((((((a[1].val + b[1].val) + cc[1].val) + d[1].val) - cols.value[1].val) + ((((((a[0].val + b[0].val) + cc[0].val) + d[0].val) - cols.value[0].val) + 0) * 2013235201)) * 2013235201) < 256)

def Add4Operation.constraints'
    (cols : Add4Operation)
    (a : Word U16)
    (b : Word U16)
    (cc : Word U16)
    (d : Word U16)
    (is_real : U2): Prop :=
    let carry0 : BabyBear := 0
    let carry1 : BabyBear := (a[0].val + b[0].val + cc[0].val + d[0].val - cols.value[0].val + carry0) * baseInv
    let carry2 : BabyBear := (a[1].val + b[1].val + cc[1].val + d[1] - cols.value[1].val + carry1) * baseInv
    (is_real = U2.one → carry1 < 256)
    ∧ (is_real = U2.one → carry2 < 256)

theorem helper1 {n : Nat} {a : Nat} {ha : a < n} {x : Nat} : (Fin.mk a ha) < x → a % n < x := by sorry

def Add4Operation.constraints_iff_constraints'
  (cols : Add4Operation)
  (a : Word U16)
  (b : Word U16)
  (cc : Word U16)
  (d : Word U16)
  (is_real : U2)
  : cols.constraints a b cc d is_real ↔ cols.constraints' a b cc d is_real :=
  by
    simp [constraints, constraints']

theorem Add4Operation.correct (cols : Add4Operation)
  (a : Word U16)
  (b : Word U16)
  (cc : Word U16)
  (d : Word U16)
  (is_real : U2)
  : cols.constraints a b cc d is_real → cols.spec a b cc d is_real :=
  by
    rw [cols.constraints_iff_constraints']
    intro ⟨h1, h2⟩
    intro h_is_real

    have q1 : ((((((a[0].val + b[0].val) + cc[0].val) + d[0].val) - cols.value[0].val) + 0) * baseInv) < 256 := h1 h_is_real
    have q2 : ((((((a[1].val + b[1].val) + cc[1].val) + d[1].val) - cols.value[1].val) + ((((((a[0].val + b[0].val) + cc[0].val) + d[0].val) - cols.value[0].val) + 0) * baseInv)) * baseInv) < 256 := h2 h_is_real
    clear h1 h2
    simp at q1 q2

    -- Extract bounds on values
    have a0_bound : a[0].val.val < 65536 := a[0].in_range
    have a1_bound : a[1].val.val < 65536 := a[1].in_range
    have b0_bound : b[0].val.val < 65536 := b[0].in_range
    have b1_bound : b[1].val.val < 65536 := b[1].in_range
    have c0_bound : cc[0].val.val < 65536 := cc[0].in_range
    have c1_bound : cc[1].val.val < 65536 := cc[1].in_range
    have d0_bound : d[0].val.val < 65536 := d[0].in_range
    have d1_bound : d[1].val.val < 65536 := d[1].in_range
    have v0_bound : cols.value[0].val.val < 65536 := cols.value[0].in_range
    have v1_bound : cols.value[1].val.val < 65536 := cols.value[1].in_range

    simp [Word.toFin32_U16]
    simp [Fin.add_def, Fin.mul_def, Fin.sub_def, add_assoc] at *
    sorry
