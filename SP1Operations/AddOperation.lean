import SP1Foundations

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

def constraints
    (cols : AddOperation)
    (a : Word U16)
    (b : Word U16)
    (is_real : U2): Prop :=
    (is_real * ((((a[0].val + b[0].val) - cols.value[0].val) + (0 : BabyBear)) * (2013235201 : BabyBear)) * (((((a[0].val + b[0].val) - cols.value[0].val) + 0) * 2013235201) - 1)) = 0 ∧
    (is_real * ((((a[1].val + b[1].val) - cols.value[1].val) + ((((a[0].val + b[0].val) - cols.value[0].val) + (0 : BabyBear)) * (2013235201 : BabyBear))) * (2013235201 : BabyBear)) * (((((a[1].val + b[1].val) - cols.value[1].val) + ((((a[0].val + b[0].val) - cols.value[0].val) + 0) * 2013235201)) * 2013235201) - 1)) = 0

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
  (is_real : U2)
  : AddOperation.constraints cols a b is_real ↔ AddOperation.constraints' cols a b is_real:=
  by
    simp [AddOperation.constraints, AddOperation.constraints']

theorem correct
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

end AddOperation

@[reducible] def AddOperation2 (T : Type) := Word T

namespace AddOperation2

/-- `AddOperation` should result in wrapping addition of the outputs.
Note that we ignore `is_real` for now. -/
def spec (cols : AddOperation2 (Fin p)) (a b : Word (Fin p)) : Prop :=
  a.isUInt32 → b.isUInt32 →
    (a.toNat + b.toNat) % 2^32 = cols.toNat

/-- Constraints on `AddOperation` as extracted from the source code:
Asserting expr 3: `(is_real * (is_real - 1))`
Asserting expr 15: `(is_real * (((((a[0] + b[0]) - cols[0]) + 0) * 2013235201) * (((((a[0] + b[0]) - cols[0]) + 0) * 2013235201) - 1)))`
Asserting expr 25: `(is_real * (((((a[1] + b[1]) - cols[1]) + ((((a[0] + b[0]) - cols[0]) + 0) * 2013235201)) * 2013235201) * (((((a[1] + b[1]) - cols[1]) + ((((a[0] + b[0]) - cols[0]) + 0) * 2013235201)) * 2013235201) - 1)))` -/
def extractedConstraints (cols : AddOperation2 (Fin p))
    (a b : Word (Fin p)) (is_real : Fin p) : Prop :=
  is_real * (is_real - 1) = 0 ∧
  is_real * (((((a[0] + b[0]) - cols[0]) + 0) * 2013235201) * (((((a[0] + b[0]) - cols[0]) + 0) * 2013235201) - 1)) = 0 ∧
  is_real * (((((a[1] + b[1]) - cols[1]) + ((((a[0] + b[0]) - cols[0]) + 0) * 2013235201)) * 2013235201) *
    (((((a[1] + b[1]) - cols[1]) + ((((a[0] + b[0]) - cols[0]) + 0) * 2013235201)) * 2013235201) - 1)) = 0

/-- Cleaned up representation of the `AddOperation` constraints. Assumes that `is_real == 1` -/
def idealizedConstraints (cols : AddOperation2 (Fin p))
    (a b : Word (Fin p)) : Prop :=
  let carry0 := 0
  let carry1 := (a[0] + b[0] - cols[0] + carry0) * baseInv
  let carry2 := (a[1] + b[1] - cols[1] + carry1) * baseInv
  carry1 * (carry1 - 1) = 0 ∧ -- isBool check
  carry2 * (carry2 - 1) = 0 -- isBool check

/-- The idealized constraints are logically equivalent to the extracted ones given `is_real := 1`. -/
lemma extractedConstraints_iff_idealizedConstraints
    (cols : AddOperation2 (Fin p)) (a b : Word (Fin p)) :
    cols.extractedConstraints a b 1 ↔ cols.idealizedConstraints a b := by
  simp [extractedConstraints, idealizedConstraints, Word.isUInt32]

/-- The extracted constraints on `AddOperation` imply the spec. -/
theorem correct [Fact (Nat.Prime p)] (cols : AddOperation2 (Fin p))
    (a b : Word (Fin p)) (hcols : cols.isUInt32) :
    cols.idealizedConstraints a b → cols.spec a b := by
  -- Unfold the definitions of constraints and spec
  simp [idealizedConstraints, spec, sub_eq_zero, mul_eq_zero]
  -- Introduce all of the hypothesis from the constraints
  intros h1 h2 ha_u32 hb_u32
  -- Split on whether the lower limb addition causes a carry
  cases h1 with | inl h1 => ?_ | inr h1 => ?_
  all_goals -- In both cases can now reduce down to the `omega` linear constraint solver
  · rw [h1] at h2
    simp [Fin.add_def, Fin.sub_def, Fin.ext_iff, p, Word.toNat, Word.isUInt32] at *
    sorry
    -- omega

end AddOperation2
