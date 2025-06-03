import SP1Foundations

@[reducible] def Add4Operation2 (T : Type) := Word T

namespace Add4Operation2

/-- `AddOperation` should either give the direct sum of the two input values, with one possible overflow.
This is more explicit than saying that `(a.toNat + b.toNat) % 2^32 = cols.toNat`. -/
def spec (cols : Add4Operation2 (Fin p))
    (a b c d : Word (Fin p)) : Prop :=
  a.isUInt32 → b.isUInt32 → c.isUInt32 → d.isUInt32 →
    (a.toNat + b.toNat + c.toNat + d.toNat) % 2^32 = cols.toNat

-- /-- TODO: Constraints on `AddOperation` as extracted from the source code. -/
-- def extractedConstraints (cols : AddOperation (Fin p))
--     (a : Word (Fin p)) (b : Word (Fin p)) : Prop :=
--   (((((a[0] + b[0]) - cols[0]) + (0 : Fin p)) *
--     (2013235201 : Fin p)) * (((((a[0] + b[0]) - cols[0]) + 0) * 2013235201) - 1)) = 0 ∧
--     (((((a[1] + b[1]) - cols[1]) + ((((a[0] + b[0]) - cols[0]) + (0 : Fin p)) *
--     (2013235201 : Fin p))) * (2013235201 : Fin p)) * (((((a[1] + b[1]) - cols[1]) +
--     ((((a[0] + b[0]) - cols[0]) + 0) * 2013235201)) * 2013235201) - 1)) = 0 ∧
--     cols[0].val < base ∧ cols[1].val < base

/-- Cleaned up representation of the `AddOperation` constraints. -/
def idealizedConstraints (cols : Add4Operation2 (Fin p))
    (aw bw cw dw : Word (Fin p)) : Prop :=
  let carry0 := 0
  let carry1 := (aw[0] + bw[0] + cw[0] + dw[0] - cols[0] + carry0) * baseInv
  let carry2 := (aw[1] + bw[1] + cw[1] + dw[1] - cols[1] + carry1) * baseInv
  carry1 * (carry1 - 1) = 0 ∧ -- isBool check
  carry2 * (carry2 - 1) = 0 ∧ -- isBool check
  cols.isUInt32 -- slice range checks

-- /-- TODO: The idealized constraints are logically equivalent to the extracted ones. -/
-- lemma extractedConstraints_iff_idealizedConstraints (cols : AddOperation (Fin p))
--     (a : Word (Fin p)) (b : Word (Fin p)) :
--     cols.extractedConstraints a b ↔ cols.idealizedConstraints a b := by
--   simp [extractedConstraints, idealizedConstraints, Word.isUInt32]

/-- The extracted constraints on `AddOperation` imply the spec. -/
theorem correct [Fact (Nat.Prime p)]
    (cols : Add4Operation2 (Fin p)) (aw bw cw dw: Word (Fin p)) :
    cols.idealizedConstraints aw bw cw dw → cols.spec aw bw cw dw := by
  -- Unfold the definitions of constraints and spec
  simp [idealizedConstraints, spec, sub_eq_zero, mul_eq_zero]
  -- Introduce all of the hypothesis from the constraints
  intros h1 h2 hcols_u32 ha_u32 hb_u32
  -- Split on whether the lower limb addition causes a carry
  cases h1 with | inl h1 => ?_ | inr h1 => ?_
  all_goals
  · rw [h1] at h2
    -- Reduce expressions to natural number arithmetic
    simp [Fin.add_def, Fin.sub_def, Fin.ext_iff, p, Word.toNat, Word.isUInt32] at *
    -- Apply linear constraint solver
    sorry --omega

end Add4Operation2
