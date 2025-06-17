import SP1Foundations

/-- XorOperation is only operating on `U8` because it's used solely for
computing the xor operation over four **bytes**. -/
structure XorOperation where
  value : Vector U8 WORD_BYTE_SIZE

namespace XorOperation

/-- `XorOperation` should result in and of all 4 limbs -/
def spec (cols : XorOperation)
    (a b : Vector (BabyBear) WORD_BYTE_SIZE)
    (is_real : BabyBear) : Prop :=
  is_real ≠ 0 → ∀ i : Fin WORD_BYTE_SIZE,
    a[i] ^^^ b[i] = cols.value[i]

/-- Constraints on `XorOperation` as extracted from the source code:
Sends: AirInteraction { values: [2, cols.value[0], a[0], b[0]], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [2, cols.value[1], a[1], b[1]], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [2, cols.value[2], a[2], b[2]], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [2, cols.value[3], a[3], b[3]], multiplicity: is_real, kind: Byte } -/
def extractedConstraints (cols : XorOperation)
    (a b : Vector (BabyBear) WORD_BYTE_SIZE) (is_real : BabyBear) :
    List (SP1Constraint) :=
  [
    .send (.byte (.ofNat 2) cols.value[0] a[0] b[0]) is_real,
    .send (.byte (.ofNat 2) cols.value[1] a[1] b[1]) is_real,
    .send (.byte (.ofNat 2) cols.value[2] a[2] b[2]) is_real,
    .send (.byte (.ofNat 2) cols.value[3] a[3] b[3]) is_real,
  ]

/-- Cleaned up representation of the `XorOperation` constraints. -/
def idealizedConstraints (cols : XorOperation)
    (a b : Vector (BabyBear) WORD_BYTE_SIZE) : Prop :=
  ((cols.value[0].toFin < 256 ∧ a[0] < 256 ∧ b[0] < 256) → a[0] ^^^ b[0] = cols.value[0]) ∧
  ((a[1] < 256 ∧ b[1] < 256 ∧ cols.value[1].toFin < 256) → a[1] ^^^ b[1] = cols.value[1]) ∧
  ((a[2] < 256 ∧ b[2] < 256 ∧ cols.value[2].toFin < 256) → a[2] ^^^ b[2] = cols.value[2]) ∧
  ((a[3] < 256 ∧ b[3] < 256 ∧ cols.value[3].toFin < 256) → a[3] ^^^ b[3] = cols.value[3])

/-- The idealized constraints are logically equivalent to the extracted ones when `is_real := 1` -/
lemma extractedConstraints_iff_idealizedConstraints
    (cols : XorOperation) (a b : Vector (BabyBear) WORD_BYTE_SIZE) :
    (cols.extractedConstraints a b 1).Forall SP1Constraint.toProp ↔
      cols.idealizedConstraints a b := by
  simp [extractedConstraints, idealizedConstraints]
  -- tauto
  sorry
  -- tauto

/-- The extracted constraints on `XorOperation` imply the spec. -/
theorem correct (cols : XorOperation)
    (a b : Vector (BabyBear) WORD_BYTE_SIZE) (is_real : BabyBear) :
    cols.idealizedConstraints a b → cols.spec a b is_real := by
  simp [idealizedConstraints, spec, sub_eq_zero, mul_eq_zero]
  intros h1 h2 h3 h4 hreal i
  match i with | 0 => ?_ | 1 => ?_ | 2 => ?_ | 3 => ?_
  all_goals sorry

end XorOperation
