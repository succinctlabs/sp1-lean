import SP1Foundations

/-- OrOperation is only operating on `U8` because it's used solely for
computing the or operation over four **bytes**. -/
structure OrOperation where
  value : Vector U8 WORD_BYTE_SIZE

namespace OrOperation

/-- `OrOperation` should result in and of all 4 limbs -/
def spec (cols : OrOperation)
    (a b : Vector (BabyBear) WORD_BYTE_SIZE)
    (is_real : BabyBear) : Prop :=
  is_real ≠ 0 → ∀ i : Fin WORD_BYTE_SIZE,
    a[i] ||| b[i] = cols.value[i]

-- /-- Constraints on `OrOperation` as extracted from the source code:
-- Sends: AirInteraction { values: [1, cols.value[0], a[0], b[0]], multiplicity: is_real, kind: Byte }
-- Sends: AirInteraction { values: [1, cols.value[1], a[1], b[1]], multiplicity: is_real, kind: Byte }
-- Sends: AirInteraction { values: [1, cols.value[2], a[2], b[2]], multiplicity: is_real, kind: Byte }
-- Sends: AirInteraction { values: [1, cols.value[3], a[3], b[3]], multiplicity: is_real, kind: Byte } -/
-- def extractedConstraints (cols : OrOperation)
--     (a b : Vector (BabyBear) WORD_BYTE_SIZE) (is_real : BabyBear) :
--     Finset (SP1Constraint) :=
--   {
--   .sendAirInteraction_byte (.ofNat 1) cols.value[0] a[0] b[0] is_real,
--   .sendAirInteraction_byte (.ofNat 1) cols.value[1] a[1] b[1] is_real,
--   .sendAirInteraction_byte (.ofNat 1) cols.value[2] a[2] b[2] is_real,
--   .sendAirInteraction_byte (.ofNat 1) cols.value[3] a[3] b[3] is_real
--   }

-- /-- Cleaned up representation of the `OrOperation` constraints. -/
-- def idealizedConstraints (cols : OrOperation)
--     (a b : Vector (BabyBear) WORD_BYTE_SIZE) : Prop :=
--   a[0] ||| b[0] = cols.value[0] ∧
--   a[1] ||| b[1] = cols.value[1] ∧
--   a[2] ||| b[2] = cols.value[2] ∧
--   a[3] ||| b[3] = cols.value[3]

-- /-- The idealized constraints are logically equivalent to the extracted ones when `is_real := 1` -/
-- lemma extractedConstraints_iff_idealizedConstraints
--     (cols : OrOperation) (a b : Vector (BabyBear) WORD_BYTE_SIZE) :
--     constraintSet_toProp (cols.extractedConstraints a b 1) ↔
--       cols.idealizedConstraints a b := by
--   simp [extractedConstraints, idealizedConstraints]
--   tauto

-- /-- The extracted constraints on `OrOperation` imply the spec. -/
-- theorem correct (cols : OrOperation)
--     (a b : Vector (BabyBear) WORD_BYTE_SIZE) (is_real : BabyBear) :
--     cols.idealizedConstraints a b → cols.spec a b is_real := by
--   simp [idealizedConstraints, spec, sub_eq_zero, mul_eq_zero]
--   intros h1 h2 h3 h4 hreal i
--   match i with | 0 => ?_ | 1 => ?_ | 2 => ?_ | 3 => ?_
--   all_goals trivial

end OrOperation
