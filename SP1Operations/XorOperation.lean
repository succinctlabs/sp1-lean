import SP1Foundations

abbrev WORD_BYTE_SIZE := 4

@[reducible] def XorOperation (T : Type) :=
  Vector T WORD_BYTE_SIZE

namespace XorOperation

/-- `XorOperation` should result in and of all 4 limbs -/
def spec (cols : XorOperation (BabyBear))
    (a b : Vector (BabyBear) WORD_BYTE_SIZE)
    (is_real : BabyBear) : Prop :=
  is_real ≠ 0 → ∀ i : Fin WORD_BYTE_SIZE,
    a[i] ^^^ b[i] = cols[i]

/-- Constraints on `XorOperation` as extracted from the source code:
Sends: AirInteraction { values: [2, cols[0], a[0], b[0]], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [2, cols[1], a[1], b[1]], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [2, cols[2], a[2], b[2]], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [2, cols[3], a[3], b[3]], multiplicity: is_real, kind: Byte } -/
def extractedConstraints (cols : XorOperation (BabyBear))
    (a b : Vector (BabyBear) WORD_BYTE_SIZE) (is_real : BabyBear) :
    List (SP1Constraint) :=
  [.sendAirInteraction_byte (.ofNat 2) cols[0] a[0] b[0] is_real,
   .sendAirInteraction_byte (.ofNat 2) cols[1] a[1] b[1] is_real,
   .sendAirInteraction_byte (.ofNat 2) cols[2] a[2] b[2] is_real,
   .sendAirInteraction_byte (.ofNat 2) cols[3] a[3] b[3] is_real,]

/-- Cleaned up representation of the `XorOperation` constraints. -/
def idealizedConstraints (cols : XorOperation (BabyBear))
    (a b : Vector (BabyBear) WORD_BYTE_SIZE) : Prop :=
  a[0] ^^^ b[0] = cols[0] ∧
  a[1] ^^^ b[1] = cols[1] ∧
  a[2] ^^^ b[2] = cols[2] ∧
  a[3] ^^^ b[3] = cols[3]

/-- The idealized constraints are logically equivalent to the extracted ones when `is_real := 1` -/
lemma extractedConstraints_iff_idealizedConstraints
    (cols : XorOperation (BabyBear)) (a b : Vector (BabyBear) WORD_BYTE_SIZE) :
    constraintList_toProp (cols.extractedConstraints a b 1) ↔
      cols.idealizedConstraints a b := by
  simp [extractedConstraints, idealizedConstraints, constraintList_toProp,
    ByteOpcode.ofNat, ByteOpcode.constrain, SP1Constraint.toProp]
  tauto

/-- The extracted constraints on `XorOperation` imply the spec. -/
theorem correct (cols : XorOperation (BabyBear))
    (a b : Vector (BabyBear) WORD_BYTE_SIZE) (is_real : BabyBear) :
    cols.idealizedConstraints a b → cols.spec a b is_real := by
  simp [idealizedConstraints, spec, sub_eq_zero, mul_eq_zero]
  intros h1 h2 h3 h4 hreal i
  match i with | 0 => ?_ | 1 => ?_ | 2 => ?_ | 3 => ?_
  all_goals trivial

end XorOperation
