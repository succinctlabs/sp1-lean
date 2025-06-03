import SP1Foundations

abbrev WORD_BYTE_SIZE := 4

@[reducible] def AndOperation2 (T : Type) :=
  Vector T WORD_BYTE_SIZE

namespace AndOperation2

/-- `AndOperation` should result in and of all 4 limbs -/
def spec (cols : AndOperation2 (Fin p))
    (a b : Vector (Fin p) WORD_BYTE_SIZE)
    (is_real : Fin p) : Prop :=
  is_real ≠ 0 → ∀ i : Fin WORD_BYTE_SIZE,
    a[i] &&& b[i] = cols[i]

/-- Constraints on `AndOperation` as extracted from the source code:
Sends: AirInteraction { values: [0, cols[0], a[0], b[0]], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [0, cols[1], a[1], b[1]], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [0, cols[2], a[2], b[2]], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [0, cols[3], a[3], b[3]], multiplicity: is_real, kind: Byte } -/
def extractedConstraints (cols : AndOperation2 (Fin p))
    (a b : Vector (Fin p) WORD_BYTE_SIZE) (is_real : Fin p) : Prop :=
  -- TODO: what exactly should we be converting these interactions to?
  -- Trying to say that if the interaction is real then the interaction enforces opcode semantics.
  (is_real ≠ 0 → ByteOpcode.constrain (ByteOpcode.ofNat 0) cols[0] a[0] b[0]) ∧
  (is_real ≠ 0 → ByteOpcode.constrain (ByteOpcode.ofNat 0) cols[1] a[1] b[1]) ∧
  (is_real ≠ 0 → ByteOpcode.constrain (ByteOpcode.ofNat 0) cols[2] a[2] b[2]) ∧
  (is_real ≠ 0 → ByteOpcode.constrain (ByteOpcode.ofNat 0) cols[3] a[3] b[3])

/-- Cleaned up representation of the `AndOperation` constraints. -/
def idealizedConstraints (cols : AndOperation2 (Fin p))
    (a b : Vector (Fin p) WORD_BYTE_SIZE) : Prop :=
  a[0] &&& b[0] = cols[0] ∧
  a[1] &&& b[1] = cols[1] ∧
  a[2] &&& b[2] = cols[2] ∧
  a[3] &&& b[3] = cols[3]

/-- The idealized constraints are logically equivalent to the extracted ones when `is_real := 1` -/
lemma extractedConstraints_iff_idealizedConstraints
    (cols : AndOperation2 (Fin p)) (a b : Vector (Fin p) WORD_BYTE_SIZE) :
    cols.extractedConstraints a b 1 ↔ cols.idealizedConstraints a b := by
  simp [extractedConstraints, idealizedConstraints, ByteOpcode.ofNat, ByteOpcode.constrain]
  tauto

/-- The extracted constraints on `AndOperation` imply the spec. -/
theorem correct (cols : AndOperation2 (Fin p))
    (a b : Vector (Fin p) WORD_BYTE_SIZE) (is_real : Fin p) :
    cols.idealizedConstraints a b → cols.spec a b is_real := by
  simp [idealizedConstraints, spec, sub_eq_zero, mul_eq_zero]
  intros h1 h2 h3 h4 hreal i
  match i with | 0 => ?_ | 1 => ?_ | 2 => ?_ | 3 => ?_
  all_goals trivial

end AndOperation2
