import SP1Operations.U16toU8OperationUnsafe

namespace U16toU8OperationSafe

def constraints
  (u16_values : (Vector (Fin BB) 4))
  (cols : U16toU8Operation)
  (is_real : (Fin BB))
  : (Vector (Fin BB) 8) × SP1ConstraintList :=
  let E0 : Fin BB := u16_values[0] - cols.low_bytes[0]
  let E1 : Fin BB := E0 * 2005401601
  let E2 : Fin BB := u16_values[1] - cols.low_bytes[1]
  let E3 : Fin BB := E2 * 2005401601
  let E4 : Fin BB := u16_values[2] - cols.low_bytes[2]
  let E5 : Fin BB := E4 * 2005401601
  let E6 : Fin BB := u16_values[3] - cols.low_bytes[3]
  let E7 : Fin BB := E6 * 2005401601
  ⟨#v[cols.low_bytes[0], E1, cols.low_bytes[1], E3, cols.low_bytes[2], E5, cols.low_bytes[3], E7], [
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[0] E1) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[1] E3) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[2] E5) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[3] E7) is_real),
  ]⟩

end U16toU8OperationSafe

-- @[simp] lemma outputVector_eq (I0 I1 I2 I3 I4 : Fin BB) :
--     (constraints I0 I1 I2 I3 I4).1 = #v[I2, (I0 - I2) * 2005401601, I3, (I1 - I3) * 2005401601] := rfl

-- lemma outputVector_spec (I0 I1 I2 I3 I4 : Fin BB) :
--     let v := (constraints I0 I1 I2 I3 I4).1
--     (v[0] + v[1] * 256 = I0) ∧ (v[2] + v[3] * 256 = I1) := by
--   simp [mul_assoc]

-- def constraintProp (I0 I1 I2 I3 _I4 : Fin BB) : Prop :=
--   I2 < 256 ∧ (I0 - I2) * 2005401601 < 256 ∧
--     I3 < 256 ∧ (I1 - I3) * 2005401601 < 256

-- lemma constraints_iff_constraintProp
--     (I0 I1 I2 I3 I4 : Fin BB) :
--     (constraints I0 I1 I2 I3 I4).2.allHold ↔
--       (I4 = 0 ∨ constraintProp I0 I1 I2 I3 I4) := by
--   simp [constraintProp, constraints]
--   by_cases hi4 : I4 = 0
--   · simp [hi4]
--   · simp [hi4, and_assoc]

-- def Spec (I0 I1 I2 I3 I4 : Fin BB) : Prop :=
--   I4 ≠ 0 → (I2 < 256 ∧ (I0 - I2) * 2005401601 < 256 ∧
--     I3 < 256 ∧ (I1 - I3) * 2005401601 < 256)

-- theorem spec_of_constraintSet
--     (I0 I1 I2 I3 I4 : Fin BB)
--     (h : (constraints I0 I1 I2 I3 I4).2.allHold) :
--     Spec I0 I1 I2 I3 I4 := by
--   rw [constraints_iff_constraintProp, constraintProp, or_iff_not_imp_left] at h
--   exact h

-- section corrollary

-- variable {I0 I1 I2 I3 I4 : Fin BB}

-- lemma outputVector_bound (hi4 : I4 ≠ 0)
--     (h : (constraints I0 I1 I2 I3 I4).2.allHold) :
--     ∀ x ∈ (constraints I0 I1 I2 I3 I4).1, x < 256 := by
--   simpa using spec_of_constraintSet I0 I1 I2 I3 I4 h hi4

-- lemma outputVector_bound' (hi4 : I4 ≠ 0)
--     (h : (constraints I0 I1 I2 I3 I4).2.allHold)
--     (i : Fin 4) : (constraints I0 I1 I2 I3 I4).1[i] < 256 :=
--   outputVector_bound hi4 h _ (Vector.mem_of_getElem rfl)

-- end corrollary

-- end U16toU8OperationSafe
