import SP1Operations.Operation.U16toU8OperationUnsafe
import SP1Operations.Operation.U16toU8OperationSafe.Operation
import SP1Operations.Operation.U16toU8OperationSafe.Constraints

namespace U16toU8OperationSafe

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
