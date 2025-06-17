import SP1Foundations

-- Probably good to still namespace things
namespace U16ToU8OperationSafe

def outputVector (I0 I1 I2 I3 _I4 : BabyBear) :
    Vector BabyBear 4 :=
  let E0 := I0 - I2
  let E2 := E0 * 2005401601
  let E4 := I1 - I3
  let E6 := E4 * 2005401601
  #v[I2, E2, I3, E6]

@[simp] lemma outputVector_eq (I0 I1 I2 I3 I4 : BabyBear) :
    outputVector I0 I1 I2 I3 I4 = #v[I2, (I0 - I2) * 2005401601, I3, (I1 - I3) * 2005401601] := rfl

lemma outputVector_spec (I0 I1 I2 I3 I4 : BabyBear) :
    let v := outputVector I0 I1 I2 I3 I4
    (v[0] + v[1] * 256 = I0) ∧ (v[2] + v[3] * 256 = I1) := by
  simp [mul_assoc]

def constraintSet
    (I0 I1 I2 I3 I4 : BabyBear) :
    (Finset SP1Constraint) :=
  let E0 := I0 - I2
  let E2 := E0 * 2005401601
  let E4 := I1 - I3
  let E6 := E4 * 2005401601
  {
    .sendAirInteraction_byte ByteOpcode.U8Range I2 E2 0 I4,
    .sendAirInteraction_byte ByteOpcode.U8Range I3 E6 0 I4
  }

def constraintProp (I0 I1 I2 I3 _I4 : BabyBear) : Prop :=
  I2 < 256 ∧ (I0 - I2) * 2005401601 < 256 ∧
    I3 < 256 ∧ (I1 - I3) * 2005401601 < 256

lemma toProp_constraintSet_iff_constraintProp
    (I0 I1 I2 I3 I4 : BabyBear) :
    constraintSet_toProp (constraintSet I0 I1 I2 I3 I4) ↔ (I4 = 0 ∨ constraintProp I0 I1 I2 I3 I4) := by
  simp [constraintSet_toProp, constraintProp, constraintSet]
  by_cases hi4 : I4 = 0
  · simp [hi4]
  · simp [hi4, and_assoc]

def Spec (I0 I1 I2 I3 I4 : BabyBear) : Prop :=
  I4 ≠ 0 → (I2 < 256 ∧ (I0 - I2) * 2005401601 < 256 ∧
    I3 < 256 ∧ (I1 - I3) * 2005401601 < 256)

theorem spec_of_constraintSet
    (I0 I1 I2 I3 I4 : BabyBear)
    (h : constraintSet_toProp (constraintSet I0 I1 I2 I3 I4)) :
    Spec I0 I1 I2 I3 I4 := by
  rw [toProp_constraintSet_iff_constraintProp, constraintProp, or_iff_not_imp_left] at h
  exact h

section corrollary

variable {I0 I1 I2 I3 I4 : BabyBear}

lemma outputVector_bound (hi4 : I4 ≠ 0)
    (h : constraintSet_toProp (constraintSet I0 I1 I2 I3 I4)) :
    ∀ x ∈ outputVector I0 I1 I2 I3 I4, x < 256 := by
  simpa using spec_of_constraintSet I0 I1 I2 I3 I4 h hi4

lemma outputVector_get_zero_bound (hi4 : I4 ≠ 0)
    (h : constraintSet_toProp (constraintSet I0 I1 I2 I3 I4)) :
    (outputVector I0 I1 I2 I3 I4)[0] < 256 :=
  outputVector_bound hi4 h _ <| by simp

lemma outputVector_get_one_bound (hi4 : I4 ≠ 0)
    (h : constraintSet_toProp (constraintSet I0 I1 I2 I3 I4)) :
    (outputVector I0 I1 I2 I3 I4)[1] < 256 :=
  outputVector_bound hi4 h _ <| by simp

lemma outputVector_get_two_bound (hi4 : I4 ≠ 0)
    (h : constraintSet_toProp (constraintSet I0 I1 I2 I3 I4)) :
    (outputVector I0 I1 I2 I3 I4)[2] < 256 :=
  outputVector_bound hi4 h _ <| by simp

lemma outputVector_get_three_bound (hi4 : I4 ≠ 0)
    (h : constraintSet_toProp (constraintSet I0 I1 I2 I3 I4)) :
    (outputVector I0 I1 I2 I3 I4)[3] < 256 :=
  outputVector_bound hi4 h _ <| by simp

end corrollary

end U16ToU8OperationSafe
