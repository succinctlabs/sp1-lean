import SP1Operations.Operation.AddOperation
import SP1Chips.Jal.Constraints

namespace Jal

section u16_composition

set_option maxHeartbeats 400000 in
theorem u16_composition 
  (Main : Vector (Fin BB) 31)
  (cstrs : (constraints Main).allHold)
  : (constraints Main).U16CompProp
  := by
    -- Expand all definitions until no more *.constraints remain
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall, AddOperation.constraints]

    -- Decompose the constraints hypothesis
    simp [constraints, SP1Constraint.toProp, List.Forall, sub_eq_zero] at cstrs
    
    -- First, handle the is_real = 0 case
    have h_main30 : Main[30] = 0 ∨ Main[30] = 1 := by
      simp_all only

    cases h_main30
    · rename_i h_not_real
      -- When Main[30] = 0, all implications are trivially true
      simp [h_not_real]

    rename_i h_is_real
    -- When Main[30] = 1, we need to prove the bounds
    simp [h_is_real] at *

    -- Extract the AddOperation constraints from cstrs
    obtain ⟨add1_cstrs, add2_cstrs, chip_cstrs⟩ := cstrs

    -- The goal has two parts
    refine ⟨?_, ?_⟩

    -- First goal: bounds on Main[22], Main[23], Main[24] (output of first AddOperation)
    · -- Main[30] = 1, so add1_cstrs are the constraints with is_real = 1
      -- Use AddOperation.isU64_of_allHold_constraints to get bounds
      have h_output_u64 : Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := 
        AddOperation.isU64_of_allHold_constraints _ _ _ add1_cstrs
      have h_bounds := Word.lt_cases_of_isU64 h_output_u64
      simp at h_bounds
      refine ⟨?_, by extract_from_and h_bounds, by extract_from_and h_bounds⟩
      · show Main[22].val ≤ 65536
        have : Main[22].val < 65536 := by simp_all only
        linarith

    -- Second goal: bounds on Main[26-29] and Main[6]
    · refine ⟨?_, ?_⟩

      -- First part: bounds on Main[26-29]
      · -- Main[26-29] come from the second AddOperation with is_real = 1 - Main[13]
        -- We need to handle two cases based on Main[13]
        have h_main13 : Main[13] = 0 ∨ Main[13] = 1 := by extract_from_and chip_cstrs
        cases h_main13 with
        | inl h_main13_0 =>
          -- When Main[13] = 0, the second AddOperation has is_real = 1
          simp [h_main13_0] at add2_cstrs
          have h_output2_u64 : Word.isU64 #v[Main[26], Main[27], Main[28], Main[29]] := 
            AddOperation.isU64_of_allHold_constraints _ _ _ add2_cstrs
          exact Word.lt_cases_of_isU64 h_output2_u64
        | inr h_main13_1 =>
          -- When Main[13] = 1, we need to prove Main[26-29] = 0
          simp [h_main13_1] at chip_cstrs
          have h29 : Main[29] = 0 := by simp_all only [chip_cstrs]
          obtain ⟨h26, h27, h28⟩ : Main[26] = 0 ∧ Main[27] = 0 ∧ Main[28] = 0 := by split_ands <;> simp_all only
          simp [h26, h27, h28, h29]

      -- Second part: bound on Main[6]
      · calc Main[6] < 32 := by simp_all only [chip_cstrs]
             _ < 65536 := by trivial

#print axioms u16_composition

end u16_composition

end Jal
