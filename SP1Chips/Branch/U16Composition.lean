import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReaderImmutable
import SP1Chips.Branch.Constraints

namespace Branch

section u16_composition

set_option maxHeartbeats 800000 in
theorem u16_composition 
  (Main : Vector (Fin BB) 45)
  (cstrs : (constraints Main).allHold)
  : (constraints Main).U16CompProp
  := by
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall, LtOperationSigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints, CPUState.constraints, ITypeReaderImmutable.constraints]
    
    -- Now expand LtOperationUnsigned.constraints in the goal
    simp [LtOperationUnsigned.constraints, SP1Constraint.toU16CompProp, List.Forall]
    
    -- Expand U16CompareOperation.constraints
    simp [U16CompareOperation.constraints, SP1Constraint.toU16CompProp, List.Forall]
    
    -- Decompose the constraints hypothesis
    simp [constraints] at cstrs
    obtain ⟨cpu_cstrs, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
    
    -- First, establish that the sum of selectors is either 0 or 1
    have h_sum_bool : Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = 0 ∨ 
                      Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = 1 := by
      obtain ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨h, _⟩⟩⟩⟩⟩⟩⟩ := chip_cstrs
      simp [sub_eq_zero] at h
      exact h
    
    cases h_sum_bool
    · -- Case: sum = 0 (no operation selected)
      rename_i h_not_real
      simp [h_not_real]
      
    -- Case: sum = 1 (exactly one operation selected)  
    rename_i h_sum_one
    
    refine ⟨?_, ?_, ?_⟩
    
    -- First goal: Next PC bounds
    · intro h_is_real
      -- Since sum = 1, we know h_is_real is trivially true
      simp [h_sum_one] at h_is_real
      
      -- Now the bounds should be simpler to extract
      simp [h_sum_one] at chip_cstrs
      -- Extract the bounds from chip_cstrs
      split_ands
      · show Main[25].val ≤ 65536
        have : Main[25].val < 65536 := by simp_all only
        clear * - this
        linarith
      · show Main[26].val < 65536
        simp_all only
      · show Main[27].val < 65536
        simp_all only
      
    -- Second goal: op_a bounds
    · intro h_is_real
      simp [h_sum_one] at h_is_real
      simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp, h_sum_one] at reader_cstrs
      refine ⟨?_, ?_⟩
      · have h_op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
        exact Word.lt_cases_of_isU64 h_op_a_is_u64
      · calc Main[6] < 32 := by simp_all only
               _ < 65536 := by trivial
        
    -- Third goal: op_b bounds  
    · intro h_is_real
      simp [h_sum_one] at h_is_real
      simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp, h_sum_one] at reader_cstrs
      refine ⟨?_, ?_⟩
      · have h_op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
        exact Word.lt_cases_of_isU64 h_op_b_is_u64
      · have h_reg_bound : Main[14] < 65536 := by simp_all only
        exact h_reg_bound

#print axioms u16_composition

end u16_composition

end Branch
