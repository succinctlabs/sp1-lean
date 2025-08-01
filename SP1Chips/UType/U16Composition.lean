import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.JTypeReader
import SP1Chips.UType.Constraints

namespace UType

section u16_composition

set_option maxHeartbeats 400000 in
theorem u16_composition 
  (Main : Vector (Fin BB) 31)
  (cstrs : (constraints Main).allHold)
  : (constraints Main).U16CompProp
  := by
    -- First, let's expand and see what we're dealing with
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall, 
          AddOperation.constraints, CPUState.constraints, JTypeReader.constraints]
    
    -- Decompose the constraints hypothesis
    simp [constraints, SP1Constraint.toProp, List.Forall, sub_eq_zero] at cstrs
    
    -- Extract that Main[30] is bool (is_real)
    have h_main30 : Main[30] = 0 ∨ Main[30] = 1 := by
      obtain ⟨cpu_cstrs, add_cstrs, reader_cstrs, chip_cstrs⟩ := cstrs
      exact chip_cstrs.1
    
    -- Handle the is_real = 0 case first
    cases h_main30
    · rename_i h_not_real
      simp [h_not_real]
    
    -- When is_real = 1, we need to prove the bounds
    rename_i h_is_real
    simp [h_is_real] at *
    
    -- Extract the constraints components
    obtain ⟨cpu_cstrs, add_cstrs, reader_cstrs, chip_cstrs⟩ := cstrs
    
    -- The goal has two parts
    refine ⟨?_, ?_⟩
    
    -- First goal: PC bounds
    · -- PC bounds come from JTypeReader constraints
      simp [JTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
      refine ⟨?_, by extract_from_and reader_cstrs, by extract_from_and reader_cstrs⟩
      -- Prove PC + 4 ≤ 65536
      have h_pc_nat_mul4 : Main[3].val % 4 = 0 := by
        have h_pc_mul4 : Main[3] % 4 = 0 := by extract_from_and reader_cstrs
        have : (Main[3] % 4).val = Main[3].val % 4 := Fin.mod_val Main[3] 4
        rw [h_pc_mul4] at this
        simp at this
        exact this.symm
      have h_pc_nat_bound : Main[3].val < 65536 := by extract_from_and reader_cstrs
      have h_no_overflow : Main[3].val + 4 < BB := by
        calc Main[3].val + 4 < 65536 + 4 := by omega
        _ = 65540 := by norm_num
        _ < BB := by norm_num
      rw [Fin.le_iff_val_le_val]
      rw [Fin.val_add_eq_of_add_lt h_no_overflow]
      omega
    
    -- Second goal: AddOperation output bounds and register bound
    · refine ⟨?_, ?_⟩
      
      -- First part: Main[25-28] bounds (output of AddOperation)
      · -- The AddOperation has is_real = 1 - Main[13]
        -- We need to consider two cases based on Main[13]
        have h_main13 : Main[13] = 0 ∨ Main[13] = 1 := by
          simp [JTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
          extract_from_and reader_cstrs
        cases h_main13 with
        | inl h_main13_0 =>
          -- When Main[13] = 0, the AddOperation has is_real = 1
          simp [h_main13_0] at add_cstrs
          have h_output_u64 : Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := 
            AddOperation.isU64_of_allHold_constraints _ _ _ add_cstrs
          exact Word.lt_cases_of_isU64 h_output_u64
        | inr h_main13_1 =>
          -- When Main[13] = 1, this case is actually impossible
          -- From chip_cstrs, we have Main[30] = 1 ∨ Main[13] = 0
          -- Since Main[30] = 1 (we're in the is_real = 1 case) and Main[13] = 1,
          -- we get 1 = 1 ∨ 0 = 0, which is 1 = 1 ∨ False, which is just True
          -- Actually wait, the constraint says Main[30] = 1 ∨ Main[13] = 0
          -- We have Main[30] = 1, so the constraint is satisfied regardless of Main[13]
          -- So this case is possible, but AddOperation has is_real = 0
          -- Main[25-28] come from the output of AddOperation
          -- Since AddOperation doesn't add memory receive constraints when is_real = 0,
          -- we need to get the bounds from somewhere else
          -- Looking at chip_cstrs, Main[22-24] are defined in terms of Main[29] * Main[3-5]
          -- And from the UType constraints, Main[25-28] is the output of AddOperation
          -- Let's check if we can derive bounds from the reader constraints
          simp [JTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
          -- Extract that Main[25-28] = 0 when Main[13] = 1
          have h25 : Main[25] = 0 := by
            have : Main[13] = 0 ∨ Main[25] = 0 := by extract_from_and reader_cstrs
            simp [h_main13_1] at this
            exact this
          have h26 : Main[26] = 0 := by
            have : Main[13] = 0 ∨ Main[26] = 0 := by extract_from_and reader_cstrs
            simp [h_main13_1] at this
            exact this
          have h27 : Main[27] = 0 := by
            have : Main[13] = 0 ∨ Main[27] = 0 := by extract_from_and reader_cstrs
            simp [h_main13_1] at this
            exact this
          have h28 : Main[28] = 0 := by
            have : Main[13] = 0 ∨ Main[28] = 0 := by extract_from_and reader_cstrs
            simp [h_main13_1] at this
            exact this
          simp [h25, h26, h27, h28]
      
      -- Second part: Main[6] bound (register from JTypeReader)
      · simp [JTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
        calc Main[6] < 32 := by extract_from_and reader_cstrs
             _ < 65536 := by trivial

#print axioms u16_composition

end u16_composition

end UType