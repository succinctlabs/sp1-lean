import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftLeft.Constraints

namespace ShiftLeft

section u16_composition

set_option maxHeartbeats 800000 in
theorem u16_composition
  (Main : Vector (Fin BB) 65)
  (cstrs : (constraints Main).allHold)
  : (constraints Main).U16CompProp
  := by
    -- First, expand definitions to see what we need to prove
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall,
          U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints]

    -- Decompose the constraints hypothesis
    simp [constraints, SP1Constraint.toProp, List.Forall] at cstrs
    obtain ⟨u16msb_cstrs, cpu_cstrs, alu_cstrs, chip_cstrs⟩ := cstrs

    -- First, establish that the sum of selectors is either 0 or 1
    have h_sum_bool : Main[62] + Main[63] = 0 ∨ Main[62] + Main[63] = 1 := by
      simp [SP1Constraint.toProp, sub_eq_zero] at chip_cstrs
      extract_from_and chip_cstrs

    cases h_sum_bool
    · -- Case: sum = 0 (no operation selected)
      rename_i h_not_real
      simp [h_not_real]
      -- When sum = 0, the only remaining goal is about Main[31]
      intro h_imm_c
      -- Extract that imm_c = 0 when is_real = 0
      simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_not_real, List.Forall] at alu_cstrs
      have h_imm_no : Main[31] = 0 := by extract_from_and alu_cstrs
      contradiction

    -- Case: sum = 1 (operation is real)
    rename_i h_sum_one

    -- Extract boolean constraints for selectors
    have h_main62_bool : Main[62] = 0 ∨ Main[62] = 1 := by
      simp [SP1Constraint.toProp, sub_eq_zero] at chip_cstrs
      extract_from_and chip_cstrs
    have h_main63_bool : Main[63] = 0 ∨ Main[63] = 1 := by
      simp [SP1Constraint.toProp, sub_eq_zero] at chip_cstrs
      extract_from_and chip_cstrs

    -- Since sum = 1 and each selector is 0 or 1, exactly one is 1
    have h_exactly_one : (Main[62] = 1 ∧ Main[63] = 0) ∨ (Main[62] = 0 ∧ Main[63] = 1) := by
      cases h_main62_bool <;> rename_i h62
      <;> cases h_main63_bool <;> rename_i h63
      <;> simp [h62, h63] at h_sum_one
      <;> aesop

    -- Also prove Main[31] is boolean
    have h_imm_c_bool : Main[31] = 0 ∨ Main[31] = 1 := by
      simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_sum_one, List.Forall] at alu_cstrs
      simp_all only

    -- Now prove each of the four conjuncts
    refine ⟨?_, ?_, ?_, ?_⟩

    -- Goal 1: PC bounds
    · intro h_is_real
      simp [h_sum_one] at h_is_real
      -- PC bounds should be in alu_cstrs
      simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_sum_one, List.Forall] at alu_cstrs
      refine ⟨?_, by simp_all only, by simp_all only⟩
      -- Prove PC + 4 ≤ 65536
      have h_pc_nat_mul4 : Main[3].val % 4 = 0 := by
        have h_pc_mul4 : Main[3] % 4 = 0 := by simp_all only
        have : (Main[3] % 4).val = Main[3].val % 4 := Fin.mod_val Main[3] 4
        rw [h_pc_mul4] at this
        simp at this
        exact this.symm
      have h_pc_nat_bound : Main[3].val < 65536 := by show Main[3] < 65536; simp_all only
      have h_no_overflow : Main[3].val + 4 < BB := by
        calc Main[3].val + 4 < 65536 + 4 := by omega
        _ = 65540 := by norm_num
        _ < BB := by norm_num
      rw [Fin.le_iff_val_le_val]
      rw [Fin.val_add_eq_of_add_lt h_no_overflow]
      omega

    -- Goal 2: Output bounds (Main[32-35] and Main[6])
    · intro h_is_real
      simp [h_sum_one] at h_is_real
      refine ⟨?_, ?_⟩
      -- First: Main[32-35] bounds
      · -- These come from the output of the shift operation
        -- Need to use case analysis on the selector
        cases h_exactly_one
        <;> rename_i h_sel
        <;> obtain ⟨h_62, h_63⟩ := h_sel
        <;> simp [h_62, h_63] at chip_cstrs
        -- The bounds for Main[32-35] should be in chip_cstrs
        -- Look for Main[32] - Main[57] = 0, etc.
        all_goals {
          -- TODO: this comes from the spec of ShiftLeft, which we don't have yet
          sorry
        }
      -- Second: Main[6] bound (register)
      · simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_sum_one, List.Forall] at alu_cstrs
        calc Main[6] < 32 := by simp_all only
             _ < 65536 := by trivial

    -- Goal 3: op_b bounds (Main[15-18] and Main[14])
    · intro h_is_real
      simp [h_sum_one] at h_is_real
      -- Need case analysis on selector to expand the opcode in ALUTypeReader
      cases h_exactly_one
      <;> rename_i h_sel
      <;> obtain ⟨h_62, h_63⟩ := h_sel
      <;> simp [h_62, h_63] at alu_cstrs
      -- Now simp with the concrete selector values to expand the opcode
      all_goals {
        simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_sum_one, h_62, h_63, Opcode.ofNat, Nat.ble, Nat.beq, List.Forall] at alu_cstrs
        refine ⟨?_, ?_⟩
        · have h_op_b_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
          exact Word.lt_cases_of_isU64 h_op_b_u64
        · -- Need to case on Main[31] to access the register bound
          cases h_imm_c_bool <;> rename_i h31
          <;> simp [h31] at alu_cstrs
          <;> calc Main[14] < 32 := by simp_all only
                   _ < 65536 := by trivial
      }

    -- Goal 4: op_c bounds (conditional on Main[31])
    · intro h_imm_c_ne
      -- The condition ¬(is_real - imm_c = 0) with is_real = 1 means imm_c ≠ 1
      -- So we need to handle the case where the selector activates the opcode
      -- Need case analysis on the selector to know which opcode we're dealing with
      cases h_exactly_one
      <;> rename_i h_sel
      <;> obtain ⟨h_62, h_63⟩ := h_sel
      <;> simp [h_62, h_63] at alu_cstrs
      -- Now simp with the concrete selector values to expand the opcode
      all_goals {
        simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_sum_one, h_62, h_63, Opcode.ofNat, Nat.ble, Nat.beq, List.Forall] at alu_cstrs
        -- The condition with concrete values
        simp [h_62, h_63, h_sum_one] at h_imm_c_ne
        -- For shift operations, imm_c controls whether op_c is used
        -- The condition 1 - Main[31] ≠ 0 means Main[31] ≠ 1, so Main[31] = 0
        have h_imm_c : Main[31] = 0 := by
          cases h_imm_c_bool <;> rename_i h31
          · exact h31
          · simp [h31] at h_imm_c_ne
        simp [h_imm_c] at alu_cstrs
        refine ⟨?_, ?_⟩
        · have h_op_c_u64 : Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := by simp_all only
          exact Word.lt_cases_of_isU64 h_op_c_u64
        · -- Main[21] bound
          simp_all only
      }

#print axioms u16_composition

end u16_composition

end ShiftLeft
