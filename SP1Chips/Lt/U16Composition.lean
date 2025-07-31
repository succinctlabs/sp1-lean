import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Lt.Constraints

namespace Lt

section u16_composition

set_option maxHeartbeats 800000 in
theorem u16_composition
  (Main : Vector (Fin BB) 45)
  (cstrs : (constraints Main).allHold)
  : (constraints Main).U16CompProp
  := by
    -- First, just expand and see what we're dealing with
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall,
          LtOperationSigned.constraints, CPUState.constraints, ALUTypeReader.constraints]

    -- Expand U16MSBOperation and LtOperationUnsigned constraints
    simp [U16MSBOperation.constraints, LtOperationUnsigned.constraints, U16CompareOperation.constraints, SP1Constraint.toU16CompProp, List.Forall]

    -- Decompose the constraints hypothesis
    simp [constraints] at cstrs
    obtain ⟨lt_cstrs, cpu_cstrs, alu_cstrs, chip_cstrs⟩ := cstrs

    -- First, establish that the sum of selectors is either 0 or 1
    have h_sum_bool : Main[32] + Main[33] = 0 ∨ Main[32] + Main[33] = 1 := by
      simp [List.Forall, SP1Constraint.toProp, sub_eq_zero] at chip_cstrs
      simp_all only

    cases h_sum_bool
    · -- Case: sum = 0 (no operation selected)
      rename_i h_not_real
      simp [h_not_real]
      -- When sum = 0, the only remaining goal is about Main[31]
      -- which is the imm_c field determining conditional op_c bounds
      intro h_imm_c
      -- We need to prove bounds for Main[25-28] and Main[21]
      -- The key insight is that the toU16CompProp for memory constraints
      -- requires is_real - imm_c ≠ 0, which is 0 - Main[31] ≠ 0, i.e., Main[31] ≠ 0
      -- So when Main[31] ≠ 0, we have memory constraints even when is_real = 0
      simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_not_real, List.Forall] at alu_cstrs
      -- The conditional memory access for op_c happens when is_real - imm_c ≠ 0
      -- With is_real = 0 and imm_c ≠ 0, we get 0 - Main[31] ≠ 0
      have h_imm_no : Main[31] = 0 := by extract_from_and alu_cstrs
      contradiction

    -- Case: sum = 1 (exactly one operation selected)
    rename_i h_sum_one

    have h_imm_c_is_bool : Main[31] = 0 ∨ Main[31] = 1 := by
      simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_sum_one, List.Forall] at alu_cstrs
      simp_all only [alu_cstrs]

    -- Since each selector is 0 or 1 and their sum is 1, exactly one is 1
    have h_is_slt_is_bool : Main[32] = 0 ∨ Main[32] = 1 := by
      simp [List.Forall, SP1Constraint.toProp, sub_eq_zero] at chip_cstrs
      simp_all only
    have h_is_sltu_is_bool : Main[33] = 0 ∨ Main[33] = 1 := by  
      simp [List.Forall, SP1Constraint.toProp, sub_eq_zero] at chip_cstrs
      simp_all only
      
    have h_exactly_one : (Main[32] = 1 ∧ Main[33] = 0) ∨ (Main[32] = 0 ∧ Main[33] = 1) := by
      clear * - h_is_slt_is_bool h_is_sltu_is_bool h_sum_one
      cases h_is_slt_is_bool <;> rename_i h32
      <;> cases h_is_sltu_is_bool <;> rename_i h33
      <;> simp [h32, h33] at h_sum_one
      <;> aesop

    -- The goal has four parts
    refine ⟨?_, ?_, ?_, ?_⟩

    -- First goal: PC bounds
    · intro h_is_real
      -- Since sum = 1, we know h_is_real is trivially true
      simp [h_sum_one] at h_is_real

      -- Extract PC bounds from alu_cstrs
      simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_sum_one, List.Forall] at alu_cstrs
      simp [Opcode.ofNat] at alu_cstrs
      -- The PC bounds should be in alu_cstrs since ALUTypeReader contains program memory access
      refine ⟨?_, by simp_all only, by simp_all only⟩

      -- Prove Main[3] + 4 ≤ 65536
      have h_pc_nat_mul4 : Main[3].val % 4 = 0 := by
        have h_pc_mul4 : Main[3] % 4 = 0 := by simp_all only
        -- Convert from Fin modulo to Nat modulo
        have : (Main[3] % 4).val = Main[3].val % 4 := Fin.mod_val Main[3] 4
        rw [h_pc_mul4] at this
        simp at this
        exact this.symm
      have h_pc_nat_bound : Main[3].val < 65536 := by show Main[3] < 65536; simp_all only
      clear * - h_pc_nat_mul4 h_pc_nat_bound
      -- Convert Fin BB inequality to Nat inequality
      have h_no_overflow : Main[3].val + 4 < BB := by
        calc Main[3].val + 4 < 65536 + 4 := by omega
        _ = 65540 := by norm_num
        _ < BB := by norm_num
      rw [Fin.le_iff_val_le_val]
      rw [Fin.val_add_eq_of_add_lt h_no_overflow]
      omega

    -- Second goal: Main[35] and Main[6] bounds
    · intro h_is_real
      simp [h_sum_one] at h_is_real

      -- Extract bounds from alu_cstrs
      simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_sum_one, List.Forall] at alu_cstrs
      simp [Opcode.ofNat, Nat.ble, Nat.beq] at alu_cstrs

      refine ⟨?_, ?_⟩
      · -- Prove Main[35] < 65536
        -- Main[35] is the output (bit) which should be bounded
        clear * - lt_cstrs
        simp [List.Forall, SP1Constraint.toProp, LtOperationSigned.constraints, LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints, sub_eq_zero] at lt_cstrs
        have : Main[35] = 0 ∨ Main[35] = 1 := by simp_all only
        cases this <;> rename_i h_35 <;> simp [h_35]
      · -- Prove Main[6] < 65536
        -- Main[6] is op_a (register index)
        calc Main[6] < 32 := by simp_all only
             _ < 65536 := by trivial

    -- Third goal: op_b memory bounds
    -- Since we rely on constraints from `ALUTypeReader` and usually it needs to
    -- know the exact value of the Opcode to expand out all the constraints, we
    -- should have the concrete values of `h_is_slt` and `h_is_sltu` so that we
    -- can calcualte Opcode and expand out the full constraints.
    · cases h_exactly_one
      <;> rename_i h_exactly_one
      <;> obtain ⟨h_is_slt, h_is_sltu⟩ := h_exactly_one
      <;> simp [h_is_slt, h_is_sltu, h_sum_one]
      all_goals 
        simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_sum_one, List.Forall] at alu_cstrs
        simp [h_is_slt, h_is_sltu, Opcode.ofNat, Nat.ble, Nat.beq] at alu_cstrs

        refine ⟨?_, ?_⟩
        · -- Prove Main[15-18] < 65536 (op_b memory value)
          have h_op_b_memory : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
            simp_all only
          exact Word.lt_cases_of_isU64 h_op_b_memory
        · -- Prove Main[14] < 65536 (op_b register)
          cases h_imm_c_is_bool <;> rename_i h_imm_c
          all_goals
            simp [h_imm_c] at alu_cstrs
            simp_all only [alu_cstrs]

    -- Third goal: op_c memory bounds
    · cases h_exactly_one
      <;> rename_i h_exactly_one
      <;> obtain ⟨h_is_slt, h_is_sltu⟩ := h_exactly_one
      <;> simp [h_is_slt, h_is_sltu, h_sum_one, sub_eq_zero]
      all_goals
        intro h_imm_c
        simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_sum_one, List.Forall] at alu_cstrs
        simp [h_is_slt, h_is_sltu, Opcode.ofNat, Nat.ble, Nat.beq, sub_eq_zero, h_imm_c] at alu_cstrs
        have h_op_c_memory : Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := by
          simp_all only
        refine ⟨Word.lt_cases_of_isU64 h_op_c_memory, ?_⟩
        simp_all only [alu_cstrs]

#print axioms u16_composition

end u16_composition

end Lt
