import SP1Operations.Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Bitwise.Constraints

namespace Bitwise

section u16_composition

set_option maxHeartbeats 800000 in
theorem u16_composition
  (Main : Vector (Fin BB) 52)
  (cstrs : (constraints Main).allHold)
  : (constraints Main).U16CompProp
  := by
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall, BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints, BitwiseOperation.constraints, CPUState.constraints, ALUTypeReader.constraints]

    simp [List.Forall, constraints, BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints] at cstrs

    obtain ⟨bitwise_cstrs, what_is_this, cpu_cstrs, alu_cstrs, chip_cstrs⟩ := cstrs
    simp [BitwiseOperation.constraints, CPUState.constraints, ALUTypeReader.constraints, List.Forall, SP1Constraint.toProp, sub_eq_zero] at *
    have h_is_xor_is_bool : Main[48] = 0 ∨ Main[48] = 1 := by simp_all only
    have h_is_or_is_bool : Main[49] = 0 ∨ Main[49] = 1 := by simp_all only
    have h_is_and_is_bool : Main[50] = 0 ∨ Main[50] = 1 := by simp_all only

    have : (Main[48] + Main[49] + Main[50] = 0) ∨ (Main[48] + Main[49] + Main[50] = 1) := by simp_all only
    cases this
    · rename_i h_not_real 
      simp [h_not_real] at *
      have : Main[31] = 0 := by simp_all only
      simp [this]

    rename_i h_is_real

    -- Since each selector is 0 or 1 and their sum is 1, exactly one is 1
    have h_exactly_one : (Main[48] = 1 ∧ Main[49] = 0 ∧ Main[50] = 0) ∨ 
                         (Main[48] = 0 ∧ Main[49] = 1 ∧ Main[50] = 0) ∨ 
                         (Main[48] = 0 ∧ Main[49] = 0 ∧ Main[50] = 1) := by
      clear * - h_is_xor_is_bool h_is_or_is_bool h_is_and_is_bool h_is_real
      cases h_is_xor_is_bool <;> rename_i h48
      <;> cases h_is_or_is_bool <;> rename_i h49
      <;> cases h_is_and_is_bool <;> rename_i h50
      <;> simp [h48, h49, h50] at h_is_real
      <;> aesop

    -- Now do case analysis on h_exactly_one
    rcases h_exactly_one with h_everything | (h_everything | h_everything)

    -- Now apply the same proof to all three cases
    all_goals {
      obtain ⟨h_48, h_49, h_50⟩ := h_everything
      simp [h_48, h_49, h_50, ByteOpcode.ofNat, Opcode.ofNat, Nat.ble, Nat.beq, sub_eq_zero] at bitwise_cstrs cpu_cstrs alu_cstrs chip_cstrs
      simp [h_is_real]

      -- Now apply the same proof for all cases
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine ⟨?_, by simp_all only, by simp_all only⟩
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

      · have h_op_a_valid_addr : Main[6] < 65536 :=
          calc
            Main[6] < 32 := by simp_all only
            _       < 65536 := by simp
        refine ⟨?_, h_op_a_valid_addr⟩

        clear * - bitwise_cstrs
        -- simp_all only not working?
        have h_40 : Main[40].val < 256 := by show Main[40] < 256; extract_from_and bitwise_cstrs
        have h_41 : Main[41].val < 256 := by extract_from_and bitwise_cstrs
        have h_42 : Main[42].val < 256 := by extract_from_and bitwise_cstrs
        have h_43 : Main[43].val < 256 := by extract_from_and bitwise_cstrs
        have h_44 : Main[44].val < 256 := by extract_from_and bitwise_cstrs
        have h_45 : Main[45].val < 256 := by extract_from_and bitwise_cstrs
        have h_46 : Main[46].val < 256 := by extract_from_and bitwise_cstrs
        have h_47 : Main[47].val < 256 := by extract_from_and bitwise_cstrs
        clear bitwise_cstrs

        split_ands
        all_goals
          simp [Fin.add_def, Fin.mul_def, Fin.lt_iff_val_lt_val]
          rw [Nat.mod_eq_of_lt (by linarith)]
          linarith

      · refine ⟨?_, by simp_all only⟩
        have h_op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
        clear * - h_op_b_is_u64
        exact Word.lt_cases_of_isU64 h_op_b_is_u64

      · intro h_imm_c
        simp [h_imm_c] at alu_cstrs
        clear * - h_imm_c alu_cstrs
        refine ⟨?_, by simp_all only⟩

        have h_op_c_is_u64 : Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := by simp_all only
        exact Word.lt_cases_of_isU64 h_op_c_is_u64
    }

#print axioms u16_composition

end u16_composition

end Bitwise
