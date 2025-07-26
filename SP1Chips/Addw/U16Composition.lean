import SP1Operations.Operation.AddwOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

import SP1Chips.Addw.Constraints

namespace Addw

section u16_composition

variable
  (Main : Vector (Fin BB) 37)
  (cstrs : (constraints Main).allHold)

set_option maxHeartbeats 800000 in
def u16_composition 
  : (constraints Main).U16CompProp
  := by
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall, AddwOperation.constraints, CPUState.constraints, ALUTypeReader.constraints]
    simp [constraints] at cstrs
    obtain ⟨addw_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs

    -- First, handle U16MSBOperation constraints (trivial since no U16CompProp constraints)
    simp [U16MSBOperation.constraints, SP1Constraint.toU16CompProp, List.Forall]

    refine ⟨?_, ?_, ?_, ?_⟩
    -- First goal: PC bounds
    · intro h_is_real
      simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
      refine ⟨?_, by extract_from_and reader_cstrs, by extract_from_and reader_cstrs⟩
      -- Prove Main[3] + 4 ≤ 65536
      have h_pc_nat_mul4 : Main[3].val % 4 = 0 := by
        have h_pc_mul4 : Main[3] % 4 = 0 := by extract_from_and reader_cstrs
        -- Convert from Fin modulo to Nat modulo
        have : (Main[3] % 4).val = Main[3].val % 4 := Fin.mod_val Main[3] 4
        rw [h_pc_mul4] at this
        simp at this
        exact this.symm
      have h_pc_nat_bound : Main[3].val < 65536 := by extract_from_and reader_cstrs
      clear * - h_pc_nat_mul4 h_pc_nat_bound
      -- Convert Fin BB inequality to Nat inequality
      have h_no_overflow : Main[3].val + 4 < BB := by
        calc Main[3].val + 4 < 65536 + 4 := by omega
        _ = 65540 := by norm_num
        _ < BB := by norm_num
      rw [Fin.le_iff_val_le_val]
      rw [Fin.val_add_eq_of_add_lt h_no_overflow]
      omega

    -- Second goal: Output bounds (including MSB)
    · intro h_is_real
      simp [AddwOperation.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at addw_op_cstrs
      -- Extract MSB constraint
      simp [U16MSBOperation.constraints, SP1Constraint.toProp, h_is_real] at addw_op_cstrs
      refine ⟨⟨by aesop, by aesop, ?_⟩, ?_⟩
      -- Prove Main[34] * 65535 < 65536
      · -- Main[34] is boolean (0 or 1) from MSB constraint
        repeat (rw [sub_eq_zero] at addw_op_cstrs)
        have h_msb_is_bool : Main[34] = 0 ∨ Main[34] = 1 := by extract_from_and addw_op_cstrs
        cases h_msb_is_bool <;> rename_i h <;> simp [h]
      -- Prove Main[6] < 65536
      · clear * - h_is_real reader_cstrs
        simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
        calc 
          Main[6] < 32 := by extract_from_and reader_cstrs
          _       < 65536 := by trivial

    -- Third goal: Input bounds (op_b)
    · intro h_is_real
      simp [ALUTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
      have h_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
        extract_from_and reader_cstrs
      refine ⟨⟨h_is_u64 0, h_is_u64 1, h_is_u64 2, h_is_u64 3⟩, ?_⟩
      extract_from_and reader_cstrs

    -- Fourth goal: Input bounds (op_c) - only when is_real ≠ imm_c
    · intro h_not_eq
      -- First, simplify reader_cstrs
      simp [ALUTypeReader.constraints, SP1Constraint.toProp, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs

      -- Extract Word.isU64 for Main[25-28]
      have h_word_u64 : Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := by
        have h : ¬Main[35] - Main[31] = 0 → Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := by
          extract_from_and reader_cstrs
        exact h h_not_eq

      refine ⟨⟨h_word_u64 0, h_word_u64 1, h_word_u64 2, h_word_u64 3⟩, ?_⟩

      -- Now prove Main[21] < 65536 by cases on Main[35]
      rw [sub_eq_zero] at rest
      have h_main35_bool : Main[35] = 0 ∨ Main[35] = 1 := by extract_from_and rest

      cases h_main35_bool with
      | inl h_main35_eq_0 =>
        -- Case 1: Main[35] = 0, so Main[31] = 1 (from h_not_eq)
        -- When imm_c = 1, we have Main[25] = Main[21]
        simp [h_main35_eq_0] at reader_cstrs
        have h_eq : Main[25] = Main[21] := by
          have h : Main[31] = 0 ∨ Main[25] - Main[21] = 0 := by
            extract_from_and reader_cstrs
          cases h with
          | inl h => 
            -- Main[31] = 0 contradicts Main[31] = 1
            exfalso
            have : Main[31] ≠ 0 := by
              intro h_eq; rw [h_main35_eq_0, h_eq] at h_not_eq; simp at h_not_eq
            exact this h
          | inr h => exact sub_eq_zero.mp h
        rw [← h_eq]; exact h_word_u64 0

      | inr h_main35_eq_1 =>
        -- Case 2: Main[35] = 1, so Main[31] = 0 (from h_not_eq)
        -- When is_real = 1, we directly get Main[21] < 65536 from reader_cstrs
        have h_main35_ne_0 : ¬Main[35] = 0 := by rw [h_main35_eq_1]; simp
        simp [h_main35_ne_0] at reader_cstrs
        extract_from_and reader_cstrs

end u16_composition

end Addw
