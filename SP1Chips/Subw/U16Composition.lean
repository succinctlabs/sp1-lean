import SP1Operations.Operation.SubwOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.Subw.Constraints

namespace Subw

section u16_composition

set_option maxHeartbeats 800000 in
theorem u16_composition
  (Main : Vector (Fin BB) 32)
  (cstrs : (constraints Main).allHold)
  : (constraints Main).U16CompProp
  := by
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall, SubwOperation.constraints, CPUState.constraints, RTypeReader.constraints]
    simp [constraints] at cstrs
    obtain ⟨subw_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs

    -- First, handle U16MSBOperation constraints (trivial since no U16CompProp constraints)
    simp [U16MSBOperation.constraints, SP1Constraint.toU16CompProp, List.Forall]

    refine ⟨?_, ?_, ?_, ?_⟩
    -- First goal: PC bounds
    · intro h_is_real
      simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
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
      simp [SubwOperation.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at subw_op_cstrs
      -- Extract MSB constraint
      simp [U16MSBOperation.constraints, SP1Constraint.toProp, h_is_real] at subw_op_cstrs
      refine ⟨⟨by aesop, by aesop, ?_⟩, ?_⟩
      -- Prove Main[30] * 65535 < 65536
      · -- Main[30] is boolean (0 or 1) from MSB constraint
        repeat (rw [sub_eq_zero] at subw_op_cstrs)
        have h_msb_is_bool : Main[30] = 0 ∨ Main[30] = 1 := by extract_from_and subw_op_cstrs
        cases h_msb_is_bool <;> rename_i h <;> simp [h]
      -- Prove Main[6] < 65536
      · clear * - h_is_real reader_cstrs
        simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
        calc
          Main[6] < 32 := by extract_from_and reader_cstrs
          _       < 65536 := by trivial

    -- Third goal: op_b bounds
    · intro h_is_real
      simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
      have h_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
        extract_from_and reader_cstrs
      refine ⟨⟨h_is_u64 0, h_is_u64 1, h_is_u64 2, h_is_u64 3⟩, ?_⟩
      extract_from_and reader_cstrs

    -- Fourth goal: op_c bounds
    · intro h_is_real
      have reader_cstrs' := reader_cstrs
      simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs'
      have h_is_u64 : Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
        extract_from_and reader_cstrs'
      refine ⟨⟨h_is_u64 0, h_is_u64 1, h_is_u64 2, h_is_u64 3⟩, ?_⟩
      extract_from_and reader_cstrs'

#print axioms u16_composition

end u16_composition

end Subw
