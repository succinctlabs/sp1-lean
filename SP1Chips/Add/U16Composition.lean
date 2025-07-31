import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.Add.Constraints

namespace Add

section u16_composition

set_option maxHeartbeats 400000 in
theorem u16_composition 
  (Main : Vector (Fin BB) 33)
  (cstrs : (constraints Main).allHold)
  : (constraints Main).U16CompProp
  := by
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall, AddOperation.constraints, CPUState.constraints, RTypeReader.constraints]
    simp [constraints] at cstrs
    obtain ⟨add_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs

    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h_is_real
      simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
      refine ⟨?_, by extract_from_and reader_cstrs, by extract_from_and reader_cstrs⟩
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
    · intro h_is_real
      simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at add_op_cstrs
      refine ⟨⟨by aesop, by aesop, by aesop, by aesop⟩, ?_⟩
      clear * - h_is_real reader_cstrs
      simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
      calc 
        Main[6] < 32 := by extract_from_and reader_cstrs
        _       < 65536 := by trivial
    · intro h_is_real
      simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
      have h_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
        extract_from_and reader_cstrs
      refine ⟨⟨h_is_u64 0, h_is_u64 1, h_is_u64 2, h_is_u64 3⟩, ?_⟩
      extract_from_and reader_cstrs
    · intro h_is_real
      have reader_cstrs' := reader_cstrs
      simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs'
      have h_is_u64 : Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
        extract_from_and reader_cstrs'
      refine ⟨⟨h_is_u64 0, h_is_u64 1, h_is_u64 2, h_is_u64 3⟩, ?_⟩
      extract_from_and reader_cstrs'

#print axioms u16_composition

end u16_composition

end Add
