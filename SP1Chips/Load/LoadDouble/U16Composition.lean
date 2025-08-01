import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Operation.AddrAddOperation
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Load.LoadDouble.Constraints

namespace Load

namespace LoadDouble

section u16_composition

set_option maxHeartbeats 800000 in
theorem u16_composition
  (Main : Vector (Fin BB) 39)
  (cstrs : (constraints Main).allHold)
  : (constraints Main).U16CompProp
  := by
    -- First, expand toU16CompProp for all constraint types
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall,
          AddressOperation.constraints, AddrAddOperation.constraints, U16MSBOperation.constraints,
          CPUState.constraints, ITypeReader.constraints]

    simp [SP1Constraint.toProp, constraints, List.Forall, AddressOperation.constraints] at cstrs

    obtain ⟨addr_add_cstrs, addr_cstr0, add_cstr1, addr_cstr2, cpu_cstrs, reader_cstrs, chip_cstrs⟩ := cstrs
    simp [sub_eq_zero] at *

    have h_is_real_is_bool : Main[38] = 0 ∨ Main[38] = 1 := by simp_all only

    cases h_is_real_is_bool
    · rename_i h_not_real
      simp [h_not_real]

    rename_i h_is_real
    simp [h_is_real]
    simp [h_is_real] at chip_cstrs

    refine ⟨?_, ?_, ?_, ?_, ?_⟩

    · -- Goal 1: PC bounds
      simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
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

    · -- Goal 2: Output bounds (Main[29-32]) and register bound (Main[6])
      refine ⟨?_, ?_⟩
      -- First: Main[29-32] bounds from chip_cstrs
      · have h_output_u64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by
          extract_from_and chip_cstrs
        exact Word.lt_cases_of_isU64 h_output_u64
      -- Second: Main[6] bound (register)
      · simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
        calc Main[6] < 32 := by extract_from_and reader_cstrs
             _ < 65536 := by trivial

    · -- Goal 3: op_b bounds (Main[15-18]) and register bound (Main[14])
      refine ⟨?_, ?_⟩
      -- First: Main[15-18] bounds (op_b memory value)
      · simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
        have h_op_b_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
          simp_all only
        exact Word.lt_cases_of_isU64 h_op_b_u64
      -- Second: Main[14] bound (op_b register)
      · simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
        calc Main[14] < 32 := by extract_from_and reader_cstrs
             _ < 65536 := by trivial

    · -- Goal 4: Memory output bounds (Main[29-32])
      -- This is the same as what we already proved from chip_cstrs
      have h_output_u64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by
        extract_from_and chip_cstrs
      exact Word.lt_cases_of_isU64 h_output_u64

    · -- Goal 5: Address bounds (Main[25-27])
      -- Use the lemma from AddrAddOperation
      have h_addr_bounds := AddrAddOperation.isU64_of_allHold_constraints
        #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[21], Main[22], Main[23], Main[24]]
        { value := #v[Main[25], Main[26], Main[27]] }
        (by rw [← h_is_real]; exact addr_add_cstrs)
      exact h_addr_bounds

#print axioms u16_composition

end u16_composition

end LoadDouble

end Load
