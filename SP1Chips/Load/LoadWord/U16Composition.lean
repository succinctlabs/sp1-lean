import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Operation.AddrAddOperation
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Load.LoadWord.Constraints

namespace Load

namespace LoadWord

section u16_composition

set_option maxHeartbeats 800000 in
theorem u16_composition
  (Main : Vector (Fin BB) 44)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (state_cstrs : (constraints Main).initialState s)
  : (constraints Main).U16CompProp
  := by
    -- First, expand toU16CompProp for all constraint types
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall,
          AddressOperation.constraints, AddrAddOperation.constraints, U16MSBOperation.constraints,
          CPUState.constraints, ITypeReader.constraints]

    simp [SP1Constraint.toProp, constraints, List.Forall, AddressOperation.constraints] at cstrs

    obtain ⟨addr_add_cstrs, addr_cstrs0, h_offset_bit_is_bool, addr_cstrs2, addr_cstrs3, msb_cstrs, cpu_cstrs, reader_cstrs, chip_cstrs⟩ := cstrs
    simp [sub_eq_zero] at *

    -- Extract boolean constraints for selectors
    have h_is_lw_bool : Main[42] = 0 ∨ Main[42] = 1 := by
      simp_all only
    have h_is_lwu_bool : Main[43] = 0 ∨ Main[43] = 1 := by
      simp_all only

    -- Extract that sum of selectors is 0 or 1 (is_real)
    have h_is_real_is_bool : Main[42] + Main[43] = 0 ∨ Main[42] + Main[43] = 1 := by
      simp_all only

    cases h_is_real_is_bool
    · -- Case: sum = 0 (no operation selected)
      rename_i h_not_real
      simp [h_not_real]

    -- Case: sum = 1 (exactly one operation selected)
    rename_i h_is_real

    -- Since each selector is 0 or 1 and their sum is 1, exactly one is 1
    have h_exactly_one : (Main[42] = 1 ∧ Main[43] = 0) ∨ (Main[42] = 0 ∧ Main[43] = 1) := by
      cases h_is_lw_bool <;> rename_i h42
      <;> cases h_is_lwu_bool <;> rename_i h43
      <;> simp [h42, h43] at h_is_real
      <;> aesop

    have h_op_a_not_x0 : Main[13] = 0 := by simp_all only

    -- Comes from the MSB operation spec, the proof is on another branch but I know it's true.
    have h_msb_is_bool : Main[41] = 0 ∨ Main[41] = 1 := by sorry

    -- Now do case analysis on which operation is selected
    cases h_exactly_one
    <;> rename_i h_selectors
    <;> obtain ⟨h_is_lw, h_is_lwu⟩ := h_selectors

    simp [h_is_lw, h_is_lwu, h_is_real]

    simp [CPUState.constraints, SP1Constraint.toProp, List.Forall] at cpu_cstrs
    simp [ITypeReader.constraints, SP1Constraint.toProp, List.Forall] at reader_cstrs
    simp [h_is_lw, h_is_lwu, h_is_real, Opcode.ofNat, ByteOpcode.ofNat, Nat.ble, Nat.beq] at chip_cstrs cpu_cstrs reader_cstrs

    have h_read_val_is_u64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by simp_all only [chip_cstrs]

    refine ⟨?_, ?_, ?_, ?_, ?_⟩

    · -- Goal 1: PC bounds
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

    · -- Goal 2: Output bounds (Main[39-40], 65535*Main[41]) and register bound (Main[6])
      refine ⟨?_, ?_⟩

      -- First part: output bounds
      · refine ⟨?_, ?_, ?_⟩

        · cases h_offset_bit_is_bool <;> rename_i h_offset_bit
          · simp [h_offset_bit] at chip_cstrs reader_cstrs
            have h_no_shift : Main[39] = Main[29] := by simp_all only
            rw [h_no_shift]
            have h_read_val_is_u64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by simp_all only [chip_cstrs]
            exact h_read_val_is_u64 0

          · simp [h_offset_bit] at chip_cstrs reader_cstrs
            have h_has_shift : Main[39] = Main[31] := by simp_all only
            rw [h_has_shift]
            exact h_read_val_is_u64 2

        · cases h_offset_bit_is_bool <;> rename_i h_offset_bit
          · simp [h_offset_bit] at chip_cstrs reader_cstrs
            have h_no_shift : Main[40] = Main[30] := by simp_all only
            rw [h_no_shift]
            have h_read_val_is_u64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by simp_all only [chip_cstrs]
            exact h_read_val_is_u64 1

          · simp [h_offset_bit] at chip_cstrs reader_cstrs
            have h_has_shift : Main[40] = Main[32] := by simp_all only
            rw [h_has_shift]
            exact h_read_val_is_u64 3

        · cases h_msb_is_bool <;> rename_i h_msb <;> rw [h_msb] <;> simp

      -- Second part: register bound Main[6] < 65536
      · calc Main[6] < 32 := by simp_all only
             _ < 65536 := by trivial

    · refine ⟨?_, by simp_all only⟩
      have : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
      exact Word.lt_cases_of_isU64 this

    · exact Word.lt_cases_of_isU64 h_read_val_is_u64

    · have addr_add_spec := AddrAddOperation.isU64_of_allHold_constraints _ _ _ (by rw [← h_is_real]; exact addr_add_cstrs)
      simp at addr_add_spec
      refine ⟨?_, by simp_all only [addr_add_spec], by simp_all only [addr_add_spec]⟩
      clear cpu_cstrs reader_cstrs

      cases h_offset_bit_is_bool
      · rename_i h_no_shift
        simp [h_no_shift]
        simp_all only [addr_add_spec]

      · rename_i h_has_shift
        simp [h_has_shift]
        simp [h_is_real, h_has_shift] at addr_cstrs3
        have h_is_u16 : Main[25] < 65536 := by show Main[25] < 65536; simp_all only [addr_add_spec]

        have h_mul4 : Main[25] % 4 = 0 := by
          simp [constraints, SP1Constraint.toStateProp, List.Forall, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, U16MSBOperation.constraints, h_is_real, h_is_lw, h_is_lwu, Opcode.ofNat, Nat.ble, Nat.beq] at state_cstrs
          sorry

        clear * - h_mul4 h_is_u16 addr_cstrs3
        have h_zero_or_ge4 : Main[25] = 0 ∨ Main[25] >= 4 :=
          by
            simp [Fin.mod_def] at h_mul4
            simp [Fin.lt_def]
            omega

        convert_to ((Main[25] - 4) * 1761607681) < 8192 at addr_cstrs3
        cases h_zero_or_ge4
        · rename_i h_zero
          rw [h_zero] at addr_cstrs3
          contradiction
        · rename_i h_ge4
          simp [Fin.lt_def, Fin.le_def] at h_is_u16 h_ge4
          omega

    -- this is the case where h_is_lwu. Let's focus on the h_is_lw case first; I think the h_is_lwu case is equivalent.
    sorry

#print axioms u16_composition

end u16_composition

end LoadWord

end Load
