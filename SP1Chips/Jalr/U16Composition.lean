import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Jalr.Constraints

namespace Jalr

section u16_composition

set_option maxHeartbeats 400000 in
theorem u16_composition
  (Main : Vector (Fin BB) 38)
  (cstrs : (constraints Main).allHold)
  : (constraints Main).U16CompProp
  := by
    -- Expand all definitions until no more *.constraints remain
    simp [SP1Constraint.toU16CompProp, constraints, List.Forall,
          AddOperation.constraints, CPUState.constraints, ITypeReader.constraints]

    -- Decompose the constraints hypothesis
    simp [constraints, SP1Constraint.toProp, List.Forall, sub_eq_zero] at cstrs

    -- First, handle the is_real = 0 case
    have h_main29 : Main[29] = 0 ∨ Main[29] = 1 := by
      simp_all only

    cases h_main29
    · rename_i h_not_real
      -- When Main[29] = 0, all implications are trivially true
      simp [h_not_real]

    rename_i h_is_real
    -- When Main[29] = 1, we need to prove the bounds
    simp [h_is_real] at *

    -- Extract the constraints from cstrs
    obtain ⟨add_cstrs, cpu_cstrs, reader_cstrs, inc_pc_cstrs, chip_cstrs⟩ := cstrs

    -- The goal has three parts
    refine ⟨?_, ?_, ?_⟩

    -- First goal: bounds on Main[30], Main[31], Main[32] (output of first AddOperation)
    · -- Main[29] = 1, so add_cstrs are the constraints with is_real = 1
      -- Use AddOperation.isU64_of_allHold_constraints to get bounds
      have h_output_u64 : Word.isU64 #v[Main[30], Main[31], Main[32], Main[33]] :=
        AddOperation.isU64_of_allHold_constraints _ _ _ add_cstrs
      have h_bounds := Word.lt_cases_of_isU64 h_output_u64
      simp at h_bounds
      refine ⟨?_, by extract_from_and h_bounds, by extract_from_and h_bounds⟩
      · show Main[30].val ≤ 65536
        have : Main[30].val < 65536 := by simp_all only
        linarith

    -- Second goal: bounds on Main[34-37] and Main[6]
    · refine ⟨?_, ?_⟩

      -- First part: bounds on Main[34-37]
      · -- Main[34-37] come from the second AddOperation with is_real = 1 - Main[13]
        -- We need to handle two cases based on Main[13]
        have h_main13 : Main[13] = 0 ∨ Main[13] = 1 := by
          simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat,
                Nat.ble, Nat.beq] at reader_cstrs
          extract_from_and reader_cstrs
        cases h_main13 with
        | inl h_main13_0 =>
          -- When Main[13] = 0, the second AddOperation has is_real = 1
          simp [h_main13_0] at inc_pc_cstrs
          have h_output2_u64 : Word.isU64 #v[Main[34], Main[35], Main[36], Main[37]] :=
            AddOperation.isU64_of_allHold_constraints _ _ _ inc_pc_cstrs
          exact Word.lt_cases_of_isU64 h_output2_u64
        | inr h_main13_1 =>
          -- When Main[13] = 1, we need to prove Main[34-37] = 0
          simp [h_main13_1] at chip_cstrs
          have h37 : Main[37] = 0 := by simp_all only [chip_cstrs]
          obtain ⟨h34, h35, h36⟩ : Main[34] = 0 ∧ Main[35] = 0 ∧ Main[36] = 0 := by
            split_ands <;> simp_all only
          simp [h34, h35, h36, h37]

      -- Second part: bound on Main[6] (op_a register)
      · simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat,
              Nat.ble, Nat.beq] at reader_cstrs
        calc Main[6] < 32 := by extract_from_and reader_cstrs
             _ < 65536 := by trivial

    -- Third goal: bounds on Main[15-18] and Main[14]
    · refine ⟨?_, ?_⟩

      -- First part: bounds on Main[15-18] (op_b memory value)
      · simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat,
              Nat.ble, Nat.beq] at reader_cstrs
        have h_op_b_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
          simp_all only
        exact Word.lt_cases_of_isU64 h_op_b_u64

      -- Second part: bound on Main[14] (op_b register)
      · simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat,
              Nat.ble, Nat.beq] at reader_cstrs
        calc Main[14] < 32 := by extract_from_and reader_cstrs
             _ < 65536 := by trivial

#print axioms u16_composition

end u16_composition

end Jalr
