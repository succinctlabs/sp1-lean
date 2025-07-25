import SP1Foundations
import SP1Operations
import LeanRV64IM.RiscvInstsEnd

import SP1Chips.Addw.Constraints

open LeanRV64IM.Functions
open BitVec

namespace Addw

variable
  (Main : Vector (Fin BB) 37)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[35] = 1)

def spec_addw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.ADDW
  pure ()

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    simp
    show Main[6] < 32

    have alu_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [ALUTypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at alu_cstrs

    exact alu_cstrs.1.2.1

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp
    show Main[14] < 32

    have alu_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [ALUTypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at alu_cstrs

    exact alu_cstrs.1.1.1

def sp1_op_c : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[21] ?_
    simp
    show Main[21] < 32

    have alu_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [ALUTypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at alu_cstrs

    exact alu_cstrs.1.1.2.1

def sp1_addw : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  -- TODO(gzgz): we can obtain this from the constraint compiler
  -- This comes from the Interaction.state in CPUState
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  SailState.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535])

theorem correct_addw
  (state_cstrs : (constraints Main).initialState s)
  (h_is_addw : Main[31] = 0) : -- PM: WHY DO I NEED THIS?
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_addw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addw Main cstrs h_is_real).run s
  := by
    -- Obtain and simplify state and pure constraints
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddwOperation.constraints, CPUState.constraints, ALUTypeReader.constraints, U16MSBOperation.constraints, h_is_real] at state_cstrs
    obtain ⟨read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    simp [constraints] at cstrs
    obtain ⟨addw_op_cstrs, cpu_cstrs, alu_cstrs, _, _⟩ := cstrs
    apply AddwOperation.correct (h_is_real := h_is_real) at addw_op_cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨ trusted_instr_prop, _, _, _, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _ ⟩ := alu_cstrs
    simp [Opcode.ofNat, Nat.ble] at *
    simp_all
    obtain ⟨ _, _, is_U64_c ⟩ := is_U64_c
    specialize addw_op_cstrs is_U64_b is_U64_c
    obtain ⟨ is_U32_val, is_addw, is_msb ⟩ := addw_op_cstrs
    simp_all

    -- Now the monadic manipulation
    simp [spec_addw, sp1_addw, execute, execute_RTYPEW']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [exec_RTYPEW_pure_bv_to_w _ _ _ (by omega) (by omega)]
    simp [execute_RTYPEW_pure_w]
    rw [← is_addw] at is_msb
    simp [sign_extend, Sail.BitVec.signExtend]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [Word.toBitVec64, Word.toNat]
      rw [← is_addw]; congr
      rw [Word.hw_sign_extend_32_to_64_msb _ _ is_U32_val]
      simp [Word.toBitVec64, Word.toNat]

end Addw
