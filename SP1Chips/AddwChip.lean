import SP1Operations.Operation.AddwOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Addw.Constraints

open LeanRV64D.Functions
open BitVec

namespace Addw

variable
  (Main : Vector (Fin KB) 37)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[36] = 1)
  (h_is_addw : Main[31] = 0)

def spec_addw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.ADDW
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21]

def sp1_addw : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[33], Main[34], Main[35] * 65535, Main[35] * 65535])

set_option maxHeartbeats 1000000 in
theorem correct_addw
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[36] = 1)
  (h_is_addw : Main[31] = 0)
  (h_is_trusted : Main[32] = 1)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_addw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addw Main).run s
  := by
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      AddwOperation.constraints, CPUState.constraints, ALUTypeReader.constraints, U16MSBOperation.constraints,
      h_is_real, h_is_trusted] at state_cstrs
    obtain ⟨read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    simp [constraints] at cstrs

    obtain ⟨addw_op_cstrs, cpu_cstrs, alu_cstrs, _⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨ trusted_instr_prop, _, _, _, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _ ⟩ := alu_cstrs
    simp [Opcode.ofNat, Nat.ble] at *
    simp_all

    obtain ⟨ _, _, is_U64_c ⟩ := is_U64_c

    rw [h_is_real] at *
    apply AddwOperation.spec is_U64_b is_U64_c at addw_op_cstrs
    obtain ⟨ is_U32_val, is_addw, is_msb ⟩ := addw_op_cstrs
    simp_all

    -- Now the monadic manipulation
    simp [spec_addw, sp1_addw, execute, execute_RTYPEW']
    rw [Sail.run_readReg, read_pc]

    simp only [BitVec.ofNatLT_eq_ofNat] at *
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]

    rw [exec_RTYPEW_pure_bv_to_w _ _ _ (by omega) (by omega)]
    simp [execute_RTYPEW_pure_w]
    rw [← is_addw] at is_msb
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . have : BitVec.ofNat 5 Main[6] ≠ 0#5 := by
        simp [← BitVec.toNat_inj]; omega
      simp [this, Word.toBitVec64, Word.toNat]
      rw [← is_addw]; congr
      rw [HWord.sign_extend_32_to_64_msb is_U32_val]
      simp [Word.toBitVec64, Word.toNat]

end Addw

namespace Addiw

open Addw

variable
  (Main : Vector (Fin KB) 37)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[35] = 1)
  (h_is_addiw : Main[31] = 1)

def spec_addiw (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ADDIW imm rs1 rd
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21]

def sp1_addiw : SailM Unit := do
  let op_a := sp1_op_a Main --cstrs h_is_real
  -- TODO(gzgz): we can obtain this from the constraint compiler
  -- This comes from the Interaction.state in CPUState
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[33], Main[34], Main[35] * 65535, Main[35] * 65535])

set_option maxHeartbeats 1000000 in
theorem correct_addw
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[36] = 1)
  (h_is_addiw : Main[31] = 1)
  (h_is_trusted : Main[32] = 1)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_addiw op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addiw Main).run s
  := by
    -- Obtain and simplify state and pure constraints
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddwOperation.constraints, CPUState.constraints, ALUTypeReader.constraints, U16MSBOperation.constraints, h_is_real] at state_cstrs
    obtain ⟨read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    simp [constraints] at cstrs
    obtain ⟨addw_op_cstrs, cpu_cstrs, alu_cstrs, _ ⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨ trusted_instr_prop, _, _, ⟨ c0, c1, c2, c3 ⟩, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, _, _, _ ⟩ := alu_cstrs
    simp [Opcode.ofNat, Nat.ble] at *
    simp_all
    have is_U64_c : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]]
      := by apply Word.isU64_of_cases c0 c1 c2 c3

    rw [h_is_real] at *
    apply AddwOperation.spec is_U64_b is_U64_c at addw_op_cstrs
    obtain ⟨ is_U32_val, is_addw, is_msb ⟩ := addw_op_cstrs
    simp_all

    obtain ⟨ h_f, h_imm_c ⟩ := trusted_instr_prop
    simp [h_is_addiw] at h_f h_imm_c
    obtain ⟨ h_c, h_is_imm_c ⟩ := h_imm_c

    simp [BitVec.ofNatLT_eq_ofNat] at *
    -- Now the monadic manipulation
    simp [spec_addiw, sp1_addiw, execute, execute_ADDIW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    rw [← h_is_imm_c]
    rw [exec_RTYPEW_pure_bv_to_w _ _ _ (by omega) (by omega)]
    simp [execute_RTYPEW_pure_w]
    rw [← is_addw] at is_msb
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . have : BitVec.ofNat 5 Main[6] ≠ 0#5 := by
        simp [← BitVec.toNat_inj]; omega
      simp [this, Word.toBitVec64, Word.toNat]
      rw [← is_addw]; congr
      rw [HWord.sign_extend_32_to_64_msb is_U32_val]
      simp [Word.toBitVec64, Word.toNat]

end Addiw
