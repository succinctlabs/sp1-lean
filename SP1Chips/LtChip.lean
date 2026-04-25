import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Lt.Constraints

open LeanRV64D.Functions
open BitVec

namespace Slt

open Lt

variable
  (Main : Vector (Fin KB) 44)
  (s : SailState)

def spec_slt (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLT
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21]

def sp1_slt : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[34], 0, 0, 0])

-- correctness proof across slt/slti/sltu/sltiu arms
theorem correct_slt
  (cstrs : (constraints Main).allHold)
  (h_is_slt : is_slt Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_slt (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_slt Main).run s
  := by
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_slt] at h_is_slt
    rw [allHold_constraints_iff_slt h_is_slt] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, M33, _M13⟩ := cstrs
    have h_is_real : Main[32] + Main[33] = 1 := by simp_all
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨trusted_instr_prop, _, _, _, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _⟩ := alu_cstrs
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all [BitVec.ofNatLT_eq_ofNat]
    obtain ⟨_, _, is_U64_c⟩ := is_U64_c
    -- Now the monadic manipulation
    simp [spec_slt, sp1_slt, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (c := BitVec.ofNat 5 ↑Main[6] = 0#5) (by simp [← BitVec.toNat_inj]; omega)]
      apply LtOperationSigned.spec.signed at lt_op_cstrs <;>
      [ simp_all; exact is_U64_b; exact is_U64_c ]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Slt

namespace Slti

open Lt

variable
  (Main : Vector (Fin KB) 44)
  (s : SailState)

def spec_slti (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.SLTI
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_slti : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[34], 0, 0, 0])

-- correctness proof across slt/slti/sltu/sltiu arms
theorem correct_slti
  (cstrs : (constraints Main).allHold)
  (h_is_slti : is_slti Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_slti op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_slti Main).run s
  := by
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_slti] at h_is_slti
    rw [allHold_constraints_iff_slti h_is_slti] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, M33, _M13⟩ := cstrs
    have h_is_real : Main[32] + Main[33] = 1 := by simp_all
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨trusted_instr_prop, _, _, ⟨c0, c1, c2, c3⟩, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _⟩ := alu_cstrs
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all [BitVec.ofNatLT_eq_ofNat]
    have is_U64_c : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]]
      := by apply Word.isU64_of_cases c0 c1 c2 c3
    obtain ⟨h_f, h_imm_c⟩ := trusted_instr_prop
    -- Now the monadic manipulation
    simp [spec_slti, sp1_slti, execute, execute_ITYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    rw [← h_imm_c]
    rw [exec_ITYPE_pure_bv_to_w _ _ _ is_U64_b is_U64_c]
    simp [execute_ITYPE_pure_w]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (c := BitVec.ofNat 5 ↑Main[6] = 0#5) (by simp [← BitVec.toNat_inj]; omega)]
      apply LtOperationSigned.spec.signed at lt_op_cstrs <;>
      [ simp_all; exact is_U64_b; exact is_U64_c ]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Slti

namespace Sltu

open Lt

variable
  (Main : Vector (Fin KB) 44)
  (s : SailState)

def spec_sltu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLTU
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21]

def sp1_sltu : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[34], 0, 0, 0])

-- correctness proof across slt/slti/sltu/sltiu arms
theorem correct_sltu
  (cstrs : (constraints Main).allHold)
  (h_is_sltu : is_sltu Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_sltu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sltu Main).run s
  := by
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_sltu] at h_is_sltu
    rw [allHold_constraints_iff_sltu h_is_sltu] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, M32, _M13⟩ := cstrs
    have h_is_real : Main[32] + Main[33] = 1 := by simp_all
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨trusted_instr_prop, _, _, _, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _⟩ := alu_cstrs
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all [BitVec.ofNatLT_eq_ofNat]
    obtain ⟨_, _, is_U64_c⟩ := is_U64_c
    -- Now the monadic manipulation
    simp [spec_sltu, sp1_sltu, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (c := BitVec.ofNat 5 ↑Main[6] = 0#5) (by simp [← BitVec.toNat_inj]; omega)]
      apply LtOperationSigned.spec.unsigned at lt_op_cstrs <;>
      [ simp_all; exact is_U64_b; exact is_U64_c ]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Sltu

namespace Sltiu

open Lt

variable
  (Main : Vector (Fin KB) 44)
  (s : SailState)

def spec_sltiu (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.SLTIU
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_sltiu : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[34], 0, 0, 0])

-- correctness proof across slt/slti/sltu/sltiu arms
theorem correct_sltiu
  (cstrs : (constraints Main).allHold)
  (h_is_sltiu : is_sltiu Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_sltiu op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sltiu Main).run s
  := by
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_sltiu] at h_is_sltiu
    rw [allHold_constraints_iff_sltiu h_is_sltiu] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, M32, _M13⟩ := cstrs
    have h_is_real : Main[32] + Main[33] = 1 := by simp_all
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨trusted_instr_prop, _, _, ⟨c0, c1, c2, c3⟩, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _⟩ := alu_cstrs
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all [BitVec.ofNatLT_eq_ofNat]
    have is_U64_c : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]]
      := by apply Word.isU64_of_cases c0 c1 c2 c3
    obtain ⟨h_f, h_imm_c⟩ := trusted_instr_prop
    -- Now the monadic manipulation
    simp [spec_sltiu, sp1_sltiu, execute, execute_ITYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    rw [← h_imm_c]
    rw [exec_ITYPE_pure_bv_to_w _ _ _ is_U64_b is_U64_c]
    simp [execute_ITYPE_pure_w]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (c := BitVec.ofNat 5 ↑Main[6] = 0#5) (by simp [← BitVec.toNat_inj]; omega)]
      apply LtOperationSigned.spec.unsigned at lt_op_cstrs <;>
      [ simp_all; exact is_U64_b; exact is_U64_c ]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Sltiu
