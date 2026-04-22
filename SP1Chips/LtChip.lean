import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Lt.Constraints

open LeanRV64D.Functions
open BitVec

namespace Slt

open Lt

variable
  (Main : Vector (Fin KB) 45)
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
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[35], 0, 0, 0])

set_option maxHeartbeats 1000000 in

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
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, M33⟩ := cstrs
    have h_is_real : Main[33] + Main[34] = 1 := by simp_all
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨ _, trusted_instr_prop, _, _, _, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _ ⟩ := alu_cstrs

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all [BitVec.ofNatLT_eq_ofNat]
    obtain ⟨ _, _, is_U64_c ⟩ := is_U64_c

    -- Now the monadic manipulation
    simp [spec_slt, sp1_slt, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (c := BitVec.ofNat 5 ↑Main[6] = 0#5) (by simp [← BitVec.toNat_inj]; omega)]
      apply LtOperationSigned.spec.signed at lt_op_cstrs <;>
      [ simp_all; exact is_U64_b; exact is_U64_c ]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Slt

namespace Slti

open Lt

variable
  (Main : Vector (Fin KB) 45)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_sltu : is_sltu Main)

def spec_slti (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.SLTI
  pure ()

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    change Main[6] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sltu h_is_sltu] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
    have h32 : Main[32] = 1 := (sub_eq_zero.mp (alu.2.2.1.resolve_right (by decide))).symm
    exact (alu.2.2.2.1 (by rw [h32]; decide)).2.1

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp
    change Main[14] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sltu h_is_sltu] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
    have h32 : Main[32] = 1 := (sub_eq_zero.mp (alu.2.2.1.resolve_right (by decide))).symm
    exact (alu.2.2.2.1 (by rw [h32]; decide)).1.1

def sp1_op_c : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[21] ?_
    simp
    change Main[21] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sltu h_is_sltu] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
    have h32 : Main[32] = 1 := (sub_eq_zero.mp (alu.2.2.1.resolve_right (by decide))).symm
    exact (alu.2.2.2.1 (by rw [h32]; decide)).1.2.1

def sp1_slti : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_sltu
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[35], 0, 0, 0])

set_option maxHeartbeats 1000000 in

-- correctness proof across slt/slti/sltu/sltiu arms
theorem correct_slti
  (cstrs : (constraints Main).allHold)
  (h_is_slti : is_slti Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_sltu
  let op_b := sp1_op_b Main cstrs h_is_sltu
  let op_a := sp1_op_a Main cstrs h_is_sltu
  (spec_slti op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_slti Main cstrs h_is_sltu).run s
  := by
    have h21 : Main[21].val < 32 := by
      rw [SP1ConstraintList.allHold, allHold_constraints_iff_sltu h_is_sltu] at cstrs
      obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
      simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
      simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
    have h632 : Main[6].val < 32 := by
      rw [SP1ConstraintList.allHold, allHold_constraints_iff_sltu h_is_sltu] at cstrs
      obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
      simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
      simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_slti] at h_is_slti
    rw [allHold_constraints_iff_slti h_is_slti] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, M33⟩ := cstrs
    have h_is_real : Main[33] + Main[34] = 1 := by simp_all
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨ _, trusted_instr_prop, _, _, ⟨ c0, c1, c2, c3 ⟩, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _ ⟩ := alu_cstrs
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *
    have is_U64_c : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]]
      := by apply Word.isU64_of_cases c0 c1 c2 c3
    obtain ⟨ h_f, h_imm_c ⟩ := trusted_instr_prop

    have h_imm' : setWidth 12 (BitVec.ofNat 5 ↑Main[21]) = BitVec.ofNat 12 Main[21] := by
      simp [setWidth, setWidth', BitVec.ofNatLT_eq_ofNat]
      grind

    simp [h_f] at read_op_b
    simp [spec_slti, sp1_slti, execute, execute_ITYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_a]
    simp [BitVec.ofNatLT_eq_ofNat, h_imm', ← h_imm_c]
    rw [exec_ITYPE_pure_bv_to_w _ _ _ is_U64_b is_U64_c]
    simp [execute_ITYPE_pure_w]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . have h6' : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        simp [← BitVec.toNat_inj]
        clear *- h_is_op_a_0 h632
        omega
      simp [h6']
      simp [Word.toBitVec64, Word.toNat]

      apply LtOperationSigned.spec.signed is_U64_b is_U64_c at lt_op_cstrs
      simp at lt_op_cstrs
      simp [lt_op_cstrs]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Slti

namespace Sltu

open Lt

variable
  (Main : Vector (Fin KB) 45)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_sltu : is_sltu Main)

def spec_sltu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLTU
  pure ()

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    change Main[6] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sltu h_is_sltu] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
    have h32 : Main[32] = 1 := (sub_eq_zero.mp (alu.2.2.1.resolve_right (by decide))).symm
    exact (alu.2.2.2.1 (by rw [h32]; decide)).2.1

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp
    change Main[14] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sltu h_is_sltu] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
    have h32 : Main[32] = 1 := (sub_eq_zero.mp (alu.2.2.1.resolve_right (by decide))).symm
    exact (alu.2.2.2.1 (by rw [h32]; decide)).1.1

def sp1_op_c : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[21] ?_
    simp
    change Main[21] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sltu h_is_sltu] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
    have h32 : Main[32] = 1 := (sub_eq_zero.mp (alu.2.2.1.resolve_right (by decide))).symm
    exact (alu.2.2.2.1 (by rw [h32]; decide)).1.2.1

def sp1_sltu : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_sltu
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[35], 0, 0, 0])

set_option maxHeartbeats 1000000 in

-- correctness proof across slt/slti/sltu/sltiu arms
theorem correct_sltu
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_sltu
  let op_b := sp1_op_b Main cstrs h_is_sltu
  let op_a := sp1_op_a Main cstrs h_is_sltu
  (spec_sltu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sltu Main cstrs h_is_sltu).run s
  := by
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_sltu] at h_is_sltu
    rw [allHold_constraints_iff_sltu h_is_sltu] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, M33⟩ := cstrs
    have h_is_real : Main[33] + Main[34] = 1 := by simp_all
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨ _, trusted_instr_prop, _, _, _, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _ ⟩ := alu_cstrs

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all
    obtain ⟨ _, _, is_U64_c ⟩ := is_U64_c

    -- Now the monadic manipulation
    simp [spec_sltu, sp1_sltu, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
    simp [execute_RTYPEW_pure_w]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (c := (Main[6])#'_ = 0#5) (by simpa [← BitVec.toNat_inj])]
      apply LtOperationSigned.spec.unsigned at lt_op_cstrs <;>
      [ simp_all; exact is_U64_b; exact is_U64_c ]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Sltu

namespace Sltiu

open Lt

variable
  (Main : Vector (Fin KB) 45)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_sltiu : is_sltiu Main)

def spec_sltiu (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.SLTIU
  pure ()

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    change Main[6] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sltiu h_is_sltiu] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
    have h32 : Main[32] = 1 := (sub_eq_zero.mp (alu.2.2.1.resolve_right (by decide))).symm
    exact (alu.2.2.2.1 (by rw [h32]; decide)).2.1

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp
    change Main[14] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sltiu h_is_sltiu] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
    have h32 : Main[32] = 1 := (sub_eq_zero.mp (alu.2.2.1.resolve_right (by decide))).symm
    exact (alu.2.2.2.1 (by rw [h32]; decide)).1.1

def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_sltiu : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_sltiu
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[35], 0, 0, 0])

set_option maxHeartbeats 1000000 in

-- correctness proof across slt/slti/sltu/sltiu arms
theorem correct_sltu
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main cstrs h_is_sltiu
  let op_a := sp1_op_a Main cstrs h_is_sltiu
  (spec_sltiu op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sltiu Main cstrs h_is_sltiu).run s
  := by
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_sltiu] at h_is_sltiu
    rw [allHold_constraints_iff_sltiu h_is_sltiu] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, M33⟩ := cstrs
    have h_is_real : Main[33] + Main[34] = 1 := by simp_all
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨ _, trusted_instr_prop, _, _, ⟨ c0, c1, c2, c3 ⟩, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _ ⟩ := alu_cstrs

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all
    have is_U64_c : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]]
      := by apply Word.isU64_of_cases c0 c1 c2 c3
    obtain ⟨ h_f, h_imm_c ⟩ := trusted_instr_prop

    -- Now the monadic manipulation
    simp [spec_sltiu, sp1_sltiu, execute, execute_ITYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    rw [← h_imm_c]
    rw [exec_ITYPE_pure_bv_to_w _ _ _ is_U64_b is_U64_c]
    simp [execute_ITYPE_pure_w]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (c := (Main[6])#'_ = 0#5) (by simpa [← BitVec.toNat_inj])]
      apply LtOperationSigned.spec.unsigned at lt_op_cstrs <;>
      [ simp_all; exact is_U64_b; exact is_U64_c ]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Sltiu
