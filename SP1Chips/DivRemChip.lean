import SP1Operations.Operation.MulOperation
import SP1Operations.Operation.AddOperation
import SP1Operations.Compare.IsEqualWordOperation
import SP1Operations.Compare.IsZeroWordOperation
import SP1Operations.Compare.LtOperationUnsigned
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.DivRem.Constraints

open LeanRV64IM.Functions
open BitVec

set_option maxHeartbeats 10000000

open DivRem

variable
  (Main : Vector (Fin BB) 251)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : is_real Main)

def sp1_op : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])

namespace Div

open DivRem

variable (h_is_div : is_div Main)

def spec_div (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_div
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ _, imm ⟩ := h_is_div
  let op_c := sp1_op_c Main cstrs h_is_real imm
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_div (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    let ⟨ div, imm ⟩ := h_is_div
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_div, sp1_op, execute, execute_DIV']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.div Main cstrs h_is_real div]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Div

namespace Divu

open DivRem

variable (h_is_divu : is_divu Main)

def spec_divu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_divu
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ _, imm ⟩ := h_is_divu
  let op_c := sp1_op_c Main cstrs h_is_real imm
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_divu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    let ⟨ divu, imm ⟩ := h_is_divu
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_divu, sp1_op, execute, execute_DIV']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divu Main cstrs h_is_real divu]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Divu

namespace Divw

open DivRem

variable (h_is_divw : is_divw Main)

def spec_divw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_divw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ _, imm ⟩ := h_is_divw
  let op_c := sp1_op_c Main cstrs h_is_real imm
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_divw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    let ⟨ divw, imm ⟩ := h_is_divw
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_divw, sp1_op, execute, execute_DIVW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divw Main cstrs h_is_real divw]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Divw

namespace Divuw

open DivRem

variable (h_is_divuw : is_divuw Main)

def spec_divuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_divuw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ _, imm ⟩ := h_is_divuw
  let op_c := sp1_op_c Main cstrs h_is_real imm
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_divuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    let ⟨ divuw, imm ⟩ := h_is_divuw
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_divuw, sp1_op, execute, execute_DIVW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divuw Main cstrs h_is_real divuw]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Divuw

namespace Rem

open DivRem

variable (h_is_rem : is_rem Main)

def spec_rem (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_rem
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ _, imm ⟩ := h_is_rem
  let op_c := sp1_op_c Main cstrs h_is_real imm
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_rem (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    let ⟨ rem, imm ⟩ := h_is_rem
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_rem, sp1_op, execute, execute_REM']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.rem Main cstrs h_is_real rem]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Rem

namespace Remu

open DivRem

variable (h_is_remu : is_remu Main)

def spec_remu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_remu
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ _, imm ⟩ := h_is_remu
  let op_c := sp1_op_c Main cstrs h_is_real imm
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_remu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    let ⟨ remu, imm ⟩ := h_is_remu
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_remu, sp1_op, execute, execute_REM']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remu Main cstrs h_is_real remu]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Remu

namespace Remw

open DivRem

variable (h_is_remw : is_remw Main)

def spec_remw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_remw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ _, imm ⟩ := h_is_remw
  let op_c := sp1_op_c Main cstrs h_is_real imm
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_remw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    let ⟨ remw, imm ⟩ := h_is_remw
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_remw, sp1_op, execute, execute_REMW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remw Main cstrs h_is_real remw]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Remw

namespace Remuw

open DivRem

variable (h_is_remuw : is_remuw Main)

def spec_remuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_remuw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ _, imm ⟩ := h_is_remuw
  let op_c := sp1_op_c Main cstrs h_is_real imm
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_remuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    let ⟨ remuw, imm ⟩ := h_is_remuw
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_remuw, sp1_op, execute, execute_REMW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remuw Main cstrs h_is_real remuw]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Remuw
