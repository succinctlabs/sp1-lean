import SP1Operations.Operation.MulOperation
import SP1Operations.Operation.AddOperation
import SP1Operations.Compare.IsEqualWordOperation
import SP1Operations.Compare.IsZeroWordOperation
import SP1Operations.Compare.LtOperationUnsigned
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.DivRem.Constraints

open LeanRV64D.Functions
open BitVec

set_option maxHeartbeats 10000000

open DivRem

variable
  (Main : Vector (Fin KB) 247)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : is_real Main)

def sp1_op : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]])

namespace Div

open DivRem

def spec_div (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_div
  (h_is_div : is_div Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_div (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, RTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_div, sp1_op, execute, execute_DIV']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.div Main cstrs h_is_real h_is_div]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Div

namespace Divu

open DivRem

def spec_divu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_divu
  (h_is_divu : is_divu Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_divu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, RTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_divu, sp1_op, execute, execute_DIV']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divu Main cstrs h_is_real h_is_divu]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Divu

namespace Divw

open DivRem

def spec_divw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_divw
  (h_is_divw : is_divw Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_divw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, RTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_divw, sp1_op, execute, execute_DIVW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divw Main cstrs h_is_real h_is_divw]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Divw

namespace Divuw

open DivRem

def spec_divuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_divuw
  (h_is_divuw : is_divuw Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_divuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, RTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_divuw, sp1_op, execute, execute_DIVW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divuw Main cstrs h_is_real h_is_divuw]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Divuw

namespace Rem

open DivRem

def spec_rem (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_rem
  (h_is_rem : is_rem Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_rem (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, RTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_rem, sp1_op, execute, execute_REM']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.rem Main cstrs h_is_real h_is_rem]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Rem

namespace Remu

open DivRem

def spec_remu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_remu
  (h_is_remu : is_remu Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_remu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, RTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_remu, sp1_op, execute, execute_REM']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remu Main cstrs h_is_real h_is_remu]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Remu

namespace Remw

open DivRem

def spec_remw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_remw
  (h_is_remw : is_remw Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_remw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, RTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_remw, sp1_op, execute, execute_REMW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remw Main cstrs h_is_real h_is_remw]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Remw

namespace Remuw

open DivRem

def spec_remuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem correct_remuw
  (h_is_remuw : is_remuw Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_remuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    simp at h_is_real
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs h_is_real
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
    have h_a0 := op_a_is_0 Main cstrs h_is_real
    have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, RTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, thr4, thr5, thr6, thr7, thr8, thr9, thr10, thr11, thr12, thr13, thr14, thr15, thr16, thr17, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3 thr4 thr5 thr6 thr7 thr8 thr9 thr10 thr11 thr12 thr13 thr14 thr15 thr16 thr17 trusted_instr_state; simp_all

    simp [spec_remuw, sp1_op, execute, execute_REMW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remuw Main cstrs h_is_real h_is_remuw]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Remuw
