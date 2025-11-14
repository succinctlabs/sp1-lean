import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftRight.Constraints

open LeanRV64D.Functions
open BitVec

set_option maxHeartbeats 10000000

namespace Srl

open ShiftRight

variable
  (Main : Vector (Fin KB) 70)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_srl : is_srl Main)

def spec_srl (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SRL
  pure ()

def sp1_srl : SailM Unit := do
  let ⟨ srl, imm ⟩ := h_is_srl
  let op_a := sp1_op_a Main cstrs (srl_real Main srl)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]])

set_option maxHeartbeats 1000000 in
theorem correct_srl
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ srl, imm ⟩ := h_is_srl
  let op_c := sp1_op_c Main cstrs (srl_real Main srl) imm
  let op_b := sp1_op_b Main cstrs (srl_real Main srl)
  let op_a := sp1_op_a Main cstrs (srl_real Main srl)
  (spec_srl (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_srl Main cstrs h_is_srl).run s
  := by
    let ⟨ srl, imm ⟩ := h_is_srl
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (srl_real Main srl)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (srl_real Main srl)
    have h_imm := immediate_bounds Main cstrs (srl_real Main srl)
    have h_a0 := op_a_is_0 Main cstrs (srl_real Main srl)
    have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      ha, hb, hc, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3; simp_all

    simp [spec_srl, sp1_srl, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.srl Main ⟨ srl, imm ⟩ cstrs]
      rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Srl

namespace Srli

open ShiftRight

variable
  (Main : Vector (Fin KB) 70)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_srli : is_srli Main)

def spec_srli (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIOP shamt rs1 rd sop.SRLI
  pure ()

def sp1_srli : SailM Unit := do
  let ⟨ srl, imm ⟩ := h_is_srli
  let op_a := sp1_op_a Main cstrs (srl_real Main srl)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]])

set_option maxHeartbeats 1000000 in
theorem correct_srli
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ srl, imm ⟩ := h_is_srli
  let op_c := sp1_op_c_imm Main cstrs (srl_real Main srl) imm (by tauto)
  let op_b := sp1_op_b Main cstrs (srl_real Main srl)
  let op_a := sp1_op_a Main cstrs (srl_real Main srl)
  (spec_srli op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_srli Main cstrs h_is_srli).run s
  := by
    let ⟨ srl, imm ⟩ := h_is_srli
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (srl_real Main srl)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (srl_real Main srl)
    have h_imm := immediate_bounds Main cstrs (srl_real Main srl)
    have h_a0 := op_a_is_0 Main cstrs (srl_real Main srl)
    have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      ha, hb, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3; simp_all

    simp [spec_srli, sp1_srli, execute, execute_SHIFTIOP']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.srli Main ⟨ srl, imm ⟩ cstrs]
      rw [exec_SHIFTIOP_pure_bv_to_w _ _ _ is_U64_b]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]
      congr 2
      omega

end Srli

namespace Srlw

open ShiftRight

variable
  (Main : Vector (Fin KB) 70)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_srlw : is_srlw Main)

def spec_srlw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SRLW
  pure ()

def sp1_srlw : SailM Unit := do
  let ⟨ srlw, imm ⟩ := h_is_srlw
  let op_a := sp1_op_a Main cstrs (srlw_real Main srlw)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]])

set_option maxHeartbeats 1000000 in
theorem correct_srlw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ srlw, imm ⟩ := h_is_srlw
  let op_c := sp1_op_c Main cstrs (srlw_real Main srlw) imm
  let op_b := sp1_op_b Main cstrs (srlw_real Main srlw)
  let op_a := sp1_op_a Main cstrs (srlw_real Main srlw)
  (spec_srlw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_srlw Main cstrs h_is_srlw).run s
  := by
    let ⟨ srlw, imm ⟩ := h_is_srlw
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (srlw_real Main srlw)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (srlw_real Main srlw)
    have h_imm := immediate_bounds Main cstrs (srlw_real Main srlw)
    have h_a0 := op_a_is_0 Main cstrs (srlw_real Main srlw)
    have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      ha, hb, hc, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3; simp_all

    simp [spec_srlw, sp1_srlw, execute, execute_RTYPEW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.srlw Main ⟨ srlw, imm ⟩ cstrs]
      rw [exec_RTYPEW_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Srlw

namespace Srliw

open ShiftRight

variable
  (Main : Vector (Fin KB) 70)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_srliw : is_srliw Main)

def spec_srliw (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW
  pure ()

def sp1_srliw : SailM Unit := do
  let ⟨ srlw, imm ⟩ := h_is_srliw
  let op_a := sp1_op_a Main cstrs (srlw_real Main srlw)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]])

set_option maxHeartbeats 1000000 in
theorem correct_srliw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ srlw, imm ⟩ := h_is_srliw
  let op_c := sp1_op_c_imm_w Main cstrs (srlw_real Main srlw) imm (by tauto)
  let op_b := sp1_op_b Main cstrs (srlw_real Main srlw)
  let op_a := sp1_op_a Main cstrs (srlw_real Main srlw)
  (spec_srliw op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_srliw Main cstrs h_is_srliw).run s
  := by
    let ⟨ srlw, imm ⟩ := h_is_srliw
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (srlw_real Main srlw)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (srlw_real Main srlw)
    have h_imm := immediate_bounds Main cstrs (srlw_real Main srlw)
    have h_a0 := op_a_is_0 Main cstrs (srlw_real Main srlw)
    have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      ha, hb, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3; simp_all

    simp [spec_srliw, sp1_srliw, execute, execute_SHIFTIWOP']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.srliw Main ⟨ srlw, imm ⟩ cstrs]
      rw [exec_SHIFTIWOP_pure_bv_to_w _ _ _ is_U64_b]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]
      have : (Word.low #v[Main[25], 0, 0, 0]).toBitVec32.toNat % 32 =
        (Word.low #v[Main[25], Main[26], Main[27], Main[28]]).toBitVec32.toNat % 32 := by
        simp [Word.low, HWord.toBitVec32, HWord.toNat]
        omega
      rw [this]

end Srliw

namespace Sra

open ShiftRight

variable
  (Main : Vector (Fin KB) 70)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_sra : is_sra Main)

def spec_sra (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SRA
  pure ()

def sp1_sra : SailM Unit := do
  let ⟨ sra, imm ⟩ := h_is_sra
  let op_a := sp1_op_a Main cstrs (sra_real Main sra)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]])

set_option maxHeartbeats 1000000 in
theorem correct_sra
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ sra, imm ⟩ := h_is_sra
  let op_c := sp1_op_c Main cstrs (sra_real Main sra) imm
  let op_b := sp1_op_b Main cstrs (sra_real Main sra)
  let op_a := sp1_op_a Main cstrs (sra_real Main sra)
  (spec_sra (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sra Main cstrs h_is_sra).run s
  := by
    let ⟨ sra, imm ⟩ := h_is_sra
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (sra_real Main sra)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (sra_real Main sra)
    have h_imm := immediate_bounds Main cstrs (sra_real Main sra)
    have h_a0 := op_a_is_0 Main cstrs (sra_real Main sra)
    have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      ha, hb, hc, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3; simp_all

    simp [spec_sra, sp1_sra, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.sra Main ⟨ sra, imm ⟩ cstrs]
      rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Sra

namespace Srai

open ShiftRight

variable
  (Main : Vector (Fin KB) 70)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_srai : is_srai Main)

def spec_srai (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIOP shamt rs1 rd sop.SRAI
  pure ()

def sp1_srai : SailM Unit := do
  let ⟨ sra, imm ⟩ := h_is_srai
  let op_a := sp1_op_a Main cstrs (sra_real Main sra)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]])

set_option maxHeartbeats 1000000 in
theorem correct_srai
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ sra, imm ⟩ := h_is_srai
  let op_c := sp1_op_c_imm Main cstrs (sra_real Main sra) imm (by tauto)
  let op_b := sp1_op_b Main cstrs (sra_real Main sra)
  let op_a := sp1_op_a Main cstrs (sra_real Main sra)
  (spec_srai op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_srai Main cstrs h_is_srai).run s
  := by
    let ⟨ sra, imm ⟩ := h_is_srai
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (sra_real Main sra)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (sra_real Main sra)
    have h_imm := immediate_bounds Main cstrs (sra_real Main sra)
    have h_a0 := op_a_is_0 Main cstrs (sra_real Main sra)
    have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      ha, hb, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3; simp_all

    simp [spec_srai, sp1_srai, execute, execute_SHIFTIOP']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.srai Main ⟨ sra, imm ⟩ cstrs]
      rw [exec_SHIFTIOP_pure_bv_to_w _ _ _ is_U64_b]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]
      congr 2
      omega

end Srai

namespace Sraw

open ShiftRight

variable
  (Main : Vector (Fin KB) 70)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_sraw : is_sraw Main)

def spec_sraw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SRAW
  pure ()

def sp1_sraw : SailM Unit := do
  let ⟨ sraw, imm ⟩ := h_is_sraw
  let op_a := sp1_op_a Main cstrs (sraw_real Main sraw)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]])

set_option maxHeartbeats 1000000 in
theorem correct_sraw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ sraw, imm ⟩ := h_is_sraw
  let op_c := sp1_op_c Main cstrs (sraw_real Main sraw) imm
  let op_b := sp1_op_b Main cstrs (sraw_real Main sraw)
  let op_a := sp1_op_a Main cstrs (sraw_real Main sraw)
  (spec_sraw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sraw Main cstrs h_is_sraw).run s
  := by
    let ⟨ sraw, imm ⟩ := h_is_sraw
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (sraw_real Main sraw)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (sraw_real Main sraw)
    have h_imm := immediate_bounds Main cstrs (sraw_real Main sraw)
    have h_a0 := op_a_is_0 Main cstrs (sraw_real Main sraw)
    have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      ha, hb, hc, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3; simp_all

    simp [spec_sraw, sp1_sraw, execute, execute_RTYPEW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.sraw Main ⟨ sraw, imm ⟩ cstrs]
      rw [exec_RTYPEW_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Sraw

namespace Sraiw

open ShiftRight

variable
  (Main : Vector (Fin KB) 70)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_sraiw : is_sraiw Main)

def spec_sraiw (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW
  pure ()

def sp1_sraiw : SailM Unit := do
  let ⟨ sraw, imm ⟩ := h_is_sraiw
  let op_a := sp1_op_a Main cstrs (sraw_real Main sraw)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]])

set_option maxHeartbeats 1000000 in
theorem correct_sraiw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ sraw, imm ⟩ := h_is_sraiw
  let op_c := sp1_op_c_imm_w Main cstrs (sraw_real Main sraw) imm (by tauto)
  let op_b := sp1_op_b Main cstrs (sraw_real Main sraw)
  let op_a := sp1_op_a Main cstrs (sraw_real Main sraw)
  (spec_sraiw op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sraiw Main cstrs h_is_sraiw).run s
  := by
    let ⟨ sraw, imm ⟩ := h_is_sraiw
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (sraw_real Main sraw)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (sraw_real Main sraw)
    have h_imm := immediate_bounds Main cstrs (sraw_real Main sraw)
    have h_a0 := op_a_is_0 Main cstrs (sraw_real Main sraw)
    have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
    simp_all

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      ha, hb, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, thr2, thr3, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 thr2 thr3; simp_all

    simp [spec_sraiw, sp1_sraiw, execute, execute_SHIFTIWOP']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.sraiw Main ⟨ sraw, imm ⟩ cstrs]
      rw [exec_SHIFTIWOP_pure_bv_to_w _ _ _ is_U64_b]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]
      have : (Word.low #v[Main[25], 0, 0, 0]).toBitVec32.toNat % 32 =
        (Word.low #v[Main[25], Main[26], Main[27], Main[28]]).toBitVec32.toNat % 32 := by
        simp [Word.low, HWord.toBitVec32, HWord.toNat]
        omega
      rw [this]

end Sraiw
