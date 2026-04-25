import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftLeft.Constraints

open LeanRV64D.Functions
open BitVec

namespace Sll

open ShiftLeft

variable
  (Main : Vector (Fin KB) 65)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_sll : is_sll Main)

def spec_sll (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLL
  pure ()

def sp1_sll : SailM Unit := do
  let ⟨sll, imm⟩ := h_is_sll
  let op_a := sp1_op_a Main cstrs (sll_real Main sll)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])


-- correctness proof across sll/slli/sllw/slliw arms
theorem correct_sll
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨sll, imm⟩ := h_is_sll
  let op_c := sp1_op_c Main cstrs (sll_real Main sll) imm
  let op_b := sp1_op_b Main cstrs (sll_real Main sll)
  let op_a := sp1_op_a Main cstrs (sll_real Main sll)
  (spec_sll (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sll Main cstrs h_is_sll).run s
  := by
    have _ := state_cstrs
    let ⟨sll, imm⟩ := h_is_sll
    have ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_imm, h_a0⟩ := bounds Main cstrs (sll_real Main sll)
    have ⟨sop1, sop2⟩ := single_op Main cstrs
    simp_all
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
      List.Forall, CPUState.constraints, ALUTypeReader.constraints, ha, hb, hc] at state_cstrs
    obtain ⟨thr, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr; simp_all
    simp [spec_sll, sp1_sll, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.sll Main ⟨sll, imm⟩ cstrs]
      rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Sll

namespace Slli

open ShiftLeft

variable
  (Main : Vector (Fin KB) 65)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_slli : is_slli Main)

def spec_slli (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIOP shamt rs1 rd sop.SLLI
  pure ()

def sp1_slli : SailM Unit := do
  let ⟨sll, imm⟩ := h_is_slli
  let op_a := sp1_op_a Main cstrs (sll_real Main sll)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])


-- correctness proof across sll/slli/sllw/slliw arms
theorem correct_slli
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨sll, imm⟩ := h_is_slli
  let op_c := sp1_op_c_imm Main cstrs (sll_real Main sll) imm (by tauto)
  let op_b := sp1_op_b Main cstrs (sll_real Main sll)
  let op_a := sp1_op_a Main cstrs (sll_real Main sll)
  (spec_slli op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_slli Main cstrs h_is_slli).run s
  := by
    have _ := state_cstrs
    let ⟨sll, imm⟩ := h_is_slli
    have ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_imm, h_a0⟩ := bounds Main cstrs (sll_real Main sll)
    have ⟨sop1, sop2⟩ := single_op Main cstrs
    simp_all
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
      List.Forall, CPUState.constraints, ALUTypeReader.constraints, ha, hb] at state_cstrs
    obtain ⟨thr, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr; simp_all
    simp [spec_slli, sp1_slli, execute, execute_SHIFTIOP']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.slli Main ⟨sll, imm⟩ cstrs]
      rw [exec_SHIFTIOP_pure_bv_to_w _ _ _ is_U64_b]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Slli

namespace Sllw

open ShiftLeft

variable
  (Main : Vector (Fin KB) 65)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_sllw : is_sllw Main)

def spec_sllw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SLLW
  pure ()

def sp1_sllw : SailM Unit := do
  let ⟨sllw, imm⟩ := h_is_sllw
  let op_a := sp1_op_a Main cstrs (sllw_real Main sllw)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])


-- correctness proof across sll/slli/sllw/slliw arms
theorem correct_sllw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨sllw, imm⟩ := h_is_sllw
  let op_c := sp1_op_c Main cstrs (sllw_real Main sllw) imm
  let op_b := sp1_op_b Main cstrs (sllw_real Main sllw)
  let op_a := sp1_op_a Main cstrs (sllw_real Main sllw)
  (spec_sllw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sllw Main cstrs h_is_sllw).run s
  := by
    have _ := state_cstrs
    let ⟨sllw, imm⟩ := h_is_sllw
    have ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_imm, h_a0⟩ := bounds Main cstrs (sllw_real Main sllw)
    have ⟨sop1, sop2⟩ := single_op Main cstrs
    simp_all
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
      List.Forall, CPUState.constraints, ALUTypeReader.constraints, ha, hb, hc] at state_cstrs
    obtain ⟨thr, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr; simp_all
    simp [spec_sllw, sp1_sllw, execute, execute_RTYPEW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.sllw Main ⟨sllw, imm⟩ cstrs]
      rw [exec_RTYPEW_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Sllw

namespace Slliw

open ShiftLeft

variable
  (Main : Vector (Fin KB) 65)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_slliw : is_slliw Main)

def spec_slliw (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW
  pure ()

def sp1_slliw : SailM Unit := do
  let ⟨sllw, imm⟩ := h_is_slliw
  let op_a := sp1_op_a Main cstrs (sllw_real Main sllw)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])


-- correctness proof across sll/slli/sllw/slliw arms
theorem correct_slliw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨sllw, imm⟩ := h_is_slliw
  let op_c := sp1_op_c_imm_w Main cstrs (sllw_real Main sllw) imm (by tauto)
  let op_b := sp1_op_b Main cstrs (sllw_real Main sllw)
  let op_a := sp1_op_a Main cstrs (sllw_real Main sllw)
  (spec_slliw op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_slliw Main cstrs h_is_slliw).run s
  := by
    have _ := state_cstrs
    let ⟨sllw, imm⟩ := h_is_slliw
    have ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_imm, h_a0⟩ := bounds Main cstrs (sllw_real Main sllw)
    have ⟨sop1, sop2⟩ := single_op Main cstrs
    simp_all
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
      List.Forall, CPUState.constraints, ALUTypeReader.constraints, ha, hb] at state_cstrs
    obtain ⟨thr, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr; simp_all
    simp [spec_slliw, sp1_slliw, execute, execute_SHIFTIWOP']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [spec.slliw Main ⟨sllw, imm⟩ cstrs]
      rw [exec_SHIFTIWOP_pure_bv_to_w _ _ _ is_U64_b]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Slliw
