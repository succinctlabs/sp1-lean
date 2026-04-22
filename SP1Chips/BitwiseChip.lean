import SP1Operations.Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Bitwise.Constraints

open LeanRV64D.Functions
open BitVec

set_option linter.style.setOption false
set_option maxHeartbeats 10000000

namespace Xor

open Bitwise

variable
  (Main : Vector (Fin KB) 52)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_xor : is_xor Main)

def spec_xor (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.XOR
  pure ()

def sp1_xor : SailM Unit := do
  let ⟨ xor, imm ⟩ := h_is_xor
  let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[33], Main[34], Main[35], Main[36]] }, c_low_bytes := { low_bytes := #v[Main[37], Main[38], Main[39], Main[40]] }, bitwise_operation := { result := #v[Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47], Main[48]] } } (Main[49] * 2 + Main[50] * 1 + Main[51] * 0) (Main[49] + Main[50] + Main[51])).1
  let op_a := sp1_op_a Main cstrs (xor_real Main xor)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]])

theorem correct_xor
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ xor, imm ⟩ := h_is_xor
  let op_c := sp1_op_c Main cstrs (xor_real Main xor) imm
  let op_b := sp1_op_b Main cstrs (xor_real Main xor)
  let op_a := sp1_op_a Main cstrs (xor_real Main xor)
  (spec_xor (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_xor Main cstrs h_is_xor).run s
  := by

    let ⟨ xor, imm ⟩ := h_is_xor
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (xor_real Main xor)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (xor_real Main xor)
    have h_imm := immediate_bounds Main cstrs (xor_real Main xor)
    have h_a0 := op_a_is_0 Main cstrs (xor_real Main xor)
    have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    split at state_cstrs

    simp_all
    simp [SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1; simp_all

    simp [spec_xor, sp1_xor, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
      have := spec.xor Main ⟨ xor, imm ⟩ cstrs
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Xor

namespace Xori

open Bitwise

variable
  (Main : Vector (Fin KB) 52)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_xori : is_xori Main)

def spec_xori (shamt : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE shamt rs1 rd iop.XORI
  pure ()

def sp1_xori : SailM Unit := do
  let ⟨ xor, imm ⟩ := h_is_xori
  let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[33], Main[34], Main[35], Main[36]] }, c_low_bytes := { low_bytes := #v[Main[37], Main[38], Main[39], Main[40]] }, bitwise_operation := { result := #v[Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47], Main[48]] } } (Main[49] * 2 + Main[50] * 1 + Main[51] * 0) (Main[49] + Main[50] + Main[51])).1
  let op_a := sp1_op_a Main cstrs (xor_real Main xor)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]])

theorem correct_xori
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ xor, imm ⟩ := h_is_xori
  let op_c := sp1_op_c_imm Main cstrs (xor_real Main xor) imm
  let op_b := sp1_op_b Main cstrs (xor_real Main xor)
  let op_a := sp1_op_a Main cstrs (xor_real Main xor)
  (spec_xori op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_xori Main cstrs h_is_xori).run s
  := by
    let ⟨ xor, imm ⟩ := h_is_xori
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (xor_real Main xor)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (xor_real Main xor)
    have h_imm := immediate_bounds Main cstrs (xor_real Main xor)
    have h_a0 := op_a_is_0 Main cstrs (xor_real Main xor)
    have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    split at state_cstrs

    simp_all
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, read_op_a, read_op_b⟩ := state_cstrs
    clear thr1; simp_all

    simp [spec_xori, sp1_xori, execute, execute_ITYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      have := spec.xori Main ⟨ xor, imm ⟩ cstrs
      rw [← h_imm]
      rw [exec_ITYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Xori

namespace Or

open Bitwise

variable
  (Main : Vector (Fin KB) 52)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_or : is_or Main)

def spec_or (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.OR
  pure ()

def sp1_or : SailM Unit := do
  let ⟨ or, imm ⟩ := h_is_or
  let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[33], Main[34], Main[35], Main[36]] }, c_low_bytes := { low_bytes := #v[Main[37], Main[38], Main[39], Main[40]] }, bitwise_operation := { result := #v[Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47], Main[48]] } } (Main[49] * 2 + Main[50] * 1 + Main[51] * 0) (Main[49] + Main[50] + Main[51])).1
  let op_a := sp1_op_a Main cstrs (or_real Main or)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]])

theorem correct_or
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ or, imm ⟩ := h_is_or
  let op_c := sp1_op_c Main cstrs (or_real Main or) imm
  let op_b := sp1_op_b Main cstrs (or_real Main or)
  let op_a := sp1_op_a Main cstrs (or_real Main or)
  (spec_or (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_or Main cstrs h_is_or).run s
  := by
    let ⟨ or, imm ⟩ := h_is_or
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (or_real Main or)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (or_real Main or)
    have h_imm := immediate_bounds Main cstrs (or_real Main or)
    have h_a0 := op_a_is_0 Main cstrs (or_real Main or)
    have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    split at state_cstrs

    simp_all
    simp [SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1; simp_all

    simp [spec_or, sp1_or, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
      have := spec.or Main ⟨ or, imm ⟩ cstrs
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Or

namespace Ori

open Bitwise

variable
  (Main : Vector (Fin KB) 52)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_ori : is_ori Main)

def spec_ori (shamt : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE shamt rs1 rd iop.ORI
  pure ()

def sp1_ori : SailM Unit := do
  let ⟨ or, imm ⟩ := h_is_ori
  let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[33], Main[34], Main[35], Main[36]] }, c_low_bytes := { low_bytes := #v[Main[37], Main[38], Main[39], Main[40]] }, bitwise_operation := { result := #v[Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47], Main[48]] } } (Main[49] * 2 + Main[50] * 1 + Main[51] * 0) (Main[49] + Main[50] + Main[51])).1
  let op_a := sp1_op_a Main cstrs (or_real Main or)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]])

theorem correct_ori
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ or, imm ⟩ := h_is_ori
  let op_c := sp1_op_c_imm Main cstrs (or_real Main or) imm
  let op_b := sp1_op_b Main cstrs (or_real Main or)
  let op_a := sp1_op_a Main cstrs (or_real Main or)
  (spec_ori op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_ori Main cstrs h_is_ori).run s
  := by
    let ⟨ or, imm ⟩ := h_is_ori
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (or_real Main or)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (or_real Main or)
    have h_imm := immediate_bounds Main cstrs (or_real Main or)
    have h_a0 := op_a_is_0 Main cstrs (or_real Main or)
    have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    split at state_cstrs

    simp_all
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, read_op_a, read_op_b⟩ := state_cstrs
    clear thr1; simp_all

    simp [spec_ori, sp1_ori, execute, execute_ITYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      have := spec.ori Main ⟨ or, imm ⟩ cstrs
      rw [← h_imm]
      rw [exec_ITYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Ori

namespace And

open Bitwise

variable
  (Main : Vector (Fin KB) 52)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_and : is_and Main)

def spec_and (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.AND
  pure ()

def sp1_and : SailM Unit := do
  let ⟨ and, imm ⟩ := h_is_and
  let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[33], Main[34], Main[35], Main[36]] }, c_low_bytes := { low_bytes := #v[Main[37], Main[38], Main[39], Main[40]] }, bitwise_operation := { result := #v[Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47], Main[48]] } } (Main[49] * 2 + Main[50] * 1 + Main[51] * 0) (Main[49] + Main[50] + Main[51])).1
  let op_a := sp1_op_a Main cstrs (and_real Main and)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]])

theorem correct_and
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ and, imm ⟩ := h_is_and
  let op_c := sp1_op_c Main cstrs (and_real Main and) imm
  let op_b := sp1_op_b Main cstrs (and_real Main and)
  let op_a := sp1_op_a Main cstrs (and_real Main and)
  (spec_and (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_and Main cstrs h_is_and).run s
  := by
    let ⟨ and, imm ⟩ := h_is_and
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (and_real Main and)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (and_real Main and)
    have h_imm := immediate_bounds Main cstrs (and_real Main and)
    have h_a0 := op_a_is_0 Main cstrs (and_real Main and)
    have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    split at state_cstrs

    simp_all
    simp [SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1; simp_all

    simp [spec_and, sp1_and, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
      have := spec.and Main ⟨ and, imm ⟩ cstrs
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end And

namespace Andi

open Bitwise

variable
  (Main : Vector (Fin KB) 52)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_andi : is_andi Main)

def spec_andi (shamt : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE shamt rs1 rd iop.ANDI
  pure ()

def sp1_andi : SailM Unit := do
  let ⟨ and, imm ⟩ := h_is_andi
  let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[33], Main[34], Main[35], Main[36]] }, c_low_bytes := { low_bytes := #v[Main[37], Main[38], Main[39], Main[40]] }, bitwise_operation := { result := #v[Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47], Main[48]] } } (Main[49] * 2 + Main[50] * 1 + Main[51] * 0) (Main[49] + Main[50] + Main[51])).1
  let op_a := sp1_op_a Main cstrs (and_real Main and)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]])

theorem correct_andi
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ and, imm ⟩ := h_is_andi
  let op_c := sp1_op_c_imm Main cstrs (and_real Main and) imm
  let op_b := sp1_op_b Main cstrs (and_real Main and)
  let op_a := sp1_op_a Main cstrs (and_real Main and)
  (spec_andi op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_andi Main cstrs h_is_andi).run s
  := by
    let ⟨ and, imm ⟩ := h_is_andi
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (and_real Main and)
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (and_real Main and)
    have h_imm := immediate_bounds Main cstrs (and_real Main and)
    have h_a0 := op_a_is_0 Main cstrs (and_real Main and)
    have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    split at state_cstrs

    simp_all
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, read_op_a, read_op_b⟩ := state_cstrs
    clear thr1; simp_all

    simp [spec_andi, sp1_andi, execute, execute_ITYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      have := spec.andi Main ⟨ and, imm ⟩ cstrs
      rw [← h_imm]
      rw [exec_ITYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp_all [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Andi
