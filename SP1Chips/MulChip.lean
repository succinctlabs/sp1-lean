import SP1Operations.Operation.MulOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Mul.Constraints

open LeanRV64IM.Functions
open BitVec

set_option maxHeartbeats 10000000

namespace Mul

open Mul

variable
  (Main : Vector (Fin BB) 87)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_mul : is_mul Main)

def spec_mul (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd { high := false, signed_rs1 := false, signed_rs2 := false }
  pure ()

def sp1_mul : SailM Unit := do
  let ⟨ is_mul, imm ⟩ := h_is_mul
  let op_a := sp1_op_a Main cstrs (mul_real Main is_mul)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])

theorem correct_mul
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ is_mul, imm ⟩ := h_is_mul
  let op_c := sp1_op_c Main cstrs (mul_real Main is_mul) imm
  let op_b := sp1_op_b Main cstrs (mul_real Main is_mul)
  let op_a := sp1_op_a Main cstrs (mul_real Main is_mul)
  (spec_mul (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_mul Main cstrs h_is_mul).run s
  := by
    let ⟨ is_mul, imm ⟩ := h_is_mul
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (mul_real Main is_mul)
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs (mul_real Main is_mul)
    have h_a0 := op_a_is_0 Main cstrs (mul_real Main is_mul)
    have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    simp_all

    simp [SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 trusted_instr_state; simp_all

    simp [spec_mul, sp1_mul, execute, execute_MUL']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_MUL_pure_bv_to_bw _ _ _ (by omega) (by omega)]
      have := spec.mul Main ⟨ is_mul, imm ⟩ cstrs
      simp_all [Word.toBitVec64, Word.toNat]
      rfl

end Mul

namespace Mulh

open Mul

variable
  (Main : Vector (Fin BB) 87)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_mulh : is_mulh Main)

def spec_mulh (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd { high := true, signed_rs1 := true, signed_rs2 := true }
  pure ()

def sp1_mulh : SailM Unit := do
  let ⟨ is_mulh, imm ⟩ := h_is_mulh
  let op_a := sp1_op_a Main cstrs (mulh_real Main is_mulh)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])

theorem correct_mulh
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ is_mulh, imm ⟩ := h_is_mulh
  let op_c := sp1_op_c Main cstrs (mulh_real Main is_mulh) imm
  let op_b := sp1_op_b Main cstrs (mulh_real Main is_mulh)
  let op_a := sp1_op_a Main cstrs (mulh_real Main is_mulh)
  (spec_mulh (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_mulh Main cstrs h_is_mulh).run s
  := by
    let ⟨ is_mulh, imm ⟩ := h_is_mulh
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (mulh_real Main is_mulh)
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs (mulh_real Main is_mulh)
    have h_a0 := op_a_is_0 Main cstrs (mulh_real Main is_mulh)
    have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    simp_all

    simp [SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 trusted_instr_state; simp_all

    simp [spec_mulh, sp1_mulh, execute, execute_MUL']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_MUL_pure_bv_to_bw _ _ _ (by omega) (by omega)]
      have := spec.mulh Main ⟨ is_mulh, imm ⟩ cstrs
      simp_all [Word.toBitVec64, Word.toNat]
      rfl

end Mulh

namespace Mulhu

open Mul

variable
  (Main : Vector (Fin BB) 87)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_mulhu : is_mulhu Main)

def spec_mulhu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd { high := true, signed_rs1 := false, signed_rs2 := false }
  pure ()

def sp1_mulhu : SailM Unit := do
  let ⟨ is_mulhu, imm ⟩ := h_is_mulhu
  let op_a := sp1_op_a Main cstrs (mulhu_real Main is_mulhu)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])

theorem correct_mulh
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ is_mulhu, imm ⟩ := h_is_mulhu
  let op_c := sp1_op_c Main cstrs (mulhu_real Main is_mulhu) imm
  let op_b := sp1_op_b Main cstrs (mulhu_real Main is_mulhu)
  let op_a := sp1_op_a Main cstrs (mulhu_real Main is_mulhu)
  (spec_mulhu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_mulhu Main cstrs h_is_mulhu).run s
  := by
    let ⟨ is_mulhu, imm ⟩ := h_is_mulhu
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (mulhu_real Main is_mulhu)
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs (mulhu_real Main is_mulhu)
    have h_a0 := op_a_is_0 Main cstrs (mulhu_real Main is_mulhu)
    have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    simp_all

    simp [SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 trusted_instr_state; simp_all

    simp [spec_mulhu, sp1_mulhu, execute, execute_MUL']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_MUL_pure_bv_to_bw _ _ _ (by omega) (by omega)]
      have := spec.mulhu Main ⟨ is_mulhu, imm ⟩ cstrs
      simp_all [Word.toBitVec64, Word.toNat]
      rfl

end Mulhu

open Mul

variable
  (Main : Vector (Fin BB) 87)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_mulhsu : is_mulhsu Main)

def spec_mulhsu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd { high := true, signed_rs1 := true, signed_rs2 := false }
  pure ()

def sp1_mulhsu : SailM Unit := do
  let ⟨ is_mulhsu, imm ⟩ := h_is_mulhsu
  let op_a := sp1_op_a Main cstrs (mulhsu_real Main is_mulhsu)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])

theorem correct_mulh
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ is_mulhsu, imm ⟩ := h_is_mulhsu
  let op_c := sp1_op_c Main cstrs (mulhsu_real Main is_mulhsu) imm
  let op_b := sp1_op_b Main cstrs (mulhsu_real Main is_mulhsu)
  let op_a := sp1_op_a Main cstrs (mulhsu_real Main is_mulhsu)
  (spec_mulhsu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_mulhsu Main cstrs h_is_mulhsu).run s
  := by
    let ⟨ is_mulhsu, imm ⟩ := h_is_mulhsu
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (mulhsu_real Main is_mulhsu)
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs (mulhsu_real Main is_mulhsu)
    have h_a0 := op_a_is_0 Main cstrs (mulhsu_real Main is_mulhsu)
    have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    simp_all

    simp [SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 trusted_instr_state; simp_all

    simp [spec_mulhsu, sp1_mulhsu, execute, execute_MUL']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_MUL_pure_bv_to_bw _ _ _ (by omega) (by omega)]
      have := spec.mulhsu Main ⟨ is_mulhsu, imm ⟩ cstrs
      simp_all [Word.toBitVec64, Word.toNat]
      rfl

namespace Mulhsu

end Mulhsu

namespace Mulw

variable
  (Main : Vector (Fin BB) 87)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_mulw : is_mulw Main)

def spec_mulw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MULW rs2 rs1 rd
  pure ()

def sp1_mulw : SailM Unit := do
  let ⟨ is_mulw, imm ⟩ := h_is_mulw
  let op_a := sp1_op_a Main cstrs (mulw_real Main is_mulw)
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])

theorem correct_mulw
  (state_cstrs : (constraints Main).initialState s) :
  let ⟨ is_mulw, imm ⟩ := h_is_mulw
  let op_c := sp1_op_c Main cstrs (mulw_real Main is_mulw) imm
  let op_b := sp1_op_b Main cstrs (mulw_real Main is_mulw)
  let op_a := sp1_op_a Main cstrs (mulw_real Main is_mulw)
  (spec_mulw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_mulw Main cstrs h_is_mulw).run s
  := by
    let ⟨ is_mulw, imm ⟩ := h_is_mulw
    have ⟨ ha, hb, hc, hpc ⟩ := register_bounds Main cstrs (mulw_real Main is_mulw)
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs (mulw_real Main is_mulw)
    have h_a0 := op_a_is_0 Main cstrs (mulw_real Main is_mulw)
    have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
    simp_all

    simp [constraints] at state_cstrs
    simp_all

    simp [SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨thr1, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear thr1 trusted_instr_state; simp_all

    simp [spec_mulw, sp1_mulw, execute, execute_MULW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_MULW_pure_bv_to_bw _ _ (by omega) (by omega)]
      have := spec.mulw Main ⟨ is_mulw, imm ⟩ cstrs
      simp_all [Word.toBitVec64, Word.toNat]
      rfl

end Mulw
