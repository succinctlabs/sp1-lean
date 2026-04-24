import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Addi.Constraints

import SP1Chips.Add.Constraints

open LeanRV64D.Functions BitVec

namespace Addi

variable
  (Main : Vector (Fin KB) 30)
  (s : SailState)

noncomputable def spec_addi (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.ADDI
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21]

def sp1_addi : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]])

open Sail

theorem correct_addi
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[29] = 1)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_addi op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addi Main).run s
  := by
    -- Obtain and simplify state and pure constraints
    simp [constraints] at cstrs
    obtain ⟨add_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ITypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs
    simp [Opcode.ofNat, Nat.ble] at reader_cstrs
    obtain ⟨ trusted_instr_prop, hcm1, hcm2, c0, c1, c2, c3, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, ⟨ is_U64_a, is_U64_b, hu64 ⟩⟩ := reader_cstrs
    have h6 : Main[6] < 32 := by aesop
    have h14 : Main[14] < 32 := by aesop
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
      List.Forall, AddOperation.constraints, CPUState.constraints, ITypeReader.constraints,
      h6, h14, h_is_real] at state_cstrs
    obtain ⟨read_pc, read_op_b, read_op_c⟩ := state_cstrs
    clear rest
    simp_all
    have is_U64_c : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]]
      := by apply Word.isU64_of_cases c0 c1 c2 c3
    rw [h_is_real] at *
    apply AddOperation.spec is_U64_b is_U64_c at add_op_cstrs
    obtain ⟨ is_U64_val, is_add ⟩ := add_op_cstrs
    simp at *
    simp [BitVec.ofNatLT_eq_ofNat] at *
    -- Now the monadic manipulation
    simp [spec_addi, sp1_addi, execute_ITYPE]
    rw [run_readReg, read_pc]
    simp [sp1_op_b]
    simp [sp1_op_c, read_op_c]
    simp [sp1_op_a]
    by_cases h_is_op_a_0 : Main[6] = 0
    · have : Main[13] = 1 := by clear *- h12 h_is_op_a_0; aesop
      rw [← is_add] at *
      simp [Word.toBitVec64, Word.toNat, h_is_op_a_0]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
      clear *- this hu64
      aesop
    · rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [is_add, trusted_instr_prop]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
      simp
      rfl

end Addi
