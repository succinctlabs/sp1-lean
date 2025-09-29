import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Addi.Constraints

import SP1Chips.Add.Constraints

open LeanRV64D.Functions BitVec

namespace Addi

variable
  (Main : Vector (Fin KB) 31)
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
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[26], Main[27], Main[28], Main[29]])

open Sail

theorem correct_addi
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[30] = 1)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_addi op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addi Main).run s
  := by
    -- Obtain and simplify state and pure constraints
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, CPUState.constraints, ITypeReader.constraints, h_is_real] at state_cstrs
    obtain ⟨read_pc, trusted_instr_state, read_op_b, read_op_c⟩ := state_cstrs
    simp [constraints] at cstrs
    obtain ⟨add_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ITypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs

    obtain ⟨ _, trusted_instr_prop, hcm1, hcm2, c0, c1, c2, c3, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, ⟨ is_U64_a, is_U64_b, hu64 ⟩⟩ := reader_cstrs

    simp_all [Opcode.ofNat, Nat.ble]
    have is_U64_c : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]]
      := by apply Word.isU64_of_cases c0 c1 c2 c3

    rw [h_is_real] at *
    apply AddOperation.spec is_U64_b is_U64_c at add_op_cstrs
    obtain ⟨ is_U64_val, is_add ⟩ := add_op_cstrs
    simp at *
    simp [BitVec.ofNatLT_eq_ofNat] at *
    -- Now the monadic manipulation
    simp [spec_addi, sp1_addi, execute, execute_ITYPE]
    rw [run_readReg, read_pc]
    simp [sp1_op_b, read_op_b]
    simp [sp1_op_c, read_op_c]
    simp [sp1_op_a]
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0
    .
      have : Main[13] = 1 := by clear *- h12 h_is_op_a_0; aesop --sorry --aesop
      rw [← is_add] at *
      simp [Word.toBitVec64, Word.toNat, h_is_op_a_0]
      clear *- this hu64
      aesop
    . rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [is_add, trusted_instr_prop.2]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Addi
