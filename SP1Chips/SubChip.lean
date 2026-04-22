import SP1Foundations
import SP1Operations.Operation.SubOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader

import SP1Chips.Sub.Constraints

open LeanRV64D.Functions BitVec

namespace Sub

variable
  (Main : Vector (Fin KB) 34)
  (s : SailState)

noncomputable def spec_sub (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SUB
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21]

def sp1_sub : SailM Unit := do
  let op_a := sp1_op_a Main --cstrs h_is_real
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]])

open Sail

theorem correct_sub
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[33] = 1)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_sub (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sub Main ).run s
  := by
    simp [constraints] at cstrs
    obtain ⟨sub_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    simp [RTypeReader.allHold_constraints_iff_is_real h_is_real,
      Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
    obtain ⟨ _, trusted_instr_prop, _, _, _, _, _, _, ⟨ ⟨ _, _, ⟨ _, is_U64_b, is_U64_c ⟩ ⟩, _ ⟩⟩ := reader_cstrs
    have h6 : Main[6] < 32 := by aesop
    have h14 : Main[14] < 32 := by aesop
    have h21 : Main[21] < 32 := by aesop
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
      List.Forall, SubOperation.constraints, CPUState.constraints, RTypeReader.constraints,
      h6, h14, h21, h_is_real] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    rw [h_is_real] at *
    apply SubOperation.spec is_U64_b is_U64_c at sub_op_cstrs
    obtain ⟨ is_U64_val, is_sub ⟩ := sub_op_cstrs
    simp [BitVec.ofNatLT_eq_ofNat] at *
    -- Now the monadic manipulation
    simp [spec_sub, sp1_sub, execute, execute_RTYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_b, read_op_b]
    simp [sp1_op_c, read_op_c]
    simp [sp1_op_a]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . rw [← is_sub]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp
      rfl

end Sub
