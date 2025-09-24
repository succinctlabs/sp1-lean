import SP1Foundations
import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import LeanRV64D.RiscvInstsEnd

import SP1Chips.Add.Constraints

open LeanRV64D.Functions BitVec

namespace Add

variable
  (Main : Vector (Fin KB) 34)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[33] = 1)

noncomputable def spec_add (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21]

def sp1_add : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]])

open Sail

set_option pp.parens true in
theorem correct_add
  (Main : Vector (Fin KB) 34)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[33] = 1)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_add (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_add Main).run s
  := by
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, CPUState.constraints, RTypeReader.constraints] at state_cstrs
    obtain ⟨read_pc, trusted_instr_state, _, read_op_b, read_op_c⟩ := state_cstrs
    simp [constraints] at cstrs
    obtain ⟨add_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [RTypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs
    simp [Opcode.ofNat, Nat.ble] at reader_cstrs
    obtain ⟨ trusted_instr_prop, _, _, _, _, _, _, _, ⟨ ⟨ _, _, ⟨ _, is_U64_b, is_U64_c ⟩ ⟩, _ ⟩⟩ := reader_cstrs
    simp [Opcode.ofNat, Nat.ble] at trusted_instr_state trusted_instr_prop

    rw [h_is_real] at *
    apply AddOperation.spec is_U64_b is_U64_c at add_op_cstrs
    obtain ⟨ is_U64_val, is_add ⟩ := add_op_cstrs
    simp [BitVec.ofNatLT_eq_ofNat] at *

    -- Now the monadic manipulation
    simp [spec_add, sp1_add, execute, execute_RTYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_b, read_op_b (by omega)]
    simp [sp1_op_c, read_op_c (by omega)]
    simp [sp1_op_a]
    rw [KoalaBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . rw [← is_add]
      simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Add
