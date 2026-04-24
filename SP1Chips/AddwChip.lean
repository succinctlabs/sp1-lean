import SP1Operations.Operation.AddwOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Addw.Constraints

open LeanRV64D.Functions
open BitVec

namespace Addw

variable
  (Main : Vector (Fin KB) 36)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[35] = 1)
  (h_is_addw : Main[31] = 0)

def spec_addw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.ADDW
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21]

def sp1_addw : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535])

set_option maxHeartbeats 1000000 in

-- correctness proof across instruction arms
-- Pre-regen proof at commit 750a3e6:SP1Chips/AddwChip.lean -- correct_addw
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/AddwChip.lean` for the full pre-regen proof body)
theorem correct_addw
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[35] = 1)
  (h_is_addw : Main[31] = 0)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_addw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addw Main).run s
  := by
    simp [constraints] at cstrs
    obtain ⟨addw_op_cstrs, cpu_cstrs, alu_cstrs, _⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨ trusted_instr_prop, _, _, _, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, is_U64_c , _, _ ⟩ := alu_cstrs
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      AddwOperation.constraints, CPUState.constraints, ALUTypeReader.constraints, U16MSBOperation.constraints,
      h_is_real] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    simp [Opcode.ofNat, Nat.ble] at *
    simp_all

end Addw

namespace Addiw

open Addw

variable
  (Main : Vector (Fin KB) 36)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[35] = 1)
  (h_is_addiw : Main[31] = 1)

def spec_addiw (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ADDIW imm rs1 rd
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21]

def sp1_addiw : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535])

set_option maxHeartbeats 1000000 in

-- correctness proof across instruction arms
-- Pre-regen proof at commit 750a3e6:SP1Chips/AddwChip.lean -- correct_addw
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/AddwChip.lean` for the full pre-regen proof body)
theorem correct_addw
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[35] = 1)
  (h_is_addiw : Main[31] = 1)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_addiw op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addiw Main).run s
  := by
    simp [constraints] at cstrs
    obtain ⟨addw_op_cstrs, cpu_cstrs, alu_cstrs, _ ⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real h_is_real] at alu_cstrs
    obtain ⟨ trusted_instr_prop, _, _, ⟨ c0, c1, c2, c3 ⟩, _, _, _, _, _, _, _, _, _, _, _, is_U64_a, is_U64_b, _, _, _ ⟩ := alu_cstrs
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddwOperation.constraints, CPUState.constraints, ALUTypeReader.constraints, U16MSBOperation.constraints, h_is_real] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    sorry

end Addiw
