import SP1Operations
import LeanRV64IM.RiscvInstsEnd

import SP1Chips.Add.Constraints

open LeanRV64IM.Functions
open BitVec

namespace Add

variable
  (Main : Vector (Fin BB) 33)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[32] = 1)

def spec_add (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

def sp1_op_c : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[21] ?_
    simp
    show Main[21] < 32

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1
    
    clear cstrs
    simp [RTypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

    exact reader_cstrs.1.1.2

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp
    show Main[14] < 32

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1
    
    clear cstrs
    simp [RTypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

    exact reader_cstrs.1.1.1

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    simp
    show Main[6] < 32

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1
    
    clear cstrs
    simp [RTypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

    exact reader_cstrs.1.2.1

def sp1_add : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  SailState.write_reg op_a (Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]])
  -- TODO(gzgz): we can obtain this from the constraint compiler
  -- This comes from the Interaction.state in CPUState
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])

def correct
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_add (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_add Main cstrs h_is_real).run s
  := by
    sorry

end Add
