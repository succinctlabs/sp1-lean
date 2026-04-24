import SP1Operations.Operation.SubwOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.Subw.Constraints

open LeanRV64D.Functions
open BitVec

namespace Subw

variable
  (Main : Vector (Fin KB) 32)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[31] = 1)

def spec_subw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SUBW
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21]

def sp1_subw : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[28], Main[29], Main[30] * 65535, Main[30] * 65535])

set_option maxHeartbeats 1000000 in

-- correctness proof across instruction arms
theorem correct_subw
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[31] = 1)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_subw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_subw Main).run s
  := by
    simp [constraints] at cstrs
    obtain ⟨subw_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [RTypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs
    obtain ⟨ trusted_instr_prop, _, _, _, _, _, _, ⟨ ⟨ _, _, ⟨ _, is_U64_b, is_U64_c ⟩ ⟩, _ ⟩⟩ := reader_cstrs
    simp only [Opcode.ofNat, Nat.ble] at trusted_instr_prop
    have h6 : Main[6] < 32 := by aesop
    have h14 : Main[14] < 32 := by aesop
    have h21 : Main[21] < 32 := by aesop
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
      SubwOperation.constraints, CPUState.constraints, RTypeReader.constraints,
      U16MSBOperation.constraints, h6, h14, h21, h_is_real] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear rest
    rw [h_is_real] at *
    apply SubwOperation.spec is_U64_b is_U64_c at subw_op_cstrs
    obtain ⟨ is_U32_val, is_subw, is_msb ⟩ := subw_op_cstrs
    simp_all

end Subw
