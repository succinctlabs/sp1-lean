import SP1Operations.Operation.SubwOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.Subw.Constraints

open LeanRV64D.Functions
open BitVec

namespace Subw

variable
  (Main : Vector (Fin BB) 32)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[31] = 1)

def spec_subw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SUBW
  pure ()

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    simp
    show Main[6] < 32

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [RTypeReader.allHold_constraints_iff_is_real (h := h_is_real), Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

    exact reader_cstrs.2.1

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp
    show Main[14] < 32

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [RTypeReader.allHold_constraints_iff_is_real (h := h_is_real), Opcode.ofNat, Nat.ble] at reader_cstrs

    exact reader_cstrs.1.1

def sp1_op_c : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[21] ?_
    simp
    show Main[21] < 32

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [RTypeReader.allHold_constraints_iff_is_real (h := h_is_real), Opcode.ofNat, Nat.ble] at reader_cstrs

    exact reader_cstrs.1.2

def sp1_subw : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[28], Main[29], Main[30] * 65535, Main[30] * 65535])

set_option maxHeartbeats 1000000 in
theorem correct_subw
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_subw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_subw Main cstrs h_is_real).run s
  := by
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, SubwOperation.constraints, CPUState.constraints, RTypeReader.constraints, U16MSBOperation.constraints, h_is_real] at state_cstrs
    obtain ⟨read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    simp [constraints] at cstrs
    obtain ⟨subw_op_cstrs, cpu_cstrs, reader_cstrs, _⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [RTypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs
    obtain ⟨ trusted_instr_prop, _, _, _, _, _, _, ⟨ ⟨ _, _, ⟨ _, is_U64_b, is_U64_c ⟩ ⟩, _ ⟩⟩ := reader_cstrs
    simp [Opcode.ofNat, Nat.ble] at *
    simp_all

    rw [h_is_real] at *
    apply SubwOperation.spec is_U64_b is_U64_c at subw_op_cstrs
    obtain ⟨ is_U32_val, is_subw, is_msb ⟩ := subw_op_cstrs
    simp_all

    -- Now the monadic manipulation
    simp [spec_subw, sp1_subw, execute, execute_RTYPEW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [exec_RTYPEW_pure_bv_to_w _ _ _ (by omega) (by omega)]
    simp [execute_RTYPEW_pure_w]
    rw [← is_subw] at is_msb
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [Word.toBitVec64, Word.toNat]
      rw [← is_subw]; congr
      rw [HWord.sign_extend_32_to_64_msb is_U32_val]
      simp [Word.toBitVec64, Word.toNat]

end Subw
