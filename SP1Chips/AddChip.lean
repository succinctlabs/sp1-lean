import SP1Foundations
import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
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

def sp1_add : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  -- TODO(gzgz): we can obtain this from the constraint compiler
  -- This comes from the Interaction.state in CPUState
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  SailState.write_reg op_a (Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]])

theorem correct
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_add (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_add Main cstrs h_is_real).run s
  := by
    -- Obtain and simplify state and pure constraints
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, CPUState.constraints, RTypeReader.constraints, h_is_real] at state_cstrs
    obtain ⟨read_pc, trusted_instr_state, _, read_op_b, read_op_c⟩ := state_cstrs
    simp [constraints] at cstrs
    obtain ⟨add_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs
    apply AddOperation.correct (h_is_real := h_is_real) at add_op_cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [RTypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs
    obtain ⟨ trusted_instr_prop, _, _, _, _, _, _, ⟨ ⟨ _, _, ⟨ _, is_U64_b, is_U64_c ⟩ ⟩, _ ⟩⟩ := reader_cstrs
    simp [Opcode.ofNat, Nat.ble] at trusted_instr_state trusted_instr_prop
    specialize add_op_cstrs is_U64_b is_U64_c
    obtain ⟨ is_U64_val, is_add ⟩ := add_op_cstrs
    simp at *

    -- Now the monadic manipulation
    simp [spec_add, sp1_add, execute_RTYPE]
    rw [run_readReg, read_pc]; simp
    simp [run_rX_bits, sp1_op_b, read_op_b (by omega)]
    simp [run_rX_bits, sp1_op_c, read_op_c (by omega)]
    simp [run_wX_bits, sp1_op_a]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . rw [← is_add]
      simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Add
