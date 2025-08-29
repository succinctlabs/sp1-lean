import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Addi.Constraints

import SP1Chips.Add.Constraints

open LeanRV64D.Functions BitVec

namespace Addi

variable
  (Main : Vector (Fin BB) 30)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[29] = 1)

noncomputable def spec_addi (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.ADDI
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
    simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

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
    simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

    exact reader_cstrs.1.1.1

def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_addi : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]])

open Sail

theorem correct_addi
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_addi op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addi Main cstrs h_is_real).run s
  := by
    -- Obtain and simplify state and pure constraints
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, CPUState.constraints, ITypeReader.constraints, h_is_real] at state_cstrs
    obtain ⟨read_pc, trusted_instr_state, read_op_b, read_op_c⟩ := state_cstrs
    simp [constraints] at cstrs
    obtain ⟨add_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
    rw [ITypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs
    obtain ⟨ trusted_instr_prop, _, _, c0, c1, c2, c3, _, _, _, _, _, _, _, _, _, _, ⟨ is_U64_a, is_U64_b, _ ⟩⟩ := reader_cstrs
    simp_all [Opcode.ofNat, Nat.ble]
    have is_U64_c : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]]
      := by apply Word.isU64_of_cases c0 c1 c2 c3

    rw [h_is_real] at *
    apply AddOperation.spec is_U64_b is_U64_c at add_op_cstrs
    obtain ⟨ is_U64_val, is_add ⟩ := add_op_cstrs
    simp at *

    -- Now the monadic manipulation
    simp [spec_addi, sp1_addi, execute, execute_ITYPE]
    rw [run_readReg, read_pc]
    simp [sp1_op_b, read_op_b]
    simp [sp1_op_c, read_op_c]
    simp [sp1_op_a]
    rw [BabyBear.add4_into_pc_ofNat (by omega)]

    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . rw [← is_add]
      simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Addi
