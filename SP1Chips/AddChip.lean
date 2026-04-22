import SP1Chips.Add.Constraints

open LeanRV64D.Functions

namespace Add

variable (Main : Vector (Fin KB) 34)

-- The input and output values in the SP1 implementation
def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]
def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]
def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21]

/-- Specification of the ADD operation in sail, while setting the next program counter-/
def spec_add (rs2 rs1 rd : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_RTYPE rs2 rs1 rd rop.ADD

/-- Behavior of the ADD operation in SP1, writing the given values to registers-/
def sp1_add : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg (sp1_op_a Main) (Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]])
  return RETIRE_SUCCESS

open Sail

/-- Given that all the constraints hold for the input `Main`, `s` is a machine state with
registers initialized to appropriate values, and the column is a real column,
the Sail spec and SP1 implementation behave the same. -/
theorem correct_add
    (Main : Vector (Fin KB) 34)
    (s : SailState)
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[33] = 1)
    (state_cstrs : (constraints Main).initialState s) :
    let op_c := .Regidx (sp1_op_c Main)
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_add op_c op_b op_a).run s = (sp1_add Main).run s := by
  -- Simplify the main constraints and split them into parts
  simp [constraints] at h_cstrs
  obtain ⟨add_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := h_cstrs
  rw [CPUState.allHold_constraints_iff_is_real h_is_real] at cpu_cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs
  simp [Opcode.ofNat, Nat.ble] at reader_cstrs

  -- Show the write values are all register values (i.e. are 5-bit)
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h21 : Main[21] < 32 := by aesop

  -- Extract constraints about the initial register states
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
    List.Forall, AddOperation.constraints, CPUState.constraints, BitVec.ofNatLT_eq_ofNat,
    RTypeReader.constraints, h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs

  rw [h_is_real] at *
  apply AddOperation.spec (by aesop) (by aesop) at add_op_cstrs
  obtain ⟨ is_U64_val, is_add ⟩ := add_op_cstrs

  -- Simplify the monadic operations
  simp [spec_add, sp1_add, execute_RTYPE']
  rw [run_readReg, read_pc]
  simp [sp1_op_b, read_op_b, sp1_op_c, read_op_c, sp1_op_a]

  -- Simplify the expressions using the arithmetic constraints
  by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
  . rw [← is_add]
    simp [Word.toBitVec64, Word.toNat]
    exact Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)
  . rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
    rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
    simp [Word.toBitVec64, Word.toNat]
    rw [Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)]
    simp
    rfl

end Add
