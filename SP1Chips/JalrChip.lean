import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Jalr.Constraints

namespace Jalr

open Sail SailState BitVec LeanRV64D.Functions

attribute [simp] jump_to ofBool
  update updateSubrange'
  assert PreSail.assert
  LeanRV64D.Functions.RETIRE_SUCCESS

variable (Main : Vector (Fin KB) 39) (s : SailState)

def sp1_op_a (Main : Vector (Fin KB) 39) : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b (Main : Vector (Fin KB) 39) : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_op_c (Main : Vector (Fin KB) 39) : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_jalr (Main : Vector (Fin KB) 39) : SailM Unit := do
  let op_a := sp1_op_a Main
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[31], Main[32], Main[33], Main[34]])
  wX_bits (.Regidx op_a) (Word.toBitVec64 #v[Main[35], Main[36], Main[37], Main[38]])

noncomputable def spec_jalr (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  writeReg Register.nextPC ((← readReg Register.PC) + 4#64)
  _ ← execute_JALR imm rs1 rd

set_option maxHeartbeats 10000000 in
theorem JALR_correct
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1)
    (hs : isInitialized s)
    -- Write value is a valid PC value. This can be proved from constraints on newest sp1 branch
    (h_valid_pc : (Main[15].val + Main[21].val) % 4 = 0)
    (state_cstrs : (constraints Main).initialState s) :
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    let op_c := sp1_op_c Main
    (spec_jalr op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_jalr Main).run s := by
  extract_lets op_c op_b op_a

  -- pull out constraints
  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp, h_is_real] at cstrs
  obtain ⟨res_cstrs, ⟨pc_cstrs, ⟨reader_cstrs, ⟨inc_pc_cstrs, chip_cstrs⟩⟩⟩⟩ := cstrs
  simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq,
    SP1Constraint.toProp, sub_eq_zero] at reader_cstrs

  have h25 : Main[25] = 1 := (reader_cstrs.2.2.1).resolve_right (by decide) |>.symm
  have h6 : Main[6] < 32 := (reader_cstrs.2.2.2.1 (by rw [h25]; decide)).2.1
  have h14 : Main[14] < 32 := (reader_cstrs.2.2.2.1 (by rw [h25]; decide)).1.1

  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    AddOperation.constraints, ITypeReader.constraints, CPUState.constraints,
    h_is_real, h6, h14] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b⟩ := state_cstrs
  simp [h25] at reader_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at read_op_a read_op_b

  have h_sign_extend : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
    BitVec.signExtend 64 (BitVec.ofNat 12 Main[21]) := by aesop
  have hmod4' : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]) % 4 = 0 := by
    clear *- h_valid_pc; simpa [← BitVec.toNat_inj]

  have h15 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
    clear *- reader_cstrs; aesop
  have h22 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    clear *- reader_cstrs; apply Word.isU64_of_cases <;> aesop
  have hu64pc : Word.isU64 #v[Main[3], Main[4], Main[5], 0] := by
    clear *- reader_cstrs; apply Word.isU64_of_cases <;> aesop
  have h_add := AddOperation.spec h15 h22 res_cstrs

  simp [spec_jalr, sp1_jalr, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, cond, execute_JALR,
    op_a, op_b, op_c, sp1_op_a, sp1_op_b, sp1_op_c, read_op_a, read_op_b,
    ← h_sign_extend, (mul4_means_0_1_are_0 hmod4').2]
  stop
  rw [run_readReg_of_isInitialized _ _ (by aesop)]
  rw [twoPow64_and_eq_self hmod4']

  by_cases h6 : BitVec.ofNat 5 Main[6] = 0#5
  · simp [h_add, h6]
  · have h6' : Main[6] ≠ 0 := by clear *- h6; aesop
    have h13 : Main[13] = 0 := by clear *- reader_cstrs h6'; aesop
    simp [h13] at *

    have h_inc_pc := AddOperation.spec hu64pc (by aesop) inc_pc_cstrs
    simp [execute_RTYPE_pure_w] at h_inc_pc

    simp [Std.ExtDHashMap.get_eq_get_get?, read_pc, h_add, h_inc_pc]
    simp [Word.toBitVec64, Word.toNat]

end Jalr
