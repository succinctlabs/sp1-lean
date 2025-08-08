import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Jalr.Constraints

namespace Jalr

open Sail SailState BitVec LeanRV64IM.Functions

variable (Main : Vector (Fin BB) 38) (s : SailState)

lemma op_a_lt32_of_constraints {Main : Vector (Fin BB) 38} (h : (constraints Main).allHold)
    (h_is_real : Main[29] = 1) : Main[6].val < 2^5 := by
  simp only [BB_eq, Nat.reducePow]
  have reader_cstrs := by
    simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at h
    exact h.2.2.1
  simp [ITypeReader.constraints, h_is_real, Opcode.ofNat,
    Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs
  aesop

lemma op_b_lt32_of_constraints {Main : Vector (Fin BB) 38} (h : (constraints Main).allHold)
    (h_is_real : Main[29] = 1) : Main[14].val < 2^5 := by
  simp only [BB_eq, Nat.reducePow]
  have reader_cstrs := by
    simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at h
    exact h.2.2.1
  simp [ITypeReader.constraints, h_is_real, Opcode.ofNat,
    Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs
  aesop

def sp1_op_a (cstrs : (constraints Main).allHold) (h_is_real : Main[29] = 1) : BitVec 5 :=
  Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)

-- dt: could instead put `Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]]` here...
def sp1_op_b (cstrs : (constraints Main).allHold) (h_is_real : Main[29] = 1): BitVec 5 :=
  Main[14].val#'(op_b_lt32_of_constraints cstrs h_is_real)

-- dt: could instead put `Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]` here...
def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_jalr  (cstrs : (constraints Main).allHold) (h_is_real : Main[29] = 1): SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  wX_bits (.Regidx op_a) (Word.toBitVec64 #v[Main[34], Main[35], Main[36], Main[37]])
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[30], Main[31], Main[32], Main[33]])

def spec_jalr (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  writeReg Register.nextPC ((← readReg Register.PC) + 4#64)
  _ ← execute_JALR imm rs1 rd

theorem JALR_correct
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[29] = 1)
    (state_cstrs : (constraints Main).initialState s)
    (h_misa : Register.misa ∈ s.regs) :
    let op_b := sp1_op_b Main cstrs h_is_real
    let op_a := sp1_op_a Main cstrs h_is_real
    let op_c := sp1_op_c Main
    (spec_jalr op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_jalr Main cstrs h_is_real).run s := by
  extract_lets op_c op_b op_a

  -- pull out state constraints about the contents of register and pc reads
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, ITypeReader.constraints, CPUState.constraints, h_is_real] at state_cstrs
  obtain ⟨read_pc, ⟨op_b_val_plus_imm_mul4, ⟨read_op_a, read_op_b⟩⟩⟩ := state_cstrs

  -- pull out constraints
  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
  obtain ⟨res_cstrs, ⟨pc_cstrs, ⟨reader_cstrs, ⟨inc_pc_cstrs, chip_cstrs⟩⟩⟩⟩ := cstrs

  simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs
  obtain ⟨⟨h_op_b, h_c_sign_extend⟩, ⟨h_op_a, ⟨_, ⟨⟨h_c_0, ⟨h_c_1, ⟨h_c_2, h_c_3⟩⟩⟩, ⟨op_a_0_is_bool, ⟨op_a_0_iff_op_a_is_0, ⟨pc_mul_4, ⟨h_pc_0, ⟨h_pc_1, h_pc_2⟩⟩⟩⟩⟩⟩⟩⟩⟩ := reader_cstrs.1
  simp [h_op_b] at read_op_b
  simp [h_op_a] at read_op_a

  have b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := reader_cstrs.2.2.2.2.2.2.2.2.2.2
  let b_bv64 : BitVec 64 := Word.toBitVec64LT #v[Main[15], Main[16], Main[17], Main[18]] b_is_u64

  have imm_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    refine Word.isU64_of_cases #v[Main[21], Main[22], Main[23], Main[24]] h_c_0 h_c_1 h_c_2 h_c_3

  have pc_is_u64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] := by
    exact Word.isU64_of_cases #v[Main[3], Main[4], Main[5], 0] h_pc_0 h_pc_1 h_pc_2 (by simp)

  have ⟨res_is_u64, h_res⟩ := (AddOperation.correct #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[30], Main[31], Main[32], Main[33]] } Main[29] h_is_real res_cstrs) b_is_u64 imm_is_u64

  have h_4_is_u64 : Word.isU64 #v[4,0,0,0] :=
    Word.isU64_of_cases _ (by trivial) (by trivial) (by trivial) (by trivial)

  have hmod : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]) % 4 = 0 := by
    rw [BitVec.ofNatLT_eq_ofNat] at read_op_b
    rw [read_op_b] at op_b_val_plus_imm_mul4
    simpa using op_b_val_plus_imm_mul4

  have hmod4 : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]])[1] = false := by
    refine (mul4_means_0_1_are_0 ?_).2
    simpa using hmod

  clear res_cstrs reader_cstrs pc_cstrs

  simp [spec_jalr, sp1_jalr, execute_JALR, op_a, op_b, op_c,
    sp1_op_a, sp1_op_b, sp1_op_c, EStateM.run_bind]
  rw [run_readReg] -- `simp` refuses to apply this itself
  simp only [read_pc, hmod4, read_op_b, run_rX_bits, get_reg?_insert_nextPC, ext_control_check_addr,
    Sail.BitVec.access, bit_to_bool, Sail.BitVec.update, Sail.BitVec.updateSubrange',
    bits_of_virtaddr, BitVec.reduceAllOnes, BitVec.truncate_eq_setWidth, BitVec.reduceSetWidth,
    BitVec.shiftLeft_zero, BitVec.reduceNot, BitVec.setWidth_zero, BitVec.or_zero,
    Nat.one_lt_ofNat, getElem!_pos, BitVec.getElem_and, BitVec.reduceGetElem, Bool.true_and,
    BitVec.ofBool, BitVec.ofNat_eq_ofNat, cond_false, EStateM.run_bind,
    run_bool_bit_backwards, Bool.false_and, EStateM.run_map, run_writeReg, EStateM.Result.map_ok,
    currentlyEnabled, hartSupports, Bool.false_and, Bool.false_or, Bool.and_self,
    BitVec.ofNat_eq_ofNat, bind_pure_comp, Functor.map_map, EStateM.run_map,
    sign_extend, Sail.BitVec.signExtend, ← h_c_sign_extend, Nat.shiftLeft_eq]
  rw [map_const_run_readReg _ _ (by simp [h_misa])]
  simp
  rw [run_readReg]
  simp only [Std.ExtDHashMap.get?_insert_self, run_wX_bits, BitVec.ofNat_eq_ofNat, EStateM.Result.map_ok]

  split_ifs with h6 <;> simp [BitVec.twoPow64_and_eq_self hmod, h_res]
  refine congr_fun ?_ _
  have htemp : Main[29] - Main[13] = 1 := by
    simp [h_is_real] at chip_cstrs
    simp [← BitVec.toNat_inj] at h6
    simp [h6] at op_a_0_iff_op_a_is_0
    simp [op_a_0_iff_op_a_is_0] at op_a_0_is_bool
    simp [op_a_0_is_bool, h_is_real]
  have ⟨ _, h_add ⟩ := AddOperation.correct _ _ _ _ htemp inc_pc_cstrs pc_is_u64 h_4_is_u64
  rw [h_add]
  simp [Word.toBitVec64, Word.toNat, Nat.shiftLeft_eq]

end Jalr
