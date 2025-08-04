import SP1Operations.Operation.AddOperation
import SP1Chips.Jal.Constraints

namespace JalChip

open BitVec

open Sail SailState BitVec LeanRV64IM.Functions

variable (Main : Vector (Fin BB) 31) (s : SailState)

lemma op_a_lt32_of_constraints {Main : Vector (Fin BB) 31}
    (h_cstrs : (constraints Main).allHold) (h_is_real : Main[30] = 1) : Main[6].val < 32 := by
  simp only [BB_eq, Nat.reducePow]
  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at h_cstrs
  have h : Main[6] < 32 := by simp_all only [BB_eq, Fin.isValue, one_ne_zero, sub_self,
    or_true, not_false_eq_true, forall_const, true_or, true_and]
  simp_all only [BB_eq, Fin.isValue, gt_iff_lt]
  exact h

def sp1_op_a (cstrs : (constraints Main).allHold) (h_is_real : Main[30] = 1) : BitVec 5 :=
  Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)

-- dt: could instead put `Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]]` here...
def sp1_op_b : BitVec 21 := BitVec.ofNat 21 (Main[14].val + Main[15].val * 65536)

def sp1_jal (Main : Vector (Fin BB) 31) : SailM Unit := do
  let op_a := regidx.Regidx Main[6].val
  wX_bits op_a (BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48))
  set_next_pc (BitVec.ofNat 64 (Main[22] + Main[23] * 2^16 + Main[24] * 2^32 + Main[25] * 2^48))

def spec_jal (imm : BitVec 21) (rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_JAL imm rd

set_option debug.skipKernelTC true in
theorem SP1JAL_correct
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1)
    (state_cstrs : (constraints Main).initialState s)
    (h_misa : Register.misa ∈ s.regs) :
    let op_a := sp1_op_a Main cstrs h_is_real
    let op_b := sp1_op_b Main
    (spec_jal op_b (.Regidx op_a)).run s = (sp1_jal Main).run s := by
  extract_lets op_a op_b

  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, h_is_real] at state_cstrs
  obtain ⟨read_pc, h⟩ := state_cstrs

  have h_op_a : Main[6].val < 32 := op_a_lt32_of_constraints cstrs h_is_real
  specialize h (by aesop)

  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp, sub_eq_zero,
    h_is_real, Fin.isValue, BB_eq, true_and] at cstrs

  have h_sign_extend : Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]] =
      BitVec.signExtend 64 (BitVec.ofNat 21 (↑Main[14] + ↑Main[15] * 65536)) := by
    simp_all only

  have hpc : BitVec.ofNat 64 (↑Main[3] + ↑Main[4] * 65536 + ↑Main[5] * 4294967296) =
      Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] := by simp [Word.toBitVec64, Word.toNat]

  have hmod : (BitVec.ofNat 64 (↑Main[3] + ↑Main[4] * 65536 + ↑Main[5] * 4294967296) +
      Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]])[1] = false := by
    refine (mul4_means_0_1_are_0 ?_).2

    simp [hpc]
    refine add_mod4_eq_zero_of_mod4_eq_zero ?_ ?_
    · simp [ofNat_eq_ofNat, BabyBear.val_mod4_eq_zero]
      simp_all only [BB_eq, Fin.isValue, true_and]
    · simp only [ofNat_eq_ofNat, ofNat64_mod_4_eq_zero_iff]
      simp_all only [BB_eq, Fin.isValue, true_and]

  have h_add_imm : List.Forall SP1Constraint.toProp (AddOperation.constraints
      #v[Main[3], Main[4], Main[5], 0]
      #v[Main[14], Main[15], Main[16], Main[17]]
      {value := #v[Main[22], Main[23], Main[24], Main[25]]} 1) := by
    simp_all only [Fin.isValue, BB_eq, true_and]
    simp_all only [Fin.isValue, _root_.and_self, and_true, true_and, or_true]

  have h3 : Main[3] < 65536 := by simp_all only
  have h4 : Main[4] < 65536 := by simp_all only
  have h5 : Main[5] < 65536 := by simp_all only
  have h14 : Main[14] < 65536 := by simp_all only
  have h15 : Main[15] < 65536 := by simp_all only
  have h16 : Main[16] < 65536 := by simp_all only
  have h17 : Main[17] < 65536 := by simp_all only
  have pc_isU64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] :=
    Word.isU64_of_cases _ h3 h4 h5 (by simp)
  have imm_isU64 : Word.isU64 #v[Main[14], Main[15], Main[16], Main[17]] := by
    refine Word.isU64_of_cases _ h14 h15 h16 h17

  have h_add' := (AddOperation.correct _ _ _  _ rfl h_add_imm pc_isU64 imm_isU64).2
  simp [Word.toBitVec64, Word.toNat] at h_add'


  simp only [spec_jal, sp1_jal, execute_JAL, op_a, op_b, sp1_op_b, sp1_op_a]

  rw [EStateM.run_bind, run_readReg, read_pc]
  simp only
  rw [EStateM.run_bind, run_writeReg]
  simp only
  rw [EStateM.run_bind, EStateM.run_bind, run_readReg, Std.ExtDHashMap.get?_insert]

  simp only [beq_iff_eq, reduceCtorEq, ↓reduceDIte, BB_eq, get_next_pc_eq, wX_bits_eq_writeReg,
    set_next_pc_eq, bind_pure_comp, pure_bind, EStateM.run_pure, natCast_eq_ofNat, Nat.reducePow]
  rw [read_pc]
  conv =>
    lhs
    arg 2
    simp only
  rw [EStateM.run_bind]

  rw [ext_control_check_pc]
  conv =>
    lhs
    arg 2
    simp only
  rw [bit_to_bool, bool_bit_backwards.eq_def, access, ofBool, bits_of_virtaddr,
    sign_extend, Sail.BitVec.signExtend]
  rw [run_ite]
  conv =>
    lhs
    arg 2
    rw [← h_sign_extend]

  hide_constants

  stop
  simp only [BB_eq, get_next_pc_eq, wX_bits_eq_writeReg, set_next_pc_eq, bind_pure_comp, pure_bind,
    map_bind, EStateM.run_bind, run_writeReg, EStateM.run_map, natCast_eq_ofNat, Nat.reducePow,
    run_ite]

  simp only [ext_control_check_pc, bit_to_bool, access, ofBool, bits_of_virtaddr, Nat.one_lt_ofNat,
    getElem!_pos, ofNat_eq_ofNat, currentlyEnabled, hartSupports, Bool.false_and, Bool.false_or,
    Bool.and_self, bind_pure_comp, Functor.map_map, bind_map_left, EStateM.run_bind,
    run_bool_bit_backwards, sign_extend, Sail.BitVec.signExtend, ← h_sign_extend]

  split_ifs with m6 m6b m6b <;>
  simp [← BitVec.toNat_inj] at m6 m6b <;>
  [ skip; omega; omega; skip ] <;>
  rw [run_readReg] <;>
  simp [read_pc] <;>
  rw [run_readReg] <;>
  simp [Std.ExtDHashMap.get?_insert, read_pc, hmod] <;>
  rw [run_readReg] <;>
  simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_eq_some_get h_misa] <;>
  rw [run_readReg]
  . simp [h_add', Word.toBitVec64, Word.toNat]
  . simp [BitVec.ofNatLT_eq_ofNat, h_add']
    simp [Word.toBitVec64, Word.toNat]
    have h_add_pc : List.Forall SP1Constraint.toProp (AddOperation.constraints
        #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0]
        {value := #v[Main[26], Main[27], Main[28], Main[29]]} 1) := by aesop
    have h_add_pc' := (AddOperation.correct _ _ _  _ rfl h_add_pc pc_isU64 Word.four_isU64).2
    simp [Word.toBitVec64, Word.toNat] at h_add_pc'
    rw [h_add_pc', BitVec.ofNatLT_eq_ofNat]

end JalChip

-- #print axioms JalChip.SP1JAL_correct
