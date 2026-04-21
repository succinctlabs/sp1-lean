import SP1Operations.Operation.AddOperation
import SP1Chips.Jal.Constraints

namespace Jal

open BitVec

open Sail SailState BitVec LeanRV64D.Functions

attribute [simp] assert PreSail.assert
  RETIRE_SUCCESS

variable (Main : Vector (Fin KB) 32) (s : SailState)

lemma op_a_lt32_of_constraints {Main : Vector (Fin KB) 32}
    (h_cstrs : (constraints Main).allHold) (h_is_real : Main[31] = 1) : Main[6].val < 32 := by
  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at h_cstrs
  have h22 : Main[22] = 1 := by
    have h31_22 : Main[31] - Main[22] = 0 :=
      (h_cstrs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).resolve_right (by decide)
    rw [← h_is_real]; exact (sub_eq_zero.mp h31_22).symm
  have h : Main[6] < 32 := by simp_all only [BB_eq, Fin.isValue, one_ne_zero, sub_self,
    or_true, not_false_eq_true, forall_const, true_or, true_and]
  simp_all only [BB_eq, Fin.isValue, gt_iff_lt]
  exact h

def sp1_op_a (cstrs : (constraints Main).allHold) (h_is_real : Main[31] = 1) : BitVec 5 :=
  Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)

-- dt: could instead put `Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]]` here...
def sp1_op_b : BitVec 21 := BitVec.ofNat 21 (Main[14].val + Main[15].val * 65536)

def sp1_jal (Main : Vector (Fin KB) 32) : SailM Unit := do
  let op_a := regidx.Regidx Main[6].val
  set_next_pc (Word.toBitVec64 #v[Main[23], Main[24], Main[25], Main[26]])
  wX_bits op_a (Word.toBitVec64 #v[Main[27], Main[28], Main[29], Main[30]])

noncomputable def spec_jal (imm : BitVec 21) (rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_JAL imm rd

set_option debug.skipKernelTC true in
theorem SP1JAL_correct
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[31] = 1)
    (state_cstrs : (constraints Main).initialState s)
    (hs : SailState.isInitialized s) :
    let op_a := sp1_op_a Main cstrs h_is_real
    let op_b := sp1_op_b Main
    (spec_jal op_b (.Regidx op_a)).run s = (sp1_jal Main).run s := by
  extract_lets op_a op_b

  have h_op_a : Main[6] < 32 := op_a_lt32_of_constraints cstrs h_is_real

  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    AddOperation.constraints, h_is_real, h_op_a] at state_cstrs
  obtain ⟨read_pc, h⟩ := state_cstrs

  -- specialize h (by aesop)

  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp, sub_eq_zero,
    h_is_real, Fin.isValue, BB_eq, true_and] at cstrs

  have h22 : Main[22] = 1 := by
    exact (cstrs.2.2.2.2.2.2.2.2.2.2.2.2.1).resolve_right (by decide) |>.symm
  simp [h22] at *

  have h3 : Main[3] < 65536 := by simp_all only
  have h4 : Main[4] < 65536 := by simp_all only
  have h5 : Main[5] < 65536 := by simp_all only
  have h14 : Main[14] < 65536 := by simp_all only
  have h15 : Main[15] < 65536 := by simp_all only
  have h16 : Main[16] < 65536 := by simp_all only
  have h17 : Main[17] < 65536 := by simp_all only

  have h_sign_extend : Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]] =
      BitVec.signExtend 64 (BitVec.ofNat 21 (↑Main[14] + ↑Main[15] * 65536)) := by
    simp_all only

  have hpc : BitVec.ofNat 64 (↑Main[3] + ↑Main[4] * 65536 + ↑Main[5] * 4294967296) =
      Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] := by simp [Word.toBitVec64, Word.toNat]

  have hmod : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
      Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]])[1] = false := by
    refine (mul4_means_0_1_are_0 ?_).2
    simp [hpc]
    refine add_mod4_eq_zero_of_mod4_eq_zero ?_ ?_
    · simp [ofNat_eq_ofNat, Fin.val_mod_eq_zero_iff_of_lt (show 4 < KB by decide)]
      simp_all only []
    · simp only [ofNat_eq_ofNat, ofNat64_mod_4_eq_zero_iff]
      simp_all only [BB_eq, Fin.isValue, true_and]

  have hmod' : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
      Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]])[0] = false := by
    refine (mul4_means_0_1_are_0 ?_).1
    simp [hpc]
    refine add_mod4_eq_zero_of_mod4_eq_zero ?_ ?_
    · simp [ofNat_eq_ofNat, Fin.val_mod_eq_zero_iff_of_lt (show 4 < KB by decide)]
      simp_all only [BB_eq, Fin.isValue, true_and]
    · simp only [ofNat_eq_ofNat, ofNat64_mod_4_eq_zero_iff]
      simp_all only [BB_eq, Fin.isValue, true_and]

  simp [spec_jal, sp1_jal, execute_JAL, op_a, op_b, sp1_op_b, sp1_op_a]

  have h_add_imm : List.Forall SP1Constraint.toProp (AddOperation.constraints
      #v[Main[3], Main[4], Main[5], 0]
      #v[Main[14], Main[15], Main[16], Main[17]]
      {value := #v[Main[23], Main[24], Main[25], Main[26]]} 1) := by
    exact cstrs.1

  have pc_isU64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] :=
    Word.isU64_of_cases h3 h4 h5 (by simp)
  have imm_isU64 : Word.isU64 #v[Main[14], Main[15], Main[16], Main[17]] := by
    refine Word.isU64_of_cases h14 h15 h16 h17

  have h_add' := (AddOperation.spec pc_isU64 imm_isU64 h_add_imm).2
  simp [execute_RTYPE_pure] at h_add'

  simp only [ext_control_check_pc, bit_to_bool, access, ofBool, bits_of_virtaddr, Nat.one_lt_ofNat,
    getElem!_pos, ofNat_eq_ofNat, currentlyEnabled, hartSupports, Bool.false_and, Bool.false_or,
    Bool.and_self, bind_pure_comp, Functor.map_map, bind_map_left, EStateM.run_bind,
    bool_bit_backwards, sign_extend, Sail.BitVec.signExtend, ← h_sign_extend, jump_to]

  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at read_pc

  simp [run_readReg_of_isInitialized _ _ hs]
  rw [run_readReg_of_isInitialized _ _ (by clear *- hs; aesop)]
  simp [Std.ExtDHashMap.get_insert, h_add', read_pc, hmod, hmod']
  stop
  rw [run_readReg_of_isInitialized _ _ (by clear *- hs; aesop)]
  simp

  by_cases h6 : Main[6] = 0
  · simp [h6, ← h_add']
  · have : BitVec.ofNat 5 ↑Main[6] ≠ 0#5 := by
      clear *- h6 h_op_a; simp [← BitVec.toNat_inj]; omega
    simp [BitVec.ofNatLT_eq_ofNat, this]
    rw [BitVec.ofNatLT_eq_ofNat, ← h_add']
    simp [← h_add']
    have h_add_pc : List.Forall SP1Constraint.toProp (AddOperation.constraints
      #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0]
      {value := #v[Main[27], Main[28], Main[29], Main[30]]} 1) := by aesop
    have h_add_pc' := (AddOperation.spec pc_isU64 Word.four_isU64 h_add_pc).2
    simp at h_add_pc'
    simp [h_add_pc']
    simp [Word.toBitVec64, Word.toNat_def]

end Jal
