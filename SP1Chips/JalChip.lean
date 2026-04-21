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
  have h : Main[6] < 32 := by simp_all only [Fin.isValue, one_ne_zero, sub_self,
    or_true, not_false_eq_true, forall_const, true_or, true_and]
  simp_all only [Fin.isValue, gt_iff_lt]
  exact h

def sp1_op_a (cstrs : (constraints Main).allHold) (h_is_real : Main[31] = 1) : BitVec 5 :=
  Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)

-- dt: could instead put `Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]]` here...
def sp1_op_b : BitVec 21 := BitVec.ofNat 21 (Main[14].val + Main[15].val * 65536)

def sp1_jal (Main : Vector (Fin KB) 32) : SailM Unit := do
  let op_a := regidx.Regidx (BitVec.ofNat 5 Main[6].val)
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
    h_is_real, Fin.isValue, true_and] at cstrs

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

  have hmod4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
      Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]]) % 4 = 0 := by
    simp
    refine add_mod4_eq_zero_of_mod4_eq_zero ?_ ?_
    · simp [ofNat_eq_ofNat, Fin.val_mod_eq_zero_iff_of_lt (show 4 < KB by decide)]
      simp_all only []
    · simp only [ofNat_eq_ofNat, ofNat64_mod_4_eq_zero_iff]
      simp_all only [Fin.isValue, true_and]

  have hmod  := (mul4_means_0_1_are_0 hmod4).2
  have hmod' := (mul4_means_0_1_are_0 hmod4).1

  simp [spec_jal, sp1_jal, execute_JAL, op_a, op_b, sp1_op_b, sp1_op_a]

  have h_add_imm : List.Forall SP1Constraint.toProp (AddOperation.constraints
      #v[Main[3], Main[4], Main[5], 0]
      #v[Main[14], Main[15], Main[16], Main[17]]
      {value := #v[Main[23], Main[24], Main[25], Main[26]]} 1) := cstrs.1

  have pc_isU64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] :=
    Word.isU64_of_cases h3 h4 h5 (by simp)
  have imm_isU64 : Word.isU64 #v[Main[14], Main[15], Main[16], Main[17]] := by
    refine Word.isU64_of_cases h14 h15 h16 h17

  have h_add' := (AddOperation.spec pc_isU64 imm_isU64 h_add_imm).2
  simp at h_add'

  have hmod4_target : Word.toBitVec64 #v[Main[23], Main[24], Main[25], Main[26]] % 4 = 0 :=
    h_add' ▸ hmod4

  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at read_pc

  simp [spec_jal, sp1_jal, execute_JAL, op_a, op_b, sp1_op_b, sp1_op_a,
    run_readReg_of_isInitialized _ _ hs, ← h_sign_extend, read_pc, h_add']
  rw [run_readReg_of_isInitialized _ _ (by clear *- hs; aesop)]
  simp [Std.ExtDHashMap.get_insert, read_pc]
  rw [jump_to_of_mod4_eq_zero _ _ (by aesop) hmod4]
  simp [Std.ExtDHashMap.insert_insert, EStateM.Result.map]

  by_cases h6 : Main[6] = 0
  · simp [h6]
  · have h6' : BitVec.ofNat 5 (↑Main[6] : Nat) ≠ 0#5 := by
      clear *- h6 h_op_a; simp [← BitVec.toNat_inj]; omega
    have h_add_pc : List.Forall SP1Constraint.toProp (AddOperation.constraints
      #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0]
      {value := #v[Main[27], Main[28], Main[29], Main[30]]} 1) := by aesop
    have h_add_pc' := (AddOperation.spec pc_isU64 Word.four_isU64 h_add_pc).2
    simp at h_add_pc'
    have h_four : Word.toBitVec64 (#v[4, 0, 0, 0] : Vector (Fin KB) 4) = (4#64 : BitVec 64) := by
      simp [Word.toBitVec64, Word.toNat_def]
    rw [h_four] at h_add_pc'
    simp only [BitVec.ofNatLT_eq_ofNat, if_neg h6', ← h_add_pc']
    simp
    congr 1 <;> rw [BitVec.ofNatLT_eq_ofNat]

end Jal
