import SP1Operations.Operation.AddOperation
import SP1Chips.Jal.Constraints

namespace Jal

open BitVec

open Sail SailState BitVec LeanRV64IM.Functions

variable (Main : Vector (Fin BB) 31) (s : SailState)

lemma op_a_lt32_of_constraints {Main : Vector (Fin BB) 31}
    (h_cstrs : (constraints Main).allHold) (h_is_real : Main[30] = 1) : Main[6].val < 32 := by
  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at h_cstrs
  have h6 : Main[6] < 32 := by simp_all only [BB_eq, Fin.isValue, one_ne_zero, sub_self,
    or_true, not_false_eq_true, forall_const, true_or, true_and]
  simp_all only [BB_eq, Fin.isValue, gt_iff_lt]
  exact h6

def sp1_op_a (cstrs : (constraints Main).allHold) (h_is_real : Main[30] = 1) : BitVec 5 :=
  Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)

-- dt: could instead put `Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]]` here...
def sp1_op_b : BitVec 21 := BitVec.ofNat 21 (Main[14].val + Main[15].val <<< 16)

def sp1_jal (Main : Vector (Fin BB) 31) : SailM Unit := do
  let op_a := regidx.Regidx Main[6].val
  wX_bits op_a (Word.toBitVec64 #v[Main[26], Main[27], Main[28], Main[29]])
  set_next_pc (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]])

def spec_jal (imm : BitVec 21) (rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_JAL imm rd

theorem SP1JAL_correct
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1)
    (state_cstrs : (constraints Main).initialState s)
    (h_misa : Register.misa ∈ s.regs) :
    let op_a := sp1_op_a Main cstrs h_is_real
    let op_b := sp1_op_b Main
    (spec_jal op_b (.Regidx op_a)).run s = (sp1_jal Main).run s := by
  extract_lets op_a op_b

  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
    List.Forall, AddOperation.constraints, h_is_real] at state_cstrs
  obtain ⟨read_pc, h⟩ := state_cstrs
  have h_op_a : Main[6].val < 32 := op_a_lt32_of_constraints cstrs h_is_real
  specialize h (by aesop)
  clear h

  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp, sub_eq_zero,
    h_is_real, Fin.isValue, BB_eq, true_and] at cstrs

  obtain ⟨add_imm_cstrs, add_pc_cstrs, cstrs⟩ := cstrs

  have h_sign_extend : Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]] =
      BitVec.signExtend 64 (BitVec.ofNat 21 (↑Main[14] + ↑Main[15] <<< 16)) := by
    simp_all only

  have hpc : BitVec.ofNat 64 (↑Main[3] + ↑Main[4] <<< 16 + ↑Main[5] <<< 32) =
      Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] := by
    simp [Nat.shiftLeft_eq, Word.toBitVec64, Word.toNat]

  have hmod : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
                BitVec.signExtend 64 (BitVec.ofNat 21 (↑Main[14] + ↑Main[15] <<< 16)))[1] = false := by
    refine (mul4_means_0_1_are_0 ?_).2
    simp [hpc]
    refine add_mod4_eq_zero_of_mod4_eq_zero ?_ ?_
    · simp only [ofNat_eq_ofNat, ofNat64_mod_4_eq_zero_iff]
      simp_all only [Fin.isValue, true_and, Fin.mod_def, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
        Fin.mk_eq_zero]
    · simp [ofNat64_mod_4_eq_zero_iff]
      rw [← h_sign_extend]
      simp
      simp_all only [Fin.isValue, true_and]

  have h3 : Main[3] < 65536 := by omega
  have h4 : Main[4] < 65536 := by omega
  have h5 : Main[5] < 65536 := by omega
  have h14 : Main[14] < 65536 := by omega
  have h15 : Main[15] < 65536 := by omega
  have h16 : Main[16] < 65536 := by omega
  have h17 : Main[17] < 65536 := by omega
  have pc_isU64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] :=
    Word.isU64_of_cases _ h3 h4 h5 (by simp)
  have imm_isU64 : Word.isU64 #v[Main[14], Main[15], Main[16], Main[17]] := by
    refine Word.isU64_of_cases _ h14 h15 h16 h17

  have h_add' := (AddOperation.correct _ _ _  _ rfl add_imm_cstrs pc_isU64 imm_isU64).2

  simp [spec_jal, sp1_jal, op_a, op_b, sp1_op_b, sp1_op_a]
  rw [run_readReg]
  rw [read_pc]
  simp only
  rw [execute_JAL]
  rw [EStateM.run_bind]
  rw [run_readReg]
  simp only [Std.ExtDHashMap.get?_insert]
  simp
  rw [read_pc]
  simp [ext_control_check_pc, bits_of_virtaddr, access, ofBool, hmod]
  simp [currentlyEnabled]
  rw [run_readReg]
  simp [Std.ExtDHashMap.get?_insert]
  simp only [ext_control_check_pc, bit_to_bool, access, ofBool, bits_of_virtaddr, Nat.one_lt_ofNat,
    getElem!_pos, ofNat_eq_ofNat, currentlyEnabled, hartSupports, Bool.false_and, Bool.false_or,
    Bool.and_self, bind_pure_comp, Functor.map_map, bind_map_left, EStateM.run_bind,
    run_bool_bit_backwards, sign_extend, Sail.BitVec.signExtend, ← h_sign_extend]
  simp [Std.ExtDHashMap.get?_eq_some_get h_misa]
  rw [run_readReg]
  simp [BitVec.ofNatLT_eq_ofNat]

  split_ifs with m6
  · simp [h_add']
  · simp only [Fin.isValue, run_writeReg, LawfulMonadStateOf.insert_insert_insert_cancel,
      EStateM.Result.map_ok, EStateM.Result.ok.injEq, PreSail.SequentialState.mk.injEq,
      _root_.and_self, and_true, true_and]
    simp [← BitVec.toNat_inj] at m6
    have h13 : Main[13] = 0 := by omega
    simp [h13] at add_pc_cstrs
    have h_add_pc : List.Forall SP1Constraint.toProp (AddOperation.constraints
        #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0]
        {value := #v[Main[26], Main[27], Main[28], Main[29]]} 1) := add_pc_cstrs
    rw [(AddOperation.correct _ _ _  _ rfl h_add_pc pc_isU64 Word.four_isU64).2, h_add']
    simp [Word.toBitVec64, Word.toNat]
    rw [BitVec.ofNatLT_eq_ofNat]

end Jal
