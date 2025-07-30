import SP1Chips.UType.Constraints


namespace UType

open BitVec

open Sail SailState BitVec LeanRV64IM.Functions

variable (Main : Vector (Fin BB) 31) (s : SailState)

lemma op_a_lt32_of_constraints {Main : Vector (Fin BB) 31} (h : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) : Main[6].val < 2^5 := by
  simp only [BB_eq, Nat.reducePow]
  have reader_cstrs := by
    simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at h
    exact h.2.2.1
  simp [JTypeReader.constraints, h_is_real,
    Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs
  -- simp [Nat.ble.eq_def] at reader_cstrs
  aesop

def spec_utype (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_UTYPE imm rd op

/-- The destination register for the operation-/
def sp1_op_a (Main : Vector (Fin BB) 31)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) : BitVec 5 :=
  Main[6]#'(op_a_lt32_of_constraints cstrs h_is_real)

/-- The immediate used to construct the value. -/
def sp1_op_b (Main : Vector (Fin BB) 31) : BitVec 20 :=
  Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]]

/-- Note this isn't actually used in the instruction. -/
def sp1_op_c (Main : Vector (Fin BB) 31) : BitVec 64 :=
  Word.toBitVec64 #v[Main[18], Main[19], Main[20], Main[21]]

def sp1_utype (Main : Vector (Fin BB) 31)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) : SailM Unit := do
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4#64)
  let op_a := sp1_op_a Main cstrs h_is_real
  let op_b := sp1_op_b Main
  wX_bits (.Regidx op_a) (op_b ++ (0x000 : (BitVec 12)))

def utype_chip_correct (Main : Vector (Fin BB) 31)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1)
    (state_cstrs : (constraints Main).initialState s)
    (h_misa : Register.misa ∈ s.regs) :
    let op_a := sp1_op_a Main cstrs h_is_real
    let op_b := sp1_op_b Main
    let op_c := sp1_op_c Main
    let opcode : uop := if Main[29] = 0 then .LUI else .AUIPC
    -- let op_c :=
    (sp1_utype Main cstrs h_is_real).run s = (spec_utype op_b (.Regidx op_a) opcode).run s := by
  simp [constraints, sub_eq_zero] at cstrs
  extract_lets op_a op_b op_c opcode

  obtain ⟨cpu_cstrs, add_cstrs, reader_cstrs, cstrs⟩ := cstrs
  simp [JTypeReader.constraints, inv_16BB_eq', h_is_real, SP1Constraint.toProp] at reader_cstrs
  simp [CPUState.constraints, h_is_real, SP1Constraint.toProp] at cpu_cstrs

  have h_opcode : Main[29] = 0 ∨ Main[29] = 1 := by sorry

  simp [op_a, op_b, op_c, opcode]

  unfold sp1_utype
  simp only [BB_eq, Fin.isValue, wX_bits_eq_writeReg, EStateM.run_bind, run_writeReg, run_ite]
  simp [sp1_utype, spec_utype, execute_UTYPE]


  cases h_opcode with
  | inl h_is_lui =>
    simp [h_is_lui] at reader_cstrs cstrs
    simp [h_is_lui, sp1_op_a]

    simp [h_is_lui, SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, JTypeReader.constraints, CPUState.constraints, h_is_real] at state_cstrs

    obtain ⟨read_pc, read_op_a⟩ := state_cstrs

    -- simp [bitVecToRegidxVal]
    rw [run_readReg]
    simp [read_pc]
    split_ifs
    · have h13 : Main[13] = 1 := sorry
      simp [h13] at reader_cstrs
      simp [h13, h_is_real] at add_cstrs
      simp

      sorry
    · have h13 : Main[13] = 0 := sorry
      simp [h13, h_is_real] at reader_cstrs add_cstrs

      have := AddOperation.correct _ _ _ _ rfl add_cstrs sorry sorry

      simp [sp1_op_b]
      have h_extend := reader_cstrs.1.1.2
      rw [← h_extend]
      rw [BitVec.ofNatLT_eq_ofNat]

      sorry

  | inr h_is_auipc =>

    sorry

  stop

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

  simp [spec_jal, sp1_jal, execute_JAL, op_a, op_b, sp1_op_b, sp1_op_a]

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

end UType
