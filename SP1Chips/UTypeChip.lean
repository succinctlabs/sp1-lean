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
def sp1_op_b (Main : Vector (Fin BB) 31) : BitVec 32 :=
  BitVec.ofNat 32 (Main[14] + Main[15] * 65536)
  -- Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]]

/-- Note this isn't actually used in the instruction. -/
def sp1_op_c (Main : Vector (Fin BB) 31) : BitVec 64 :=
  Word.toBitVec64 #v[Main[18], Main[19], Main[20], Main[21]]

lemma BitVec.eq_zero_length_zero (x : BitVec 0) : x = 0 := by
  refine BitVec.eq_of_toNat_eq ?_
  simp [BitVec.toNat]

lemma BitVec.signExtend_append (n : ℕ) (hn : k ≤ n) (x : BitVec m) (y : BitVec k) :
    BitVec.signExtend n (x ++ y) = (BitVec.signExtend (n - k) x) ++ y := by
  unfold BitVec.signExtend
  rw [BitVec.toInt_append]
  by_cases hm : m = 0
  · cases hm
    rw [BitVec.eq_zero_length_zero x]
    simp
    rw [BitVec.setWidth_append]
    simp [hn]
    sorry
  stop
  rw [BitVec.setWidth_eq]
  rw [BitVec.setWidth_append_of_eq]
  sorry

def sp1_utype (Main : Vector (Fin BB) 31)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) : SailM Unit := do
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4#64)
  let op_a := sp1_op_a Main cstrs h_is_real
  let write_value := Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]] --++ (0x000 : (BitVec 12))
  wX_bits (.Regidx op_a) (write_value)

set_option debug.skipKernelTC true in
set_option maxHeartbeats 0 in
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
    (sp1_utype Main cstrs h_is_real).run s = (spec_utype (op_b >>> 12) (.Regidx op_a) opcode).run s := by
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
    rw [run_readReg]
    simp [read_pc]
    split_ifs with h6
    · have h13 : Main[13] = 1 := by
        rw [← BitVec.toNat_inj] at h6
        simp_all [h6]
      simp [h13] at reader_cstrs
      simp [h13, h_is_real] at add_cstrs
      simp [Word.toBitVec64, Word.toNat]
    stop
    · have h13 : Main[13] = 0 := by
        simp [← BitVec.toNat_inj] at h6
        have : Main[13] ≠ 1 := by simp_all only [Fin.isValue, BB_eq, one_ne_zero, or_true,
          true_or, and_true, true_and, forall_true_left, ne_eq, not_false_eq_true]
        simp [h6, this] at reader_cstrs
        simp_all only
      simp [h13, h_is_real] at reader_cstrs add_cstrs

      simp [cstrs.2.1, cstrs.2.2.1, cstrs.2.2.2.1] at add_cstrs
      have := AddOperation.correct _ _ _ _ rfl add_cstrs sorry sorry
      simp at this
      have h25 : Main[25] = Main[14] ∧ Main[26] = Main[15] ∧
          Main[27] = Main[16] ∧ Main[28] = Main[17] := by

        sorry
      simp [h25.1, h25.2.1, h25.2.2.1, h25.2.2.2]

      simp [sp1_op_b]
      have h_extend := reader_cstrs.1.1.2
      simp only [sign_extend, Sail.BitVec.signExtend]
      rw [BitVec.signExtend_append _ (by omega)]

      rw [← h_extend.2.2.2.1]
      rw [BitVec.ofNatLT_eq_ofNat]
      rw [BitVec.setWidth_append]
      simp only [Fin.isValue, Nat.reduceLeDiff, ↓reduceDIte, Nat.reduceSub, Nat.reduceAdd,
        BitVec.cast_eq]
      simp only [Word.toBitVec64]
      simp only [Word.toNat]
      simp
      congr 3

      rw [BitVec.signExtend_append _ (by omega)]
      simp

  | inr h_is_auipc =>
    simp [h_is_auipc] at reader_cstrs cstrs
    simp [h_is_auipc, sp1_op_a]
    simp [h_is_auipc, constraints, List.Forall, SP1Constraint.toStateProp,
      AddOperation.constraints, JTypeReader.constraints, CPUState.constraints, h_is_real] at state_cstrs
    obtain ⟨read_pc, read_op_a⟩ := state_cstrs

    split_ifs with h6
    · have h13 : Main[13] = 1 := by
        rw [← BitVec.toNat_inj] at h6
        simp_all [h6]
      simp [h13] at reader_cstrs
      simp [h13, h_is_real] at add_cstrs
      simp [read_pc]

      rw [run_readReg]
      simp [read_pc]
      rw [run_readReg]
      simp [Std.ExtDHashMap.get?_insert, read_pc]
      simp [Word.toBitVec64, Word.toNat]
    · have h13 : Main[13] = 0 := by
        rw [← BitVec.toNat_inj] at h6
        have : Main[13] ≠ 1 := by simp_all only [Fin.isValue, BB_eq, one_ne_zero, or_true,
          true_or, and_true, true_and, forall_true_left, toNat_ofNatLT, toNat_ofNat, Nat.reducePow,
          Nat.zero_mod, Fin.val_eq_zero_iff, ne_eq, not_false_eq_true]
        simp_all [h6]
      simp [h13, h_is_real] at reader_cstrs add_cstrs
      simp [cstrs.2.1, cstrs.2.2.1, cstrs.2.2.2.1] at add_cstrs
      simp [sp1_op_b]

      have h_extend := reader_cstrs.1.1.2
      simp only [sign_extend, Sail.BitVec.signExtend]
      rw [BitVec.signExtend_append _ (by omega)]
      simp
      rw [run_readReg]
      simp [read_pc]
      rw [run_readReg]
      simp [read_pc]
      simp [Std.ExtDHashMap.get?_insert, read_pc]

      have := (AddOperation.correct _ _ _ _ rfl add_cstrs sorry sorry).2
      simp [Word.toBitVec64, Word.toNat] at this


      rw [← h_extend.2.2.2]
      rw [BitVec.ofNatLT_eq_ofNat]
      rw [BitVec.setWidth_append]
      rw [run_readReg]
      simp only [Fin.isValue, Nat.reduceLeDiff, ↓reduceDIte, Nat.reduceSub, Nat.reduceAdd,
        BitVec.cast_eq]
      simp only [Word.toBitVec64]
      simp only [Word.toNat, read_pc]
      simp
      rw [run_readReg]
      simp [Std.ExtDHashMap.get?_insert, read_pc]


      congr 3
      have := (AddOperation.correct _ _ _ _ rfl add_cstrs sorry sorry).2
      simp [Word.toBitVec64, Word.toNat] at this
      convert this

      ·
        sorry
      ·
        sorry
      rw [this]


      refine BitVec.eq_of_toNat_eq ?_
      simp
      have h16 : Main[16] = 0 := by simp_all only
      have h17 : Main[17] = 0 := by simp_all only
      simp [h16, h17]

      rw [Nat.mod_eq_of_lt (b := 1048576)]
      have h1415 : Main[14].val + ↑Main[15] * 65536 < 1048576 := by simp_all only
      exact h1415
      sorry


end UType
