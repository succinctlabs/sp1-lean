import SP1Operations.Operation.AddOperation

namespace JalChip

open BitVec

open Sail SailState BitVec LeanRV64IM.Functions

def constraints (Main : Vector (Fin BB) 31) : SP1ConstraintList :=
  let E0 : Fin BB := Main[30] - 1
  let E1 : Fin BB := Main[30] * E0
  let CS0 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[Main[14], Main[15], Main[16], Main[17]] { value := #v[Main[22], Main[23], Main[24], Main[25]] } Main[30]
  let E2 : Fin BB := Main[1] * 65536
  let E3 : Fin BB := Main[2] + E2
  let E4 : Fin BB := Main[30] - 1
  let E5 : Fin BB := Main[30] * E4
  let E6 : Fin BB := E3 + 8
  let E7 : Fin BB := Main[2] - 1
  let E8 : Fin BB := E7 * 1761607681
  let E9 : Fin BB := Main[30] - 1
  let E10 : Fin BB := E9 * Main[13]
  let E11 : Fin BB := Main[30] - Main[13]
  let CS1 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0] { value := #v[Main[26], Main[27], Main[28], Main[29]] } E11
  let E12 : Fin BB := Main[13] * Main[26]
  let E13 : Fin BB := Main[13] * Main[27]
  let E14 : Fin BB := Main[13] * Main[28]
  let E15 : Fin BB := Main[1] * 65536
  let E16 : Fin BB := Main[2] + E15
  let E17 : Fin BB := Main[30] - 1
  let E18 : Fin BB := Main[30] * E17
  let E19 : Fin BB := Main[26] - 0
  let E20 : Fin BB := Main[13] * E19
  let E21 : Fin BB := Main[27] - 0
  let E22 : Fin BB := Main[13] * E21
  let E23 : Fin BB := Main[28] - 0
  let E24 : Fin BB := Main[13] * E23
  let E25 : Fin BB := Main[29] - 0
  let E26 : Fin BB := Main[13] * E25
  let E27 : Fin BB := E16 + 3
  let E28 : Fin BB := Main[30] - 1
  let E29 : Fin BB := Main[30] * E28
  let E30 : Fin BB := E27 - Main[11]
  let E31 : Fin BB := E30 - 1
  let E32 : Fin BB := E31 - Main[12]
  let E33 : Fin BB := E32 * 2013235201
  [
    (.assertZero E1),
    (.assertZero Main[25]),
    (.assertZero E5),
    (.receive (.state Main[0] E3 Main[3] Main[4] Main[5]) Main[30]),
    (.send (.state Main[0] E6 Main[22] Main[23] Main[24]) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 6) E8 13 0) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0) Main[30]),
    (.assertZero E10),
    (.assertZero Main[29]),
    (.assertZero E12),
    (.assertZero E13),
    (.assertZero E14),
    (.assertZero E18),
    (.send (.program Main[3] Main[4] Main[5] (Opcode.ofNat 33) Main[6] Main[14] Main[15] Main[16] Main[17] Main[18] Main[19] Main[20] Main[21] Main[13] 1 1 111 0 0) Main[30]),
    (.assertZero E20),
    (.assertZero E22),
    (.assertZero E24),
    (.assertZero E26),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 6) Main[12] 16 0) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E33 0) Main[30]),
    (.send (.memory Main[0] Main[11] Main[6] 0 0 Main[7] Main[8] Main[9] Main[10]) Main[30]),
    (.receive (.memory Main[0] E27 Main[6] 0 0 Main[26] Main[27] Main[28] Main[29]) Main[30]),
  ] ++ CS0 ++ CS1

open LeanRV64IM.Functions

-- lemma eq_zero_of_constraints (Main : Vector (Fin BB) 31)
--     (h_cstrs : (constraints Main).allHold) : Main[25] = 0 := by
--   simp [constraints] at h_cstrs
--   aesop

-- lemma isU64_of_constraints (Main : Vector (Fin BB) 31)
--     (h_cstrs : (constraints Main).allHold)
--     (h_is_real : Main[30] = 1) :
--     Word.isU64 #v[Main[3], Main[4], Main[5], 0] := by
--   simp [constraints, h_is_real, SP1Constraint.toProp] at h_cstrs
--   refine Word.isU64_of_cases ?_ ?_ ?_ ?_ ?_
--   · aesop
--   · aesop
--   · aesop
--   · aesop

-- lemma isU64_of_constraints' (Main : Vector (Fin BB) 31)
--     (h_cstrs : (constraints Main).allHold)
--     (h_is_real : Main[30] = 1) :
--     Word.isU64 #v[Main[14], Main[15], Main[16], Main[17]] := by
--   simp [constraints, h_is_real, SP1Constraint.toProp] at h_cstrs
--   refine Word.isU64_of_cases ?_ ?_ ?_ ?_ ?_
--   · aesop
--   · aesop
--   · aesop
--   · aesop

-- lemma program_constraints_allHold (Main : Vector (Fin BB) 31)
--     (h_cstrs : (constraints Main).allHold) :
--     SP1Constraint.toProp (.send (.program Main[3] Main[4] Main[5] (Opcode.ofNat 33)
--       Main[6] Main[14] Main[15] Main[16] Main[17] Main[18] Main[19]
--       Main[20] Main[21] Main[13] 1 1 111 0 0) Main[30]) := by
--   simp [constraints] at h_cstrs
--   aesop

-- lemma link_eq_of_constraints (Main : Vector (Fin BB) 31)
--     (h_cstrs : (constraints Main).allHold)
--     (h_is_real : Main[30] = 1) (h_op_a : Main[13] = 0) :
--     BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48) =
--       BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32) + 4 := by
--   have h345 := isU64_of_constraints Main h_cstrs h_is_real
--   simp [constraints] at h_cstrs
--   have : (AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0]
--       { value := #v[Main[26], Main[27], Main[28], Main[29]] } (Main[30] - Main[13])).allHold := by
--     aesop
--   have := AddOperation.correct _ _ _ _ ?_ this h345 ?_
--   simp [Word.toBitVec64] at this
--   have := this.2
--   refine this.trans ?_
--   simp [Word.toNat]
--   · simp [h_op_a, h_is_real]
--   · apply Word.isU64_of_cases <;> simp

-- lemma add_imm_eq_of_constarints (Main : Vector (Fin BB) 31)
--     (h_cstrs : (constraints Main).allHold)
--     (h_is_real : Main[30] = 1) :
--     BitVec.ofNat 64 (Main[22] + Main[23] * 65536 + Main[24] * 4294967296) =
--         BitVec.ofNat 64 (Main[3] + Main[4] * 65536 + ↑Main[5] * 4294967296) +
--           BitVec.ofNat 64 (Main[14] + Main[15] * 65536 + Main[16] * 4294967296 + Main[17] * 281474976710656) := by
--   have h345 := isU64_of_constraints Main h_cstrs h_is_real
--   have h1415 := isU64_of_constraints' Main h_cstrs h_is_real
--   simp [constraints] at h_cstrs
--   have : (AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[Main[14], Main[15], Main[16], Main[17]]
--       { value := #v[Main[22], Main[23], Main[24], Main[25]] } Main[30]).allHold := by
--     aesop
--   have := AddOperation.correct _ _ _ _ h_is_real this h345 h1415
--   simp [Word.toBitVec64] at this
--   have := this.2
--   have h25 : Main[25] = 0 := h_cstrs.2.1
--   simp [Word.toNat, h25] at this
--   exact this

-- /-- dt: should extract this out and clean up more -/
-- lemma ofInt_ofNat_of_constraints (Main : Vector (Fin BB) 31)
--     (h_cstrs : (constraints Main).allHold)
--     (h_is_real : Main[30] = 1) :
--     let imm_nat : ℕ := Main[14] + Main[15] * 65536 + Main[16] * 4294967296 + Main[17] * 281474976710656
--     BitVec.ofInt 64 (BitVec.ofNat 21 (imm_nat)).toInt = (BitVec.ofNat 64 (imm_nat)) := by
--   have := program_constraints_allHold Main h_cstrs
--   simp [SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble] at this

--   obtain ⟨⟨h14, h15, h16, h17⟩, _⟩ := this.1
--   simp [h15, h16, h17]
--   simp [BitVec.ofInt, BitVec.toInt]
--   simp [Int.toNat]

--   have h14' : Main[14].val % 2097152 = Main[14].val
--   · rw [Nat.mod_eq_of_lt]
--     omega
--   have h14'' : (Main[14].val : ℤ) % (2097152 : ℤ) = Main[14].val
--   · exact
--     Eq.symm
--       ((fun {a b} ↦ Int.neg_inj.mp) (congrArg Neg.neg (congrArg Nat.cast (id (Eq.symm h14')))))
--   simp [h14', h14'']
--   have h14''' : 2 * Main[14].val < 2097152 := by omega
--   simp [h14''']
--   rename_i right
--   simp_all only [SP1ConstraintList.allHold, BB_eq, Fin.isValue, and_self, Fin.reduceLT, and_true, true_and]
--   obtain ⟨left, right_1⟩ := this
--   obtain ⟨left_2, right_1⟩ := right_1
--   obtain ⟨left_3, right_1⟩ := right_1
--   obtain ⟨left_5, right_1⟩ := right_1
--   simp_all only [Fin.isValue]
--   rfl

--------------------------

lemma op_a_lt32_of_constraints {Main : Vector (Fin BB) 31}
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) : Main[6].val < 32 := by
  simp only [BB_eq, Nat.reducePow]
  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at h_cstrs
  have h : Main[6] < 32 := by aesop
  clear h_cstrs
  aesop

variable (Main : Vector (Fin BB) 31)
  (s : SailState) (cstrs : (constraints Main).allHold)
  (h_is_real : Main[30] = 1)

def sp1_imm : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_op_a : BitVec 5 := Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)

def sp1_jal (Main : Vector (Fin BB) 31) : SailM Unit := do
  let rd := regidx.Regidx Main[6].val
  let new_pc := BitVec.ofNat 64 (Main[22] + Main[23] * 2^16 + Main[24] * 2^32 + Main[25] * 2^48)
  let link := BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48)
  wX_bits rd link
  set_next_pc new_pc

def spec_jal (imm : BitVec 21) (rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_JAL imm rd

--   let init_pc := BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32)
--   let imm := BitVec.ofNat 64 (Main[14] + Main[15] * 2^16 + Main[16] * 2^32 + Main[17] * 2^48)
--   let new_pc := BitVec.ofNat 64 (Main[22] + Main[23] * 2^16 + Main[24] * 2^32 + Main[25] * 2^48)
--   let link := BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48)

set_option debug.skipKernelTC true in
set_option maxHeartbeats 0 in
theorem SP1JAL_correct
    (state_cstrs : (constraints Main).initialState s)
    (h_misa : Register.misa ∈ s.regs) :
    let imm := sp1_imm Main
    let op_a := sp1_op_a Main cstrs h_is_real
    (spec_jal imm (.Regidx op_a)).run s = (sp1_jal Main).run s := by
  extract_lets imm op_a

  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, h_is_real] at state_cstrs
  obtain ⟨read_pc, h⟩ := state_cstrs

  have h_op_a : Main[6].val < 32 := op_a_lt32_of_constraints cstrs h_is_real
  specialize h (by aesop)

  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp, sub_eq_zero,
    h_is_real] at cstrs

  have h_misa' : ∃ v_misa, s.regs.get? Register.misa = some v_misa := by

    sorry

  have hmod : (BitVec.ofNat 64 (↑Main[3] + ↑Main[4] * 65536 + ↑Main[5] * 4294967296) +
                sign_extend (setWidth 21 (BitVec.ofNat 12 ↑Main[21])))[1] = false := by
    sorry

  simp [spec_jal, sp1_jal, execute_JAL, op_a, imm, sp1_imm, sp1_op_a]


  have h13_is_bool : Main[13] = 0 ∨ Main[13] = 1 := by
    aesop

  simp [run_rX_bits, get_reg?_insert_nextPC, ext_control_check_addr, ext_control_check_pc,
    Sail.BitVec.access, bit_to_bool, Sail.BitVec.update, Sail.BitVec.updateSubrange',
    bits_of_virtaddr, BitVec.reduceAllOnes, BitVec.truncate_eq_setWidth, BitVec.reduceSetWidth,
    BitVec.shiftLeft_zero, BitVec.reduceNot, BitVec.setWidth_zero, BitVec.or_zero,
    Nat.one_lt_ofNat, getElem!_pos, BitVec.getElem_and, BitVec.reduceGetElem, Bool.true_and,
    BitVec.ofBool, BitVec.ofNat_eq_ofNat, cond_false, EStateM.run_bind,
    run_bool_bit_backwards, Bool.false_and, EStateM.run_map, run_writeReg, EStateM.Result.map_ok,
    currentlyEnabled, hartSupports, Bool.false_and, Bool.false_or, Bool.and_self,
    BitVec.ofNat_eq_ofNat, bind_pure_comp, Functor.map_map, EStateM.run_map]

  have h_add : BitVec.ofNat 64 (↑Main[3] + ↑Main[4] * 65536 + ↑Main[5] * 4294967296) +
      sign_extend (setWidth 21 (BitVec.ofNat 12 ↑Main[21])) =
      (BitVec.ofNat 64 (↑Main[22] + ↑Main[23] * 65536 + ↑Main[24] * 4294967296 + ↑Main[25] * 281474976710656)) := by

    sorry

  cases h13_is_bool with
  | inl h13_is_0 =>
      simp [h13_is_0] at cstrs
      have h6 : Main[6] ≠ 0 := by aesop
      have h6_bv : BitVec.ofNat 5 ↑Main[6] = 0#5 := sorry
      rw [run_readReg, read_pc]
      simp [h6]
      rw [run_readReg]
      simp [Std.ExtDHashMap.get?_insert, read_pc, hmod]
      rw [run_readReg]
      simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_eq_some_get h_misa]
      rw [run_readReg]
      simp [BitVec.ofNatLT_eq_ofNat, h6_bv]
      simp [h_add]

  | inr h13_is_1 =>
      simp [h13_is_1] at cstrs
      have h6 : Main[6] = 0 := by aesop

      simp [h6]
      rw [run_readReg]
      simp [read_pc]
      rw [run_readReg]
      simp [Std.ExtDHashMap.get?_insert, read_pc, hmod]
      rw [run_readReg]
      simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_eq_some_get h_misa]
      rw [run_readReg]
      simp [h_add]



end JalChip
