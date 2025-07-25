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

def sp1_op_a : BitVec 5 := Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)

-- dt: could instead put `Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]]` here...
def sp1_op_b : BitVec 21 := BitVec.ofNat 21 (Main[14].val + Main[15].val * 65536)

def sp1_jal (Main : Vector (Fin BB) 31) : SailM Unit := do
  let rd := regidx.Regidx Main[6].val
  let new_pc := BitVec.ofNat 64 (Main[22] + Main[23] * 2^16 + Main[24] * 2^32 + Main[25] * 2^48)
  let link := BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48)
  wX_bits rd link
  set_next_pc new_pc

def spec_jal (imm : BitVec 21) (rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_JAL imm rd

section move

@[simp] -- common enough to want a lemma
lemma Word.four_isU64 : Word.isU64 #v[4, 0, 0, 0] :=
  Word.isU64_of_cases _ (by trivial) (by trivial) (by trivial) (by trivial)

end move

set_option debug.skipKernelTC true in
set_option maxHeartbeats 0 in
theorem SP1JAL_correct
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
    h_is_real] at cstrs

  have h_sign_extend : Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]] =
      BitVec.signExtend 64 (BitVec.ofNat 21 (↑Main[14] + ↑Main[15] * 65536)) := by
    have := cstrs.2.2.2.2.2.2.2.1.1.1
    exact this

  have hmod : (BitVec.ofNat 64 (↑Main[3] + ↑Main[4] * 65536 + ↑Main[5] * 4294967296) +
      Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]])[1] = false := by
    refine (mul4_means_0_1_are_0 ?_).2
    have hpc : BitVec.ofNat 64 (↑Main[3] + ↑Main[4] * 65536 + ↑Main[5] * 4294967296) =
      Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] := by simp [Word.toBitVec64, Word.toNat]
    rw [hpc]
    simp [Word.toBitVec64_add_mod_4, Word.add_toBitVec64_mod_4]
    refine mul4_add_is_mul4 ?_ ?_
    · simp
      rw [ofNat64_mod_4_eq_zero_iff]
      have : Main[3] % 4 = 0 := by aesop
      clear cstrs
      rw [Fin.mod_def] at this
      rw [← Fin.val_inj] at this
      simp at this
      exact this
    · simp
      aesop

  simp [spec_jal, sp1_jal, execute_JAL, op_a, op_b, sp1_op_b, sp1_op_a]

  have h_add_imm : List.Forall SP1Constraint.toProp (AddOperation.constraints
      #v[Main[3], Main[4], Main[5], 0]
      #v[Main[14], Main[15], Main[16], Main[17]]
      {value := #v[Main[22], Main[23], Main[24], Main[25]]} 1) := by
    aesop

  have pc_isU64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] := by
    refine Word.isU64_of_cases _ ?_ ?_ ?_ (by simp)
    · simp
      aesop
    · simp
      aesop
    · simp
      aesop

  have imm_isU64 : Word.isU64 #v[Main[14], Main[15], Main[16], Main[17]] := by
    refine Word.isU64_of_cases _ ?_ ?_ ?_ ?_
    · simp
      aesop
    · simp
      aesop
    · simp
      aesop
    · simp
      aesop

  have := AddOperation.correct _ _ _  _ rfl h_add_imm
  have h_add' := (this pc_isU64 imm_isU64).2
  simp [Word.toBitVec64, Word.toNat] at h_add'

  simp only [ext_control_check_pc, bit_to_bool, access, ofBool, bits_of_virtaddr, Nat.one_lt_ofNat,
    getElem!_pos, ofNat_eq_ofNat, currentlyEnabled, hartSupports, Bool.false_and, Bool.false_or,
    Bool.and_self, bind_pure_comp, Functor.map_map, bind_map_left, EStateM.run_bind,
    run_bool_bit_backwards,
    sign_extend, Sail.BitVec.signExtend, ← h_sign_extend]

  have h13_is_bool : Main[13] = 0 ∨ Main[13] = 1 := by aesop

  have h6_lt : Main[6].val < 2^5 := by aesop

  cases h13_is_bool with
  | inl h13_is_0 =>
      simp [h13_is_0] at cstrs
      have h6 : Main[6] ≠ 0 := by aesop
      have h6' : ∀ p : ↑Main[6] < 2 ^ 5, (BitVec.ofNatLT Main[6].val p : BitVec 5) ≠ 0#5 := by
        refine fun p h => h6 ?_
        simp [← BitVec.toFin_inj] at h
        rw [← Fin.val_inj] at h
        simpa using h

      rw [run_readReg, read_pc]
      simp [h6]
      rw [run_readReg]
      simp [Std.ExtDHashMap.get?_insert, read_pc]
      simp [hmod]
      rw [run_readReg]
      simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_eq_some_get h_misa]
      rw [run_readReg]

      simp [h6']
      have h6'' := h6' h6_lt
      rw [BitVec.ofNatLT_eq_ofNat] at h6''
      simp [h6'']
      rw [h_add']
      simp [Word.toBitVec64, Word.toNat]
      have h_add_pc : List.Forall SP1Constraint.toProp (AddOperation.constraints
          #v[Main[3], Main[4], Main[5], 0]
          #v[4, 0, 0, 0]
          {value := #v[Main[26], Main[27], Main[28], Main[29]]} 1) := by
        aesop
      have := AddOperation.correct _ _ _  _ rfl h_add_pc
      have h_add_pc' := (this pc_isU64 Word.four_isU64).2
      simp [Word.toBitVec64, Word.toNat] at h_add_pc'
      rw [h_add_pc']
      rw [BitVec.ofNatLT_eq_ofNat]

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
      simp [h_add']
      simp [Word.toBitVec64, Word.toNat]

end JalChip

#print axioms JalChip.SP1JAL_correct
