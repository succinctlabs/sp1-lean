import SP1Operations.Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace Bitwise

variable (Main : Vector (Fin KB) 51)
def is_real : Prop := Main[48] = 1 ∨ Main[49] = 1 ∨ Main[50] = 1

section constraints

-- Generated Lean code for chip BitwiseChip
@[irreducible] def constraints (Main : Vector (Fin KB) 51) : SP1ConstraintList :=
  let E0 : Fin KB := Main[48] + Main[49]
  let E1 : Fin KB := E0 + Main[50]
  let E2 : Fin KB := Main[48] - 1
  let E3 : Fin KB := Main[48] * E2
  let E4 : Fin KB := Main[49] - 1
  let E5 : Fin KB := Main[49] * E4
  let E6 : Fin KB := Main[50] - 1
  let E7 : Fin KB := Main[50] * E6
  let E8 : Fin KB := E1 - 1
  let E9 : Fin KB := E1 * E8
  let E10 : Fin KB := Main[48] * 2
  let E11 : Fin KB := Main[49] * 1
  let E12 : Fin KB := E10 + E11
  let E13 : Fin KB := Main[50] * 0
  let E14 : Fin KB := E12 + E13
  let E15 : Fin KB := Main[48] * 3
  let E16 : Fin KB := Main[49] * 4
  let E17 : Fin KB := E15 + E16
  let E18 : Fin KB := Main[50] * 5
  let E19 : Fin KB := E17 + E18
  let E20 : Fin KB := Main[48] * 4
  let E21 : Fin KB := Main[49] * 6
  let E22 : Fin KB := E20 + E21
  let E23 : Fin KB := Main[50] * 7
  let E24 : Fin KB := E22 + E23
  let E25 : Fin KB := Main[48] * 0
  let E26 : Fin KB := Main[49] * 0
  let E27 : Fin KB := E25 + E26
  let E28 : Fin KB := Main[50] * 0
  let E29 : Fin KB := E27 + E28
  let E30 : Fin KB := Main[48] * 51
  let E31 : Fin KB := Main[49] * 51
  let E32 : Fin KB := E30 + E31
  let E33 : Fin KB := Main[50] * 51
  let E34 : Fin KB := E32 + E33
  let E35 : Fin KB := 32 * Main[31]
  let E36 : Fin KB := E34 - E35
  let E37 : Fin KB := Main[48] * 8
  let E38 : Fin KB := Main[49] * 8
  let E39 : Fin KB := E37 + E38
  let E40 : Fin KB := Main[50] * 8
  let E41 : Fin KB := E39 + E40
  let E42 : Fin KB := 4 * Main[31]
  let E43 : Fin KB := E41 - E42
  let ⟨⟨⟨[E44, E45, E46, E47]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } E14 E1
  let E48 : Fin KB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E48, Main[4], Main[5]] 8 E1
  let E49 : Fin KB := Main[1] * 65536
  let E50 : Fin KB := Main[2] + E49
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E50 #v[Main[3], Main[4], Main[5]] E19 #v[E43, E36, E24, E29] #v[E44, E45, E46, E47] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E1
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero Main[13]),
  ]

end constraints

lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
    List.Forall SP1Constraint.toProp (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).2 ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[(Main[3] + 4), Main[4], Main[5]] 8 (Main[48] + Main[49] + Main[50])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[48] * 3 + Main[49] * 4 + Main[50] * 5)
      #v[Main[48] * 8 + Main[49] * 8 + Main[50] * 8 - 4 * Main[31],
      Main[48] * 51 + Main[49] * 51 + Main[50] * 51 - 32 * Main[31], Main[48] * 4 + Main[49] * 6 + Main[50] * 7, 0]
      #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[48] + Main[49] + Main[50])) ∧
    (Main[48] = 0 ∨ Main[48] = 1) ∧
    (Main[49] = 0 ∨ Main[49] = 1) ∧
    (Main[50] = 0 ∨ Main[50] = 1) ∧
    (Main[48] + Main[49] + Main[50] = 0 ∨ Main[48] + Main[49] + Main[50] - 1 = 0) ∧
    Main[13] = 0 := by
  simp [and_assoc, constraints, BitwiseU16Operation.constraints,
    U16toU8OperationUnsafe.constraints, sub_eq_zero]

section opcodes

@[simp] def is_xor := Main[48] = 1 ∧ Main[31] = 0
@[simp] def is_xori := Main[48] = 1 ∧ Main[31] = 1
@[simp] def is_or := Main[49] = 1 ∧ Main[31] = 0
@[simp] def is_ori := Main[49] = 1 ∧ Main[31] = 1
@[simp] def is_and := Main[50] = 1 ∧ Main[31] = 0
@[simp] def is_andi := Main[50] = 1 ∧ Main[31] = 1


lemma single_op : List.Forall SP1Constraint.toProp (constraints Main) →
  (Main[48] = 1 → Main[49] = 0 ∧ Main[50] = 0) ∧
  (Main[49] = 1 → Main[48] = 0 ∧ Main[50] = 0) ∧
  (Main[50] = 1 → Main[48] = 0 ∧ Main[49] = 0)
   := by
  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_bop, cpu, alu, b_xor, b_or, b_and, one_of_ops ⟩ := cstrs
  clear h_bop cpu alu
  aesop

end opcodes

section is_real

lemma xor_real : Main[48] = 1 → is_real Main := by simp [is_real]; aesop
lemma or_real : Main[49] = 1 → is_real Main := by simp [is_real]; aesop
lemma and_real : Main[50] = 1 → is_real Main := by simp [is_real]; aesop

end is_real

section entailed_constraints

lemma register_bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let imm := Main[31]
  Main[6] < 32 ∧ Main[14] < 32 ∧ (imm = 0 → Main[21] < 32) ∧ Main[3] < 65536 := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_bop, cpu, alu, b_xor, b_or, b_and, one_of_ops ⟩ := cstrs
  clear h_bop cpu
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  · obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18 ⟩ := alu
    clear h18
    rcases real with xor | or | and <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq] <;>
    rcases b_imm <;> simp_all
  · clear alu; rcases real with xor | or | and <;> simp_all

lemma immediate_bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let imm := Main[31]
  (imm = 1 →
    Main[21] = Main[25] ∧ Main[22] = Main[26] ∧ Main[23] = Main[27] ∧ Main[24] = Main[28] ∧
    Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] = BitVec.signExtend 64 (BitVec.ofNat 12 Main[21])) := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_bop, cpu, alu, b_xor, b_or, b_and, one_of_ops ⟩ := cstrs
  clear h_bop cpu
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  · obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19 ⟩ := alu
    clear h18; rcases real with xor | or | and <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
  · clear alu; rcases real with xor | or | and <;> simp_all

lemma op_a_is_0 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
  (Main[6] = 0 → ret_val[0] = 0 ∧ ret_val[1] = 0 ∧ ret_val[2] = 0 ∧ ret_val[3] = 0) := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_bop, cpu, alu, b_xor, b_or, b_and, one_of_ops ⟩ := cstrs
  clear h_bop cpu
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  · obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9 ⟩ := alu
    intro ret_val hm6; simp_all
  · clear alu; rcases real with xor | or | and <;> simp_all

lemma ops_U64_b_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_bop, cpu, alu, b_xor, b_or, b_and, one_of_ops ⟩ := cstrs
  clear h_bop cpu
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  · simp only [and_assoc] at alu
    obtain ⟨ h0, h1, h2, h21, h22, h23, h24, h4, h5, b_imm, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19 ⟩ := alu
    simp_all
    clear h1
    rcases real with xor | or | and <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq] <;>
    rcases b_imm <;> simp_all <;> apply Word.isU64_of_cases <;> simp <;>
      {simp_all; clear *- h21 h22 h23 h24 h19; aesop}
  · clear alu; rcases real with xor | or | and <;> simp_all

lemma ops_U64_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
  Word.isU64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]] := by
  intro cstrs real ret_val
  have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs real
  obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
  obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
  have ⟨ sop1, sop2, sop3 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_bop, cpu, alu, b_xor, b_or, b_and, one_of_ops ⟩ := cstrs
  clear cpu alu
  suffices : ret_val[0] < 65536 ∧ ret_val[1] < 65536 ∧ ret_val[2] < 65536 ∧ ret_val[3] < 65536
  · clear *- this; apply Word.isU64_of_cases <;> simp <;> omega
  · rcases real with xor | and | or <;> simp_all
    all_goals {
      subst ret_val
      simp [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints, BitwiseOperation.constraints] at *
      have ⟨ ⟨ ⟨ hr0, hb0, hc0 ⟩, heq_0 ⟩, ⟨ ⟨ hr1, hb1, hc1 ⟩, heq_1 ⟩, ⟨ ⟨ hr2, hb2, hc2 ⟩, heq_2 ⟩,  ⟨ ⟨ hr3, hb3, hc3 ⟩, heq_3 ⟩,
             ⟨ ⟨ hr4, hb4, hc4 ⟩, heq_4 ⟩, ⟨ ⟨ hr5, hb5, hc5 ⟩, heq_5 ⟩, ⟨ ⟨ hr6, hb6, hc6 ⟩, heq_6 ⟩,  ⟨ ⟨ hr7, hb7, hc7 ⟩, heq_7 ⟩  ⟩ := h_bop
      clear *- hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
      repeat rw [Fin.lt_def, Fin.val_add, Fin.val_mul]
      rw [Fin.lt_def] at *; simp_all
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      omega
    }

lemma ops_U64 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
  Word.isU64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]] ∧
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]]
    := by
  intro cstrs real
  constructor
  · exact ops_U64_a Main cstrs real
  · exact ops_U64_b_c Main cstrs real

end entailed_constraints

section operands

@[simp]
def sp1_op_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[6] ?_
  change Main[6] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_b : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[14] ?_
  change Main[14] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 0 → BitVec 5 := by
  intro cstrs real imm
  refine BitVec.ofNatLT Main[21] ?_
  change Main[21] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c_imm : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → BitVec 12 := by
  intro cstrs real imm
  exact BitVec.ofNat 12 Main[21]

end operands

section xor

lemma spec.xor (h : is_xor Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
    Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .XOR
  := by
    intro cstrs
    obtain ⟨ eq_xor, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (xor_real Main eq_xor)
    obtain ⟨ sop_1, sop_2, sop_3 ⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨ h_bop, rest ⟩ := cstrs
    simp_all [← Word.eq_mk_getElem]
    exact BitwiseU16Operation.spec.xor is_U64_b is_U64_c h_bop

end xor

section xori

lemma spec.xori (h : is_xori Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
    Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]] = execute_ITYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .XORI
  := by
    intro cstrs
    obtain ⟨ eq_xor, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (xor_real Main eq_xor)
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    have immediate_bounds := immediate_bounds Main cstrs (xor_real Main eq_xor)
    rw [eq_imm] at immediate_bounds; simp_all
    obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3, eq_c ⟩ := immediate_bounds
    obtain ⟨ sop_1, sop_2, sop_3 ⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨ h_bop, rest ⟩ := cstrs
    simp_all [← Word.eq_mk_getElem]
    exact BitwiseU16Operation.spec.xor is_U64_b is_U64_c h_bop

end xori

section or

lemma spec.or (h : is_or Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
    Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .OR
  := by
    intro cstrs
    obtain ⟨ eq_or, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (or_real Main eq_or)
    obtain ⟨ sop_1, sop_2, sop_3 ⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨ h_bop, rest ⟩ := cstrs
    simp_all [← Word.eq_mk_getElem]
    exact BitwiseU16Operation.spec.or is_U64_b is_U64_c h_bop

end or

section ori

lemma spec.ori (h : is_ori Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
    Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]] = execute_ITYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .ORI
  := by
    intro cstrs
    obtain ⟨ eq_or, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (or_real Main eq_or)
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    have immediate_bounds := immediate_bounds Main cstrs (or_real Main eq_or)
    rw [eq_imm] at immediate_bounds; simp_all
    obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3, eq_c ⟩ := immediate_bounds
    obtain ⟨ sop_1, sop_2, sop_3 ⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨ h_bop, rest ⟩ := cstrs
    simp_all [← Word.eq_mk_getElem]
    exact BitwiseU16Operation.spec.or is_U64_b is_U64_c h_bop

end ori

section and

lemma spec.and (h : is_and Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
    Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .AND
  := by
    intro cstrs
    obtain ⟨ eq_and, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (and_real Main eq_and)
    obtain ⟨ sop_1, sop_2, sop_3 ⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨ h_bop, rest ⟩ := cstrs
    simp_all [← Word.eq_mk_getElem]
    exact BitwiseU16Operation.spec.and is_U64_b is_U64_c h_bop

end and

section andi

lemma spec.andi (h : is_andi Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
    Word.toBitVec64 #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]] = execute_ITYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .ANDI
  := by
    intro cstrs
    obtain ⟨ eq_and, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (and_real Main eq_and)
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    have immediate_bounds := immediate_bounds Main cstrs (and_real Main eq_and)
    rw [eq_imm] at immediate_bounds; simp_all
    obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3, eq_c ⟩ := immediate_bounds
    obtain ⟨ sop_1, sop_2, sop_3 ⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨ h_bop, rest ⟩ := cstrs
    simp_all [← Word.eq_mk_getElem]
    exact BitwiseU16Operation.spec.and is_U64_b is_U64_c h_bop

end andi

end Bitwise
