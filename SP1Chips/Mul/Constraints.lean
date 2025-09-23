import SP1Operations.Operation.MulOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader

namespace Mul

set_option maxHeartbeats 100000000

variable (Main : Vector (Fin BB) 83)
def is_real : Prop := Main[78] = 1 ∨ Main[79] = 1 ∨ Main[80] = 1 ∨ Main[81] = 1 ∨ Main[82] = 1

section constraints

-- Generated Lean code for chip MulChip
@[irreducible] def constraints (Main : Vector (Fin BB) 83) : SP1ConstraintList :=
  let E0 : Fin BB := Main[78] + Main[79]
  let E1 : Fin BB := E0 + Main[80]
  let E2 : Fin BB := E1 + Main[81]
  let E3 : Fin BB := E2 + Main[82]
  let CS0 : SP1ConstraintList := MulOperation.constraints #v[Main[29], Main[30], Main[31], Main[32]] #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[22], Main[23], Main[24], Main[25]] { carry := #v[Main[33], Main[34], Main[35], Main[36], Main[37], Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47], Main[48]], product := #v[Main[49], Main[50], Main[51], Main[52], Main[53], Main[54], Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61], Main[62], Main[63], Main[64]], b_lower_byte := { low_bytes := #v[Main[65], Main[66], Main[67], Main[68]] }, c_lower_byte := { low_bytes := #v[Main[69], Main[70], Main[71], Main[72]] }, b_msb := Main[73], c_msb := Main[74], product_msb := { msb := Main[75] }, b_sign_extend := Main[76], c_sign_extend := Main[77] } E3 Main[78] Main[79] Main[82] Main[80] Main[81]
  let E4 : Fin BB := Main[78] - 1
  let E5 : Fin BB := Main[78] * E4
  let E6 : Fin BB := Main[79] - 1
  let E7 : Fin BB := Main[79] * E6
  let E8 : Fin BB := Main[80] - 1
  let E9 : Fin BB := Main[80] * E8
  let E10 : Fin BB := Main[82] - 1
  let E11 : Fin BB := Main[82] * E10
  let E12 : Fin BB := Main[81] - 1
  let E13 : Fin BB := Main[81] * E12
  let E14 : Fin BB := E3 - 1
  let E15 : Fin BB := E3 * E14
  let E16 : Fin BB := Main[78] * 11
  let E17 : Fin BB := Main[79] * 12
  let E18 : Fin BB := E16 + E17
  let E19 : Fin BB := Main[80] * 13
  let E20 : Fin BB := E18 + E19
  let E21 : Fin BB := Main[81] * 14
  let E22 : Fin BB := E20 + E21
  let E23 : Fin BB := Main[82] * 47
  let E24 : Fin BB := E22 + E23
  let E25 : Fin BB := Main[78] * 0
  let E26 : Fin BB := Main[79] * 1
  let E27 : Fin BB := E25 + E26
  let E28 : Fin BB := Main[80] * 3
  let E29 : Fin BB := E27 + E28
  let E30 : Fin BB := Main[81] * 2
  let E31 : Fin BB := E29 + E30
  let E32 : Fin BB := Main[82] * 0
  let E33 : Fin BB := E31 + E32
  let E34 : Fin BB := Main[78] * 1
  let E35 : Fin BB := Main[79] * 1
  let E36 : Fin BB := E34 + E35
  let E37 : Fin BB := Main[80] * 1
  let E38 : Fin BB := E36 + E37
  let E39 : Fin BB := Main[81] * 1
  let E40 : Fin BB := E38 + E39
  let E41 : Fin BB := Main[82] * 1
  let E42 : Fin BB := E40 + E41
  let E43 : Fin BB := Main[78] * 51
  let E44 : Fin BB := Main[79] * 51
  let E45 : Fin BB := E43 + E44
  let E46 : Fin BB := Main[80] * 51
  let E47 : Fin BB := E45 + E46
  let E48 : Fin BB := Main[81] * 51
  let E49 : Fin BB := E47 + E48
  let E50 : Fin BB := Main[82] * 59
  let E51 : Fin BB := E49 + E50
  let E52 : Fin BB := Main[78] * 8
  let E53 : Fin BB := Main[79] * 8
  let E54 : Fin BB := E52 + E53
  let E55 : Fin BB := Main[80] * 8
  let E56 : Fin BB := E54 + E55
  let E57 : Fin BB := Main[81] * 8
  let E58 : Fin BB := E56 + E57
  let E59 : Fin BB := Main[82] * 8
  let E60 : Fin BB := E58 + E59
  let E61 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E61, Main[4], Main[5]] 8 E3
  let E62 : Fin BB := Main[1] * 65536
  let E63 : Fin BB := Main[2] + E62
  let CS2 : SP1ConstraintList := RTypeReader.constraints Main[0] E63 #v[Main[3], Main[4], Main[5]] E24 #v[E60, E51, E33, E42] #v[Main[29], Main[30], Main[31], Main[32]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } }, is_trusted := Main[28] } E3
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E11),
    (.assertZero E13),
    (.assertZero E15),
  ]

end constraints

lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (MulOperation.constraints #v[Main[29], Main[30], Main[31], Main[32]] #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[22], Main[23], Main[24], Main[25]] { carry := #v[Main[33], Main[34], Main[35], Main[36], Main[37], Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47], Main[48]], product := #v[Main[49], Main[50], Main[51], Main[52], Main[53], Main[54], Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61], Main[62], Main[63], Main[64]], b_lower_byte := { low_bytes := #v[Main[65], Main[66], Main[67], Main[68]] }, c_lower_byte := { low_bytes := #v[Main[69], Main[70], Main[71], Main[72]] }, b_msb := Main[73], c_msb := Main[74], product_msb := { msb := Main[75] }, b_sign_extend := Main[76], c_sign_extend := Main[77] } (Main[78] + Main[79] + Main[80] + Main[81] + Main[82]) Main[78] Main[79] Main[82] Main[80] Main[81]) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[78] + Main[79] + Main[80] + Main[81] + Main[82])) ∧
    List.Forall SP1Constraint.toProp (RTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[78] * 11 + Main[79] * 12 + Main[80] * 13 + Main[81] * 14 + Main[82] * 47) #v[Main[78] * 8 + Main[79] * 8 + Main[80] * 8 + Main[81] * 8 + Main[82] * 8,
          Main[78] * 51 + Main[79] * 51 + Main[80] * 51 + Main[81] * 51 + Main[82] * 59,
          Main[79] + Main[80] * 3 + Main[81] * 2, Main[78] + Main[79] + Main[80] + Main[81] + Main[82]] #v[Main[29], Main[30], Main[31], Main[32]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } , is_trusted := Main[28] } (Main[78] + Main[79] + Main[80] + Main[81] + Main[82])) ∧
    (Main[78] = 0 ∨ Main[78] = 1) ∧
    (Main[79] = 0 ∨ Main[79] = 1) ∧
    (Main[80] = 0 ∨ Main[80] = 1) ∧
    (Main[82] = 0 ∨ Main[82] = 1) ∧
    (Main[81] = 0 ∨ Main[81] = 1) ∧
    (Main[78] + Main[79] + Main[80] + Main[81] + Main[82] = 0 ∨ Main[78] + Main[79] + Main[80] + Main[81] + Main[82] - 1 = 0) --∧
  := by
    simp [constraints, sub_eq_zero]

section opcodes

@[simp] def is_mul := Main[78] = 1 ∧ Main[31] = 0
@[simp] def is_mulh := Main[79] = 1 ∧ Main[31] = 0
@[simp] def is_mulhu := Main[80] = 1 ∧ Main[31] = 0
@[simp] def is_mulhsu := Main[81] = 1 ∧ Main[31] = 0
@[simp] def is_mulw := Main[82] = 1 ∧ Main[31] = 0

lemma single_op : List.Forall SP1Constraint.toProp (constraints Main) →
  (Main[78] = 1 → Main[79] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0 ∧ Main[82] = 0) ∧
  (Main[79] = 1 → Main[78] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0 ∧ Main[82] = 0) ∧
  (Main[80] = 1 → Main[78] = 0 ∧ Main[79] = 0 ∧ Main[81] = 0 ∧ Main[82] = 0) ∧
  (Main[81] = 1 → Main[78] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0 ∧ Main[82] = 0) ∧
  (Main[82] = 1 → Main[78] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0)
   := by
  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, rest ⟩ := cstrs
  clear h_mop cpu alu
  aesop

end opcodes

section is_real

lemma mul_real : Main[78] = 1 → is_real Main := by simp [is_real]; tauto
lemma mulh_real : Main[79] = 1 → is_real Main := by simp [is_real]; tauto
lemma mulhu_real : Main[80] = 1 → is_real Main := by simp [is_real]; tauto
lemma mulhsu_real : Main[81] = 1 → is_real Main := by simp [is_real]; tauto
lemma mulw_real : Main[82] = 1 → is_real Main := by simp [is_real]; tauto

end is_real

section entailed_constraints

lemma register_bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let imm := Main[31]
  Main[6] < 32 ∧ Main[14] < 32 ∧ (imm = 0 → Main[21] < 32) ∧ Main[3] < 65536
    := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, one_of_ops, rest ⟩ := cstrs
  clear h_mop cpu rest
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  . obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19 ⟩ := alu
    clear h18
    rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
  . clear alu; rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all

lemma op_a_is_0 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  (Main[6] = 0 → Main[32] = 0 ∧ Main[33] = 0 ∧ Main[34] = 0 ∧ Main[35] = 0) := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, one_of_ops, rest ⟩ := cstrs
  clear h_mop cpu rest
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  . obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19 ⟩ := alu
    intro hm6; simp_all
  . clear alu; rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all

lemma ops_U64_b_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, one_of_ops, rest ⟩ := cstrs
  clear h_mop cpu rest
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  . obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19 ⟩ := alu
    simp_all; clear h18
    rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
  . clear alu; rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all

end entailed_constraints

section operands

@[simp]
def sp1_op_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[6] ?_
  show Main[6] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_b : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[14] ?_
  show Main[14] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 0 → BitVec 5 := by
  intro cstrs real imm
  refine BitVec.ofNatLT Main[21] ?_
  show Main[21] < 32
  have := register_bounds Main cstrs real
  tauto

end operands

section mul

lemma spec.mul (h : is_mul Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[25], Main[26], Main[27], Main[28]]) .MUL
  := by
    intro cstrs
    obtain ⟨ eq_mul, eq_imm ⟩ := h
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs (mul_real Main eq_mul)
    obtain ⟨ sop_1, sop_2, sop_3, sop_4, sop_5 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    obtain ⟨ h_mop, rest ⟩ := cstrs
    simp_all

    have ⟨ _, spec ⟩ := MulOperation.spec.mul is_U64_b is_U64_c h_mop (by simp)
    rw [spec, exec_MUL_pure_bv_to_bw _ _ _ is_U64_b is_U64_c]

end mul

section mulh

lemma spec.mulh (h : is_mulh Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[25], Main[26], Main[27], Main[28]]) .MULH
  := by
    intro cstrs
    obtain ⟨ eq_mulh, eq_imm ⟩ := h
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs (mulh_real Main eq_mulh)
    obtain ⟨ sop_1, sop_2, sop_3, sop_4, sop_5 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    obtain ⟨ h_mop, rest ⟩ := cstrs
    simp_all

    have ⟨ _, spec ⟩ := MulOperation.spec.mulh is_U64_b is_U64_c h_mop (by simp)
    rw [spec, exec_MUL_pure_bv_to_bw _ _ _ is_U64_b is_U64_c]

end mulh

section mulhu

lemma spec.mulhu (h : is_mulhu Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[25], Main[26], Main[27], Main[28]]) .MULHU
  := by
    intro cstrs
    obtain ⟨ eq_mulhu, eq_imm ⟩ := h
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs (mulhu_real Main eq_mulhu)
    obtain ⟨ sop_1, sop_2, sop_3, sop_4, sop_5 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    obtain ⟨ h_mop, rest ⟩ := cstrs
    simp_all

    have ⟨ _, spec ⟩ := MulOperation.spec.mulhu is_U64_b is_U64_c h_mop (by simp)
    rw [spec, exec_MUL_pure_bv_to_bw _ _ _ is_U64_b is_U64_c]

end mulhu

section mulhsu

lemma spec.mulhsu (h : is_mulhsu Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[25], Main[26], Main[27], Main[28]]) .MULHSU
  := by
    intro cstrs
    obtain ⟨ eq_mulhsu, eq_imm ⟩ := h
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs (mulhsu_real Main eq_mulhsu)
    obtain ⟨ sop_1, sop_2, sop_3, sop_4, sop_5 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    obtain ⟨ h_mop, rest ⟩ := cstrs
    simp_all

    have ⟨ _, spec ⟩ := MulOperation.spec.mulhsu is_U64_b is_U64_c h_mop (by simp)
    rw [spec, exec_MUL_pure_bv_to_bw _ _ _ is_U64_b is_U64_c]

end mulhsu

section mulw

lemma spec.mulw (h : is_mulw Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_MULW_pure_bhw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]).low (Word.toBWord #v[Main[25], Main[26], Main[27], Main[28]]).low
  := by
    intro cstrs
    obtain ⟨ eq_mulw, eq_imm ⟩ := h
    have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs (mulw_real Main eq_mulw)
    obtain ⟨ sop_1, sop_2, sop_3, sop_4, sop_5 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    obtain ⟨ h_mop, rest ⟩ := cstrs
    simp_all

    have ⟨ _, spec ⟩ := MulOperation.spec.mulw is_U64_b is_U64_c h_mop (by simp)
    rw [spec, exec_MULW_pure_bv_to_bhw _ _ is_U64_b is_U64_c]

end mulw

end Mul
