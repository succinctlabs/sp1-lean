import SP1Operations.Operation.MulOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader

namespace Mul

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 82)
def is_real : Prop := Main[77] = 1 ∨ Main[78] = 1 ∨ Main[79] = 1 ∨ Main[80] = 1 ∨ Main[81] = 1

section constraints

-- Generated Lean code for chip MulChip
@[irreducible] def constraints (Main : Vector (Fin KB) 82) : SP1ConstraintList :=
  let E0 : Fin KB := Main[77] + Main[78]
  let E1 : Fin KB := E0 + Main[79]
  let E2 : Fin KB := E1 + Main[80]
  let E3 : Fin KB := E2 + Main[81]
  let CS0 : SP1ConstraintList := MulOperation.constraints #v[Main[28], Main[29], Main[30], Main[31]] #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[22], Main[23], Main[24], Main[25]] { carry := #v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37], Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]], product := #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54], Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61], Main[62], Main[63]], b_lower_byte := { low_bytes := #v[Main[64], Main[65], Main[66], Main[67]] }, c_lower_byte := { low_bytes := #v[Main[68], Main[69], Main[70], Main[71]] }, b_msb := Main[72], c_msb := Main[73], product_msb := { msb := Main[74] }, b_sign_extend := Main[75], c_sign_extend := Main[76] } E3 Main[77] Main[78] Main[81] Main[79] Main[80]
  let E4 : Fin KB := Main[77] - 1
  let E5 : Fin KB := Main[77] * E4
  let E6 : Fin KB := Main[78] - 1
  let E7 : Fin KB := Main[78] * E6
  let E8 : Fin KB := Main[79] - 1
  let E9 : Fin KB := Main[79] * E8
  let E10 : Fin KB := Main[81] - 1
  let E11 : Fin KB := Main[81] * E10
  let E12 : Fin KB := Main[80] - 1
  let E13 : Fin KB := Main[80] * E12
  let E14 : Fin KB := E3 - 1
  let E15 : Fin KB := E3 * E14
  let E16 : Fin KB := Main[77] * 11
  let E17 : Fin KB := Main[78] * 12
  let E18 : Fin KB := E16 + E17
  let E19 : Fin KB := Main[79] * 13
  let E20 : Fin KB := E18 + E19
  let E21 : Fin KB := Main[80] * 14
  let E22 : Fin KB := E20 + E21
  let E23 : Fin KB := Main[81] * 24
  let E24 : Fin KB := E22 + E23
  let E25 : Fin KB := Main[77] * 0
  let E26 : Fin KB := Main[78] * 1
  let E27 : Fin KB := E25 + E26
  let E28 : Fin KB := Main[79] * 3
  let E29 : Fin KB := E27 + E28
  let E30 : Fin KB := Main[80] * 2
  let E31 : Fin KB := E29 + E30
  let E32 : Fin KB := Main[81] * 0
  let E33 : Fin KB := E31 + E32
  let E34 : Fin KB := Main[77] * 1
  let E35 : Fin KB := Main[78] * 1
  let E36 : Fin KB := E34 + E35
  let E37 : Fin KB := Main[79] * 1
  let E38 : Fin KB := E36 + E37
  let E39 : Fin KB := Main[80] * 1
  let E40 : Fin KB := E38 + E39
  let E41 : Fin KB := Main[81] * 1
  let E42 : Fin KB := E40 + E41
  let E43 : Fin KB := Main[77] * 51
  let E44 : Fin KB := Main[78] * 51
  let E45 : Fin KB := E43 + E44
  let E46 : Fin KB := Main[79] * 51
  let E47 : Fin KB := E45 + E46
  let E48 : Fin KB := Main[80] * 51
  let E49 : Fin KB := E47 + E48
  let E50 : Fin KB := Main[81] * 59
  let E51 : Fin KB := E49 + E50
  let E52 : Fin KB := Main[77] * 8
  let E53 : Fin KB := Main[78] * 8
  let E54 : Fin KB := E52 + E53
  let E55 : Fin KB := Main[79] * 8
  let E56 : Fin KB := E54 + E55
  let E57 : Fin KB := Main[80] * 8
  let E58 : Fin KB := E56 + E57
  let E59 : Fin KB := Main[81] * 8
  let E60 : Fin KB := E58 + E59
  let E61 : Fin KB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E61, Main[4], Main[5]] 8 E3
  let E62 : Fin KB := Main[1] * 65536
  let E63 : Fin KB := Main[2] + E62
  let CS2 : SP1ConstraintList := RTypeReader.constraints Main[0] E63 #v[Main[3], Main[4], Main[5]] E24 #v[E60, E51, E33, E42] #v[Main[28], Main[29], Main[30], Main[31]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } } E3
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E11),
    (.assertZero E13),
    (.assertZero E15),
    (.assertZero Main[13]),
  ]

end constraints

lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (MulOperation.constraints #v[Main[28], Main[29], Main[30], Main[31]] #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[22], Main[23], Main[24], Main[25]] { carry := #v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37], Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]], product := #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54], Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61], Main[62], Main[63]], b_lower_byte := { low_bytes := #v[Main[64], Main[65], Main[66], Main[67]] }, c_lower_byte := { low_bytes := #v[Main[68], Main[69], Main[70], Main[71]] }, b_msb := Main[72], c_msb := Main[73], product_msb := { msb := Main[74] }, b_sign_extend := Main[75], c_sign_extend := Main[76] } (Main[77] + Main[78] + Main[79] + Main[80] + Main[81]) Main[77] Main[78] Main[81] Main[79] Main[80]) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[77] + Main[78] + Main[79] + Main[80] + Main[81])) ∧
    List.Forall SP1Constraint.toProp (RTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[77] * 11 + Main[78] * 12 + Main[79] * 13 + Main[80] * 14 + Main[81] * 47) #v[Main[77] * 8 + Main[78] * 8 + Main[79] * 8 + Main[80] * 8 + Main[81] * 8,
          Main[77] * 51 + Main[78] * 51 + Main[79] * 51 + Main[80] * 51 + Main[81] * 59,
          Main[78] + Main[79] * 3 + Main[80] * 2, Main[77] + Main[78] + Main[79] + Main[80] + Main[81]] #v[Main[28], Main[29], Main[30], Main[31]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } }  } (Main[77] + Main[78] + Main[79] + Main[80] + Main[81])) ∧
    (Main[77] = 0 ∨ Main[77] = 1) ∧
    (Main[78] = 0 ∨ Main[78] = 1) ∧
    (Main[79] = 0 ∨ Main[79] = 1) ∧
    (Main[81] = 0 ∨ Main[81] = 1) ∧
    (Main[80] = 0 ∨ Main[80] = 1) ∧
    (Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 0 ∨ Main[77] + Main[78] + Main[79] + Main[80] + Main[81] - 1 = 0) --∧
  := by
    stop
    simp [constraints, sub_eq_zero]

section opcodes

@[simp] def is_mul := Main[77] = 1 ∧ Main[30] = 0
@[simp] def is_mulh := Main[78] = 1 ∧ Main[30] = 0
@[simp] def is_mulhu := Main[79] = 1 ∧ Main[30] = 0
@[simp] def is_mulhsu := Main[80] = 1 ∧ Main[30] = 0
@[simp] def is_mulw := Main[81] = 1 ∧ Main[30] = 0

lemma single_op : List.Forall SP1Constraint.toProp (constraints Main) →
  (Main[77] = 1 → Main[78] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0) ∧
  (Main[78] = 1 → Main[77] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0) ∧
  (Main[79] = 1 → Main[77] = 0 ∧ Main[78] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0) ∧
  (Main[80] = 1 → Main[77] = 0 ∧ Main[78] = 0 ∧ Main[79] = 0 ∧ Main[81] = 0) ∧
  (Main[81] = 1 → Main[77] = 0 ∧ Main[78] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0)
   := by
  stop
  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, rest ⟩ := cstrs
  clear h_mop cpu alu
  aesop

end opcodes

section is_real

lemma mul_real : Main[77] = 1 → is_real Main := by simp [is_real]; tauto
lemma mulh_real : Main[78] = 1 → is_real Main := by simp [is_real]; tauto
lemma mulhu_real : Main[79] = 1 → is_real Main := by simp [is_real]; tauto
lemma mulhsu_real : Main[80] = 1 → is_real Main := by simp [is_real]; tauto
lemma mulw_real : Main[81] = 1 → is_real Main := by simp [is_real]; tauto

end is_real

section entailed_constraints

lemma register_bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Main[6] < 32 ∧ Main[14] < 32 ∧ (Main[30] = 0 → Main[21] < 32) ∧ Main[3] < 65536
    := by
  stop
  intro cstrs real
  have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, rest ⟩ := cstrs
  clear h_mop cpu rest
  rw [RTypeReader.allHold_constraints_iff_is_real] at alu
  simp only at alu
  · obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9 ⟩ := alu
    rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
  · clear alu; rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all

lemma op_a_is_0 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  (Main[6] = 0 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0) := by
  stop
  intro cstrs real
  have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, rest ⟩ := cstrs
  clear h_mop cpu rest
  rw [RTypeReader.allHold_constraints_iff_is_real] at alu
  simp only at alu
  · obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9 ⟩ := alu
    intro hm6; simp_all
  · clear alu; rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all

lemma ops_U64_b_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  stop
  intro cstrs real
  have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, rest ⟩ := cstrs
  clear h_mop cpu rest
  rw [RTypeReader.allHold_constraints_iff_is_real] at alu
  · obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9 ⟩ := alu
    simp_all
  · clear alu; rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all

end entailed_constraints

section operands

@[simp]
def sp1_op_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  stop
  intro cstrs real
  refine BitVec.ofNatLT Main[6] ?_
  change Main[6] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_b : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  stop
  intro cstrs real
  refine BitVec.ofNatLT Main[14] ?_
  change Main[14] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[30] = 0 → BitVec 5 := by
  stop
  intro cstrs real imm
  refine BitVec.ofNatLT Main[21] ?_
  change Main[21] < 32
  have := register_bounds Main cstrs real
  tauto

end operands

section mul

lemma spec.mul (h : is_mul Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[22], Main[23], Main[24], Main[25]]) .MUL
  := by
    have _ := h
    stop
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

lemma spec.mulh (h : is_mulh Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[22], Main[23], Main[24], Main[25]]) .MULH
  := by
    have _ := h
    stop
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

lemma spec.mulhu (h : is_mulhu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[22], Main[23], Main[24], Main[25]]) .MULHU
  := by
    have _ := h
    stop
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

lemma spec.mulhsu (h : is_mulhsu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[22], Main[23], Main[24], Main[25]]) .MULHSU
  := by
    have _ := h
    stop
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

lemma spec.mulw (h : is_mulw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = execute_MULW_pure_bhw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]).low (Word.toBWord #v[Main[22], Main[23], Main[24], Main[25]]).low
  := by
    have _ := h
    stop
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
