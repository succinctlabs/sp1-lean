import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace Lt

section constraints

-- Generated Lean code for chip LtChip
@[irreducible] def constraints (Main : Vector (Fin KB) 44) : SP1ConstraintList :=
  let E0 : Fin KB := Main[32] + Main[32]
  let E1 : Fin KB := Main[32] - 1
  let E2 : Fin KB := Main[32] * E1
  let E3 : Fin KB := Main[32] - 1
  let E4 : Fin KB := Main[32] * E3
  let E5 : Fin KB := E0 - 1
  let E6 : Fin KB := E0 * E5
  let CS0 : SP1ConstraintList := LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[33] }, u16_flags := #v[Main[34], Main[35], Main[36], Main[37]], not_eq_inv := Main[38], comparison_limbs := #v[Main[39], Main[40]] }, b_msb := { msb := Main[41] }, c_msb := { msb := Main[42] } } Main[32] E0
  let E7 : Fin KB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E7, Main[4], Main[5]] 8 E0
  let E8 : Fin KB := Main[32] * 9
  let E9 : Fin KB := Main[32] * 10
  let E10 : Fin KB := E8 + E9
  let E11 : Fin KB := Main[32] * 2
  let E12 : Fin KB := Main[32] * 3
  let E13 : Fin KB := E11 + E12
  let E14 : Fin KB := Main[32] * 0
  let E15 : Fin KB := Main[32] * 0
  let E16 : Fin KB := E14 + E15
  let E17 : Fin KB := Main[32] * 51
  let E18 : Fin KB := Main[32] * 51
  let E19 : Fin KB := E17 + E18
  let E20 : Fin KB := 32 * Main[31]
  let E21 : Fin KB := E19 - E20
  let E22 : Fin KB := Main[32] * 8
  let E23 : Fin KB := Main[32] * 8
  let E24 : Fin KB := E22 + E23
  let E25 : Fin KB := 4 * Main[31]
  let E26 : Fin KB := E24 - E25
  let E27 : Fin KB := Main[1] * 65536
  let E28 : Fin KB := Main[2] + E27
  let E29 : Fin KB := 0 + Main[33]
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E28 #v[Main[3], Main[4], Main[5]] E10 #v[E26, E21, E13, E16] #v[E29, 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E0
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E2),
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero Main[13]),
  ]

end constraints


@[simp] def is_slt (Main : Vector (Fin KB) 44) := Main[32] = 1 ∧ Main[31] = 0
@[simp] def is_sltu (Main : Vector (Fin KB) 44) := Main[33] = 1 ∧ Main[31] = 0
@[simp] def is_slti (Main : Vector (Fin KB) 44) := Main[32] = 1 ∧ Main[31] = 1
@[simp] def is_sltiu (Main : Vector (Fin KB) 44) := Main[33] = 1 ∧ Main[31] = 1

lemma allHold_constraints_iff_slt (h : is_slt Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[32] * 9 + Main[33] * 10)
      #v[8 + Main[33] * 8, 51 + Main[33] * 51, 2 + Main[33] * 3, 0] #v[Main[34], 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[32] + Main[33])) ∧
    Main[33] = 0 --∧ Main[34] = 51
   := by
  have _ := h
  stop
  simp_all [constraints]
  intros
  omega

lemma allHold_constraints_iff_sltu (h : is_sltu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[32] * 9 + Main[33] * 10)
      #v[Main[32] * 8 + 8, Main[32] * 51 + 51, Main[32] * 2 + 3, 0] #v[Main[34], 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[32] + Main[33])) ∧
    Main[32] = 0 --∧ Main[33] = 51
   := by
  have _ := h
  stop
  simp_all [constraints]
  intros
  omega

lemma allHold_constraints_iff_slti (h : is_slti Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[32] * 9 + Main[33] * 10)
      #v[8 + Main[33] * 8 - 4, 51 + Main[33] * 51 - 32, 2 + Main[33] * 3, 0] #v[Main[34], 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[32] + Main[33])) ∧
    Main[33] = 0 --∧ Main[33] = 19
   := by
  have _ := h
  stop
  simp_all [constraints]
  intros
  omega

lemma allHold_constraints_iff_sltiu (h : is_sltiu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[32] * 9 + Main[33] * 10)
     #v[Main[32] * 8 + 8 - 4, Main[32] * 51 + 51 - 32, Main[32] * 2 + 3, 0] #v[Main[34], 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[32] + Main[33])) ∧
    Main[32] = 0 --∧ Main[33] = 19
   := by
  have _ := h
  stop
  simp_all [constraints]
  intros
  omega

end Lt
