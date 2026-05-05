import SP1Operations.Operation.MulOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader

namespace Mul

variable (Main : Vector (Fin KB) 82)
def is_real : Prop := Main[77] = 1 ∨ Main[78] = 1 ∨ Main[79] = 1 ∨ Main[80] = 1 ∨ Main[81] = 1

section constraints

-- Generated Lean code for chip MulChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 82) : SP1ConstraintList F :=
  let E0 : F := Main[77] + Main[78]
  let E1 : F := E0 + Main[79]
  let E2 : F := E1 + Main[80]
  let E3 : F := E2 + Main[81]
  let CS0 : SP1ConstraintList F := MulOperation.constraints #v[Main[28], Main[29], Main[30], Main[31]] #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[22], Main[23], Main[24], Main[25]] { carry := #v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37], Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]], product := #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54], Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61], Main[62], Main[63]], b_lower_byte := { low_bytes := #v[Main[64], Main[65], Main[66], Main[67]] }, c_lower_byte := { low_bytes := #v[Main[68], Main[69], Main[70], Main[71]] }, b_msb := Main[72], c_msb := Main[73], product_msb := { msb := Main[74] }, b_sign_extend := Main[75], c_sign_extend := Main[76] } E3 Main[77] Main[78] Main[81] Main[79] Main[80]
  let E4 : F := Main[77] - 1
  let E5 : F := Main[77] * E4
  let E6 : F := Main[78] - 1
  let E7 : F := Main[78] * E6
  let E8 : F := Main[79] - 1
  let E9 : F := Main[79] * E8
  let E10 : F := Main[81] - 1
  let E11 : F := Main[81] * E10
  let E12 : F := Main[80] - 1
  let E13 : F := Main[80] * E12
  let E14 : F := E3 - 1
  let E15 : F := E3 * E14
  let E16 : F := Main[77] * 11
  let E17 : F := Main[78] * 12
  let E18 : F := E16 + E17
  let E19 : F := Main[79] * 13
  let E20 : F := E18 + E19
  let E21 : F := Main[80] * 14
  let E22 : F := E20 + E21
  let E23 : F := Main[81] * 24
  let E24 : F := E22 + E23
  let E25 : F := Main[77] * 0
  let E26 : F := Main[78] * 1
  let E27 : F := E25 + E26
  let E28 : F := Main[79] * 3
  let E29 : F := E27 + E28
  let E30 : F := Main[80] * 2
  let E31 : F := E29 + E30
  let E32 : F := Main[81] * 0
  let E33 : F := E31 + E32
  let E34 : F := Main[77] * 1
  let E35 : F := Main[78] * 1
  let E36 : F := E34 + E35
  let E37 : F := Main[79] * 1
  let E38 : F := E36 + E37
  let E39 : F := Main[80] * 1
  let E40 : F := E38 + E39
  let E41 : F := Main[81] * 1
  let E42 : F := E40 + E41
  let E43 : F := Main[77] * 51
  let E44 : F := Main[78] * 51
  let E45 : F := E43 + E44
  let E46 : F := Main[79] * 51
  let E47 : F := E45 + E46
  let E48 : F := Main[80] * 51
  let E49 : F := E47 + E48
  let E50 : F := Main[81] * 59
  let E51 : F := E49 + E50
  let E52 : F := Main[77] * 8
  let E53 : F := Main[78] * 8
  let E54 : F := E52 + E53
  let E55 : F := Main[79] * 8
  let E56 : F := E54 + E55
  let E57 : F := Main[80] * 8
  let E58 : F := E56 + E57
  let E59 : F := Main[81] * 8
  let E60 : F := E58 + E59
  let E61 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E61, Main[4], Main[5]] 8 E3
  let E62 : F := Main[1] * 65536
  let E63 : F := Main[2] + E62
  let CS2 : SP1ConstraintList F := RTypeReader.constraints Main[0] E63 #v[Main[3], Main[4], Main[5]] E24 #v[E60, E51, E33, E42] #v[Main[28], Main[29], Main[30], Main[31]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } } E3
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
    List.Forall SP1Constraint.toProp (RTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[77] * 11 + Main[78] * 12 + Main[79] * 13 + Main[80] * 14 + Main[81] * 24) #v[Main[77] * 8 + Main[78] * 8 + Main[79] * 8 + Main[80] * 8 + Main[81] * 8,
          Main[77] * 51 + Main[78] * 51 + Main[79] * 51 + Main[80] * 51 + Main[81] * 59,
          Main[78] + Main[79] * 3 + Main[80] * 2, Main[77] + Main[78] + Main[79] + Main[80] + Main[81]] #v[Main[28], Main[29], Main[30], Main[31]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } }  } (Main[77] + Main[78] + Main[79] + Main[80] + Main[81])) ∧
    (Main[77] = 0 ∨ Main[77] = 1) ∧
    (Main[78] = 0 ∨ Main[78] = 1) ∧
    (Main[79] = 0 ∨ Main[79] = 1) ∧
    (Main[81] = 0 ∨ Main[81] = 1) ∧
    (Main[80] = 0 ∨ Main[80] = 1) ∧
    (Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 0 ∨ Main[77] + Main[78] + Main[79] + Main[80] + Main[81] - 1 = 0) ∧
    Main[13] = 0
  := by
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
  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, rest⟩ := cstrs
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

set_option linter.style.multiGoal false in
lemma register_bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Main[6] < 32 ∧ Main[14] < 32 ∧ (Main[30] = 0 → Main[21] < 32) ∧ Main[3] < 65536
    := by
  intro cstrs real
  have ⟨sop1, sop2, sop3, sop4, sop5⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, rest⟩ := cstrs
  clear h_mop cpu rest
  rw [RTypeReader.allHold_constraints_iff_is_real] at alu
  simp only at alu
  · obtain ⟨h1, h2, h3, h4, h5, b_imm, h7, h8, h9⟩ := alu
    rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all [Opcode.ofNat, Nat.ble]
  · clear alu; rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all

set_option linter.style.multiGoal false in
lemma op_a_is_0 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  (Main[6] = 0 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0) := by
  intro cstrs real
  have ⟨sop1, sop2, sop3, sop4, sop5⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, rest⟩ := cstrs
  clear h_mop cpu rest
  rw [RTypeReader.allHold_constraints_iff_is_real] at alu
  simp only at alu
  · obtain ⟨h1, h2, h3, h4, h5, b_imm, h7, h8, h9⟩ := alu
    intro hm6; simp_all
  · clear alu; rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all

lemma ops_U64_b_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  intro cstrs real
  have ⟨sop1, sop2, sop3, sop4, sop5⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨h_mop, cpu, alu, b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, rest⟩ := cstrs
  clear h_mop cpu rest
  rw [RTypeReader.allHold_constraints_iff_is_real] at alu
  · obtain ⟨h1, h2, h3, h4, h5, b_imm, h7, h8, h9⟩ := alu
    simp_all
  · clear alu; rcases real with mul | mulh | mulhu | mulhsu | mulw <;> simp_all

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
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[30] = 0 → BitVec 5 := by
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
    intro cstrs
    obtain ⟨eq_mul, eq_imm⟩ := h
    have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs (mul_real Main eq_mul)
    obtain ⟨sop_1, sop_2, sop_3, sop_4, sop_5⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨h_mop, rest⟩ := cstrs
    simp_all
    have ⟨_, spec⟩ := MulOperation.spec.mul is_U64_b is_U64_c h_mop (by simp)
    rw [spec, exec_MUL_pure_bv_to_bw _ _ _ is_U64_b is_U64_c]

end mul

section mulh

lemma spec.mulh (h : is_mulh Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[22], Main[23], Main[24], Main[25]]) .MULH
  := by
    intro cstrs
    obtain ⟨eq_mulh, eq_imm⟩ := h
    have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs (mulh_real Main eq_mulh)
    obtain ⟨sop_1, sop_2, sop_3, sop_4, sop_5⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨h_mop, rest⟩ := cstrs
    simp_all
    have ⟨_, spec⟩ := MulOperation.spec.mulh is_U64_b is_U64_c h_mop (by simp)
    rw [spec, exec_MUL_pure_bv_to_bw _ _ _ is_U64_b is_U64_c]

end mulh

section mulhu

lemma spec.mulhu (h : is_mulhu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[22], Main[23], Main[24], Main[25]]) .MULHU
  := by
    intro cstrs
    obtain ⟨eq_mulhu, eq_imm⟩ := h
    have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs (mulhu_real Main eq_mulhu)
    obtain ⟨sop_1, sop_2, sop_3, sop_4, sop_5⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨h_mop, rest⟩ := cstrs
    simp_all
    have ⟨_, spec⟩ := MulOperation.spec.mulhu is_U64_b is_U64_c h_mop (by simp)
    rw [spec, exec_MUL_pure_bv_to_bw _ _ _ is_U64_b is_U64_c]

end mulhu

section mulhsu

lemma spec.mulhsu (h : is_mulhsu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = execute_MUL_pure_bw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBWord #v[Main[22], Main[23], Main[24], Main[25]]) .MULHSU
  := by
    intro cstrs
    obtain ⟨eq_mulhsu, eq_imm⟩ := h
    have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs (mulhsu_real Main eq_mulhsu)
    obtain ⟨sop_1, sop_2, sop_3, sop_4, sop_5⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨h_mop, rest⟩ := cstrs
    simp_all
    have ⟨_, spec⟩ := MulOperation.spec.mulhsu is_U64_b is_U64_c h_mop (by simp)
    rw [spec, exec_MUL_pure_bv_to_bw _ _ _ is_U64_b is_U64_c]

end mulhsu

section mulw

lemma spec.mulw (h : is_mulw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] = execute_MULW_pure_bhw (Word.toBWord #v[Main[15], Main[16], Main[17], Main[18]]).low (Word.toBWord #v[Main[22], Main[23], Main[24], Main[25]]).low
  := by
    intro cstrs
    obtain ⟨eq_mulw, eq_imm⟩ := h
    have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs (mulw_real Main eq_mulw)
    obtain ⟨sop_1, sop_2, sop_3, sop_4, sop_5⟩ := single_op Main cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨h_mop, rest⟩ := cstrs
    simp_all
    have ⟨_, spec⟩ := MulOperation.spec.mulw is_U64_b is_U64_c h_mop (by simp)
    rw [spec, exec_MULW_pure_bv_to_bhw _ _ is_U64_b is_U64_c]

end mulw

section poly_helpers

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

@[simp] def is_real_poly (Main : Vector (ZMod p) 82) : Prop :=
  Main[77] = 1 ∨ Main[78] = 1 ∨ Main[79] = 1 ∨ Main[80] = 1 ∨ Main[81] = 1

@[simp] def is_mul_poly (Main : Vector (ZMod p) 82) : Prop :=
  Main[77] = 1 ∧ Main[30] = 0
@[simp] def is_mulh_poly (Main : Vector (ZMod p) 82) : Prop :=
  Main[78] = 1 ∧ Main[30] = 0
@[simp] def is_mulhu_poly (Main : Vector (ZMod p) 82) : Prop :=
  Main[79] = 1 ∧ Main[30] = 0
@[simp] def is_mulhsu_poly (Main : Vector (ZMod p) 82) : Prop :=
  Main[80] = 1 ∧ Main[30] = 0
@[simp] def is_mulw_poly (Main : Vector (ZMod p) 82) : Prop :=
  Main[81] = 1 ∧ Main[30] = 0

/-- From `a = 1` and the four other 5-arm flags `∈ {0,1}` and the sum-disjunction
`Σ = 0 ∨ Σ - 1 = 0`, conclude `Σ = 1`. Mirrors `Bitwise.sum_eq_one_of_eq_one_*`
extended to the 5-arm Mul shape. The `_left` variant assumes `a` (the first
slot) is the active variant. -/
lemma sum_eq_one_of_eq_one_left
    {a b c d e : ZMod p}
    (h_a : a = 1)
    (b_b : b = 0 ∨ b = 1) (b_c : c = 0 ∨ c = 1)
    (b_d : d = 0 ∨ d = 1) (b_e : e = 0 ∨ e = 1)
    (one_of : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1) :
    a + b + c + d + e = 1 := by
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  haveI : NeZero p := ⟨by omega⟩
  have h2lt : (2 : ℕ) < p := by omega
  have h3lt : (3 : ℕ) < p := by omega
  have h4lt : (4 : ℕ) < p := by omega
  have h5lt : (5 : ℕ) < p := by omega
  have h1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h2_val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2lt
  have h3_val : (3 : ZMod p).val = 3 := ZMod.val_natCast_of_lt h3lt
  have h4_val : (4 : ZMod p).val = 4 := ZMod.val_natCast_of_lt h4lt
  have h5_val : (5 : ZMod p).val = 5 := ZMod.val_natCast_of_lt h5lt
  have h1_ne : (1 : ZMod p) ≠ 0 := by
    intro h0; have := congrArg ZMod.val h0; rw [h1_val, ZMod.val_zero] at this; omega
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro h0; have := congrArg ZMod.val h0; rw [h2_val, ZMod.val_zero] at this; omega
  have h3_ne : (3 : ZMod p) ≠ 0 := by
    intro h0; have := congrArg ZMod.val h0; rw [h3_val, ZMod.val_zero] at this; omega
  have h4_ne : (4 : ZMod p) ≠ 0 := by
    intro h0; have := congrArg ZMod.val h0; rw [h4_val, ZMod.val_zero] at this; omega
  have h5_ne : (5 : ZMod p) ≠ 0 := by
    intro h0; have := congrArg ZMod.val h0; rw [h5_val, ZMod.val_zero] at this; omega
  rcases one_of with h | h
  · exfalso
    rcases b_b with rfl | rfl <;> rcases b_c with rfl | rfl <;>
      rcases b_d with rfl | rfl <;> rcases b_e with rfl | rfl <;>
      rw [h_a] at h <;>
      first
        | exact h1_ne (by linear_combination h)
        | exact h2_ne (by linear_combination h)
        | exact h3_ne (by linear_combination h)
        | exact h4_ne (by linear_combination h)
        | exact h5_ne (by linear_combination h)
  · linear_combination h

/-- Mid-position variants of `sum_eq_one_of_eq_one_left`. The active flag occupies the
2nd, 3rd, 4th, or 5th slot of the sum. -/
lemma sum_eq_one_of_eq_one_2
    {a b c d e : ZMod p}
    (h_b : b = 1)
    (b_a : a = 0 ∨ a = 1) (b_c : c = 0 ∨ c = 1)
    (b_d : d = 0 ∨ d = 1) (b_e : e = 0 ∨ e = 1)
    (one_of : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1) :
    a + b + c + d + e = 1 := by
  have heq : b + a + c + d + e = 1 := sum_eq_one_of_eq_one_left h_b b_a b_c b_d b_e
    (by rcases one_of with h | h
        · left; linear_combination h
        · right; linear_combination h)
  linear_combination heq

lemma sum_eq_one_of_eq_one_3
    {a b c d e : ZMod p}
    (h_c : c = 1)
    (b_a : a = 0 ∨ a = 1) (b_b : b = 0 ∨ b = 1)
    (b_d : d = 0 ∨ d = 1) (b_e : e = 0 ∨ e = 1)
    (one_of : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1) :
    a + b + c + d + e = 1 := by
  have heq : c + a + b + d + e = 1 := sum_eq_one_of_eq_one_left h_c b_a b_b b_d b_e
    (by rcases one_of with h | h
        · left; linear_combination h
        · right; linear_combination h)
  linear_combination heq

lemma sum_eq_one_of_eq_one_4
    {a b c d e : ZMod p}
    (h_d : d = 1)
    (b_a : a = 0 ∨ a = 1) (b_b : b = 0 ∨ b = 1)
    (b_c : c = 0 ∨ c = 1) (b_e : e = 0 ∨ e = 1)
    (one_of : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1) :
    a + b + c + d + e = 1 := by
  have heq : d + a + b + c + e = 1 := sum_eq_one_of_eq_one_left h_d b_a b_b b_c b_e
    (by rcases one_of with h | h
        · left; linear_combination h
        · right; linear_combination h)
  linear_combination heq

lemma sum_eq_one_of_eq_one_5
    {a b c d e : ZMod p}
    (h_e : e = 1)
    (b_a : a = 0 ∨ a = 1) (b_b : b = 0 ∨ b = 1)
    (b_c : c = 0 ∨ c = 1) (b_d : d = 0 ∨ d = 1)
    (one_of : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1) :
    a + b + c + d + e = 1 := by
  have heq : e + a + b + c + d = 1 := sum_eq_one_of_eq_one_left h_e b_a b_b b_c b_d
    (by rcases one_of with h | h
        · left; linear_combination h
        · right; linear_combination h)
  linear_combination heq

set_option maxHeartbeats 4000000 in
-- Polymorphic mirror of `single_op` (line 118): from the chip-level constraints,
-- only one of `Main[77..81]` can be `1`. Mirrors the KB proof pattern but
-- destructures the constraint list directly via simp+List.forall_append rather
-- than going through a chip-level `iff_poly` lemma. Note constraint compiler
-- emits the boolean assertions in the order `77, 78, 79, 81, 80` (mulw before
-- mulhsu), matching the existing KB iff at line 100-105.
lemma single_op_poly (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main)) :
    (Main[77] = 1 → Main[78] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0) ∧
    (Main[78] = 1 → Main[77] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0) ∧
    (Main[79] = 1 → Main[77] = 0 ∧ Main[78] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0) ∧
    (Main[80] = 1 → Main[77] = 0 ∧ Main[78] = 0 ∧ Main[79] = 0 ∧ Main[81] = 0) ∧
    (Main[81] = 1 → Main[77] = 0 ∧ Main[78] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0) := by
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨_h_mop, _h_cpu⟩, _h_alu⟩, b_77, b_78, b_79, b_81, b_80, sum_disj, _h_M13⟩ := cstrs
  -- Map Main[77..81] to is_mul/is_mulh/is_mulhu/is_mulhsu/is_mulw and apply
  -- MulOperation.single_op_poly. Note the slot mapping per the constraint
  -- compiler: 77=mul, 78=mulh, 79=mulhu, 80=mulhsu, 81=mulw.
  have h_77 := fun h_77_one => sum_eq_one_of_eq_one_left h_77_one b_78 b_79 b_80 b_81 sum_disj
  have h_78 := fun h_78_one => sum_eq_one_of_eq_one_2 h_78_one b_77 b_79 b_80 b_81 sum_disj
  have h_79 := fun h_79_one => sum_eq_one_of_eq_one_3 h_79_one b_77 b_78 b_80 b_81 sum_disj
  have h_80 := fun h_80_one => sum_eq_one_of_eq_one_4 h_80_one b_77 b_78 b_79 b_81 sum_disj
  have h_81 := fun h_81_one => sum_eq_one_of_eq_one_5 h_81_one b_77 b_78 b_79 b_80 sum_disj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h_one
  · have h_sum : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := h_77 h_one
    have ⟨h78, h81, h79, h80⟩ :=
      (MulOperation.single_op_poly b_77 b_78 b_79 b_80 b_81 h_sum).1 h_one
    exact ⟨h78, h79, h80, h81⟩
  · have h_sum : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := h_78 h_one
    have ⟨h77, h81, h79, h80⟩ :=
      (MulOperation.single_op_poly b_77 b_78 b_79 b_80 b_81 h_sum).2.1 h_one
    exact ⟨h77, h79, h80, h81⟩
  · have h_sum : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := h_79 h_one
    have ⟨h77, h78, h81, h80⟩ :=
      (MulOperation.single_op_poly b_77 b_78 b_79 b_80 b_81 h_sum).2.2.2.1 h_one
    exact ⟨h77, h78, h80, h81⟩
  · have h_sum : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := h_80 h_one
    have ⟨h77, h78, h81, h79⟩ :=
      (MulOperation.single_op_poly b_77 b_78 b_79 b_80 b_81 h_sum).2.2.2.2 h_one
    exact ⟨h77, h78, h79, h81⟩
  · have h_sum : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := h_81 h_one
    have ⟨h77, h78, h79, h80⟩ :=
      (MulOperation.single_op_poly b_77 b_78 b_79 b_80 b_81 h_sum).2.2.1 h_one
    exact ⟨h77, h78, h79, h80⟩

@[simp] def sp1_op_a_poly (Main : Vector (ZMod p) 82) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val
@[simp] def sp1_op_b_poly (Main : Vector (ZMod p) 82) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val
@[simp] def sp1_op_c_poly (Main : Vector (ZMod p) 82) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val

set_option maxHeartbeats 4000000 in
-- Polymorphic mirror of `ops_U64_b_c` (line 176): both `b` and `c` operands
-- are 64-bit values. Uses `RTypeReader.allHold_constraints_iff_is_real_poly`
-- after extracting the ALU sub-constraints from `cstrs`. Takes the
-- specialized `is_real = 1` (sum of the 5 variant flags = 1) as input,
-- since deriving it requires the boolean disjunctions which the chip-level
-- `correct_*_poly` proofs extract once via `sum_eq_one_of_eq_one_*`.
lemma ops_U64_b_c_poly (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main))
    (h_is_real_eq_one :
      Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1) :
    Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64_poly #v[Main[22], Main[23], Main[24], Main[25]] := by
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨_h_mop, _h_cpu⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at h_alu
  obtain ⟨_, _, _, _, _, _, _, h_complex, _⟩ := h_alu
  obtain ⟨_, _, _, h_isU64_b, h_isU64_c⟩ := h_complex
  exact ⟨h_isU64_b, h_isU64_c⟩

/-- Derive `Main[77] + ... + Main[81] = 1` from cstrs + `Main[77] = 1`.
Used by chip-level `correct_mul_poly` so that downstream helpers
(`ops_U64_b_c_poly`, `register_bounds_poly`) can be invoked with raw
cstrs + this single derived fact. -/
lemma is_real_eq_one_of_mul (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main))
    (h_77 : Main[77] = 1) :
    Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := by
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨_, _b_77, b_78, b_79, b_81, b_80, sum_disj, _⟩ := cstrs
  exact sum_eq_one_of_eq_one_left h_77 b_78 b_79 b_80 b_81 sum_disj

lemma is_real_eq_one_of_mulh (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main))
    (h_78 : Main[78] = 1) :
    Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := by
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨_, b_77, _b_78, b_79, b_81, b_80, sum_disj, _⟩ := cstrs
  exact sum_eq_one_of_eq_one_2 h_78 b_77 b_79 b_80 b_81 sum_disj

lemma is_real_eq_one_of_mulhu (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main))
    (h_79 : Main[79] = 1) :
    Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := by
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨_, b_77, b_78, _b_79, b_81, b_80, sum_disj, _⟩ := cstrs
  exact sum_eq_one_of_eq_one_3 h_79 b_77 b_78 b_80 b_81 sum_disj

lemma is_real_eq_one_of_mulhsu (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main))
    (h_80 : Main[80] = 1) :
    Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := by
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨_, b_77, b_78, b_79, b_81, _b_80, sum_disj, _⟩ := cstrs
  exact sum_eq_one_of_eq_one_4 h_80 b_77 b_78 b_79 b_81 sum_disj

lemma is_real_eq_one_of_mulw (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main))
    (h_81 : Main[81] = 1) :
    Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := by
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨_, b_77, b_78, b_79, _b_81, b_80, sum_disj, _⟩ := cstrs
  exact sum_eq_one_of_eq_one_5 h_81 b_77 b_78 b_79 b_80 sum_disj

end poly_helpers

end Mul
