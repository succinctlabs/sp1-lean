import SP1Foundations
import SP1Operations.Reader.CPUState
import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.ITypeReaderImmutable

namespace Branch

section constraints

-- Generated Lean code for chip BranchChip
@[irreducible] def constraints (Main : Vector (Fin KB) 45) : SP1ConstraintList :=
  let E0 : Fin KB := Main[28] - 1
  let E1 : Fin KB := Main[28] * E0
  let E2 : Fin KB := Main[29] - 1
  let E3 : Fin KB := Main[29] * E2
  let E4 : Fin KB := Main[30] - 1
  let E5 : Fin KB := Main[30] * E4
  let E6 : Fin KB := Main[31] - 1
  let E7 : Fin KB := Main[31] * E6
  let E8 : Fin KB := Main[32] - 1
  let E9 : Fin KB := Main[32] * E8
  let E10 : Fin KB := Main[33] - 1
  let E11 : Fin KB := Main[33] * E10
  let E12 : Fin KB := Main[28] + Main[29]
  let E13 : Fin KB := E12 + Main[30]
  let E14 : Fin KB := E13 + Main[31]
  let E15 : Fin KB := E14 + Main[32]
  let E16 : Fin KB := E15 + Main[33]
  let E17 : Fin KB := E16 - 1
  let E18 : Fin KB := E16 * E17
  let E19 : Fin KB := Main[28] * 40
  let E20 : Fin KB := Main[29] * 41
  let E21 : Fin KB := E19 + E20
  let E22 : Fin KB := Main[30] * 42
  let E23 : Fin KB := E21 + E22
  let E24 : Fin KB := Main[31] * 43
  let E25 : Fin KB := E23 + E24
  let E26 : Fin KB := Main[32] * 44
  let E27 : Fin KB := E25 + E26
  let E28 : Fin KB := Main[33] * 45
  let E29 : Fin KB := E27 + E28
  let E30 : Fin KB := Main[28] * 0
  let E31 : Fin KB := Main[29] * 1
  let E32 : Fin KB := E30 + E31
  let E33 : Fin KB := Main[30] * 4
  let E34 : Fin KB := E32 + E33
  let E35 : Fin KB := Main[31] * 5
  let E36 : Fin KB := E34 + E35
  let E37 : Fin KB := Main[32] * 6
  let E38 : Fin KB := E36 + E37
  let E39 : Fin KB := Main[33] * 7
  let E40 : Fin KB := E38 + E39
  let E41 : Fin KB := Main[28] * 0
  let E42 : Fin KB := Main[29] * 0
  let E43 : Fin KB := E41 + E42
  let E44 : Fin KB := Main[30] * 0
  let E45 : Fin KB := E43 + E44
  let E46 : Fin KB := Main[31] * 0
  let E47 : Fin KB := E45 + E46
  let E48 : Fin KB := Main[32] * 0
  let E49 : Fin KB := E47 + E48
  let E50 : Fin KB := Main[33] * 0
  let E51 : Fin KB := E49 + E50
  let E52 : Fin KB := Main[28] * 99
  let E53 : Fin KB := Main[29] * 99
  let E54 : Fin KB := E52 + E53
  let E55 : Fin KB := Main[30] * 99
  let E56 : Fin KB := E54 + E55
  let E57 : Fin KB := Main[31] * 99
  let E58 : Fin KB := E56 + E57
  let E59 : Fin KB := Main[32] * 99
  let E60 : Fin KB := E58 + E59
  let E61 : Fin KB := Main[33] * 99
  let E62 : Fin KB := E60 + E61
  let E63 : Fin KB := Main[28] * 32
  let E64 : Fin KB := Main[29] * 32
  let E65 : Fin KB := E63 + E64
  let E66 : Fin KB := Main[30] * 32
  let E67 : Fin KB := E65 + E66
  let E68 : Fin KB := Main[31] * 32
  let E69 : Fin KB := E67 + E68
  let E70 : Fin KB := Main[32] * 32
  let E71 : Fin KB := E69 + E70
  let E72 : Fin KB := Main[33] * 32
  let E73 : Fin KB := E71 + E72
  let CS0 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[25], Main[26], Main[27]] 8 E16
  let E74 : Fin KB := Main[1] * 65536
  let E75 : Fin KB := Main[2] + E74
  let CS1 : SP1ConstraintList := ITypeReaderImmutable.constraints Main[0] E75 #v[Main[3], Main[4], Main[5]] E29 #v[E73, E62, E40, E51] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E16
  let E76 : Fin KB := Main[30] + Main[31]
  let CS2 : SP1ConstraintList := LtOperationSigned.constraints #v[Main[7], Main[8], Main[9], Main[10]] #v[Main[15], Main[16], Main[17], Main[18]] { result := { u16_compare_operation := { bit := Main[35] }, u16_flags := #v[Main[36], Main[37], Main[38], Main[39]], not_eq_inv := Main[40], comparison_limbs := #v[Main[41], Main[42]] }, b_msb := { msb := Main[43] }, c_msb := { msb := Main[44] } } E76 E16
  let E77 : Fin KB := Main[36] + Main[37]
  let E78 : Fin KB := E77 + Main[38]
  let E79 : Fin KB := E78 + Main[39]
  let E80 : Fin KB := 1 - E79
  let E81 : Fin KB := Main[28] * E80
  let E82 : Fin KB := 0 + E81
  let E83 : Fin KB := 1 - E80
  let E84 : Fin KB := Main[29] * E83
  let E85 : Fin KB := E82 + E84
  let E86 : Fin KB := Main[31] + Main[33]
  let E87 : Fin KB := 1 - Main[35]
  let E88 : Fin KB := E86 * E87
  let E89 : Fin KB := E85 + E88
  let E90 : Fin KB := Main[30] + Main[32]
  let E91 : Fin KB := E90 * Main[35]
  let E92 : Fin KB := E89 + E91
  let E93 : Fin KB := Main[34] - 1
  let E94 : Fin KB := Main[34] * E93
  let E95 : Fin KB := Main[34] - E92
  let E96 : Fin KB := E16 * E95
  let E97 : Fin KB := 0 + Main[3]
  let E98 : Fin KB := E97 + Main[21]
  let E99 : Fin KB := E98 - Main[25]
  let E100 : Fin KB := E99 * 2130673921
  let E101 : Fin KB := E100 - 1
  let E102 : Fin KB := E100 * E101
  let E103 : Fin KB := Main[34] * E102
  let E104 : Fin KB := E100 + Main[4]
  let E105 : Fin KB := E104 + Main[22]
  let E106 : Fin KB := E105 - Main[26]
  let E107 : Fin KB := E106 * 2130673921
  let E108 : Fin KB := E107 - 1
  let E109 : Fin KB := E107 * E108
  let E110 : Fin KB := Main[34] * E109
  let E111 : Fin KB := E107 + Main[5]
  let E112 : Fin KB := E111 + Main[23]
  let E113 : Fin KB := E112 - Main[27]
  let E114 : Fin KB := E113 * 2130673921
  let E115 : Fin KB := E114 - 1
  let E116 : Fin KB := E114 * E115
  let E117 : Fin KB := Main[34] * E116
  let E118 : Fin KB := E114 + 0
  let E119 : Fin KB := E118 + Main[24]
  let E120 : Fin KB := E119 - 0
  let E121 : Fin KB := E120 * 2130673921
  let E122 : Fin KB := E121 - 1
  let E123 : Fin KB := E121 * E122
  let E124 : Fin KB := Main[34] * E123
  let E125 : Fin KB := 0 + Main[3]
  let E126 : Fin KB := E125 + 4
  let E127 : Fin KB := E126 - Main[25]
  let E128 : Fin KB := E127 * 2130673921
  let E129 : Fin KB := E16 - Main[34]
  let E130 : Fin KB := E128 - 1
  let E131 : Fin KB := E128 * E130
  let E132 : Fin KB := E129 * E131
  let E133 : Fin KB := E128 + Main[4]
  let E134 : Fin KB := E133 + 0
  let E135 : Fin KB := E134 - Main[26]
  let E136 : Fin KB := E135 * 2130673921
  let E137 : Fin KB := E16 - Main[34]
  let E138 : Fin KB := E136 - 1
  let E139 : Fin KB := E136 * E138
  let E140 : Fin KB := E137 * E139
  let E141 : Fin KB := E136 + Main[5]
  let E142 : Fin KB := E141 + 0
  let E143 : Fin KB := E142 - Main[27]
  let E144 : Fin KB := E143 * 2130673921
  let E145 : Fin KB := E16 - Main[34]
  let E146 : Fin KB := E144 - 1
  let E147 : Fin KB := E144 * E146
  let E148 : Fin KB := E145 * E147
  let E149 : Fin KB := E144 + 0
  let E150 : Fin KB := E149 + 0
  let E151 : Fin KB := E150 - 0
  let E152 : Fin KB := E151 * 2130673921
  let E153 : Fin KB := E16 - Main[34]
  let E154 : Fin KB := E152 - 1
  let E155 : Fin KB := E152 * E154
  let E156 : Fin KB := E153 * E155
  let E157 : Fin KB := Main[25] * 1598029825
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E11),
    (.assertZero E18),
    (.assertZero E94),
    (.assertZero E96),
    (.assertZero E103),
    (.assertZero E110),
    (.assertZero E117),
    (.assertZero E124),
    (.assertZero E132),
    (.assertZero E140),
    (.assertZero E148),
    (.assertZero E156),
    (.send (.byte (ByteOpcode.ofNat 6) E157 14 0) E16),
    (.send (.byte (ByteOpcode.ofNat 6) Main[26] 16 0) E16),
    (.send (.byte (ByteOpcode.ofNat 6) Main[27] 16 0) E16),
  ]

end constraints

def is_real (Main : Vector (Fin KB) 45) :=
  Main[28] = 1 ∨ Main[29] = 1 ∨ Main[30] = 1 ∨ Main[31] = 1 ∨ Main[32] = 1 ∨ Main[33] = 1

lemma single_op (Main : Vector (Fin KB) 45) (cstrs : (constraints Main).allHold) :
    (Main[28] = 1 → Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[29] = 1 → Main[28] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[30] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[31] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[32] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[33] = 0) ∧
    (Main[33] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0) := by
  simp [constraints, sub_eq_zero] at cstrs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩ := cstrs
  clear h1 h2 h3
  cases h4 <;> cases h5 <;> cases h6 <;> cases h7 <;> cases h8 <;> cases h9
  all_goals simp_all only [Fin.isValue, add_zero, zero_add, one_ne_zero, or_true, zero_ne_one,
    and_self, implies_true, Fin.reduceAdd, Fin.reduceEq, or_self]

lemma eq_signExtend_of_is_real (Main : Vector (Fin KB) 45)
    (_ : (constraints Main).allHold)
    (_ : is_real Main) :
    Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 13 Main[21]) := by
  sorry

lemma add_signExtend_of_constraints (Main : Vector (Fin KB) 45)
    (_ : (constraints Main).allHold)
    (_ : is_real Main) :
    (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
      BitVec.signExtend 64 (BitVec.ofNat 13 Main[21])) % 4 = 0 := by
  sorry

end Branch
