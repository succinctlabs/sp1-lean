import SP1Foundations
import SP1Operations.Reader.CPUState
import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.ITypeReaderImmutable

namespace Branch

section constraints

-- Generated Lean code for chip BranchChip
@[irreducible] def constraints (Main : Vector (Fin BB) 46) : SP1ConstraintList :=
  let E0 : Fin BB := Main[29] - 1
  let E1 : Fin BB := Main[29] * E0
  let E2 : Fin BB := Main[30] - 1
  let E3 : Fin BB := Main[30] * E2
  let E4 : Fin BB := Main[31] - 1
  let E5 : Fin BB := Main[31] * E4
  let E6 : Fin BB := Main[32] - 1
  let E7 : Fin BB := Main[32] * E6
  let E8 : Fin BB := Main[33] - 1
  let E9 : Fin BB := Main[33] * E8
  let E10 : Fin BB := Main[34] - 1
  let E11 : Fin BB := Main[34] * E10
  let E12 : Fin BB := Main[29] + Main[30]
  let E13 : Fin BB := E12 + Main[31]
  let E14 : Fin BB := E13 + Main[32]
  let E15 : Fin BB := E14 + Main[33]
  let E16 : Fin BB := E15 + Main[34]
  let E17 : Fin BB := E16 - 1
  let E18 : Fin BB := E16 * E17
  let E19 : Fin BB := Main[29] * 27
  let E20 : Fin BB := Main[30] * 28
  let E21 : Fin BB := E19 + E20
  let E22 : Fin BB := Main[31] * 29
  let E23 : Fin BB := E21 + E22
  let E24 : Fin BB := Main[32] * 30
  let E25 : Fin BB := E23 + E24
  let E26 : Fin BB := Main[33] * 31
  let E27 : Fin BB := E25 + E26
  let E28 : Fin BB := Main[34] * 32
  let E29 : Fin BB := E27 + E28
  let E30 : Fin BB := Main[29] * 0
  let E31 : Fin BB := Main[30] * 1
  let E32 : Fin BB := E30 + E31
  let E33 : Fin BB := Main[31] * 4
  let E34 : Fin BB := E32 + E33
  let E35 : Fin BB := Main[32] * 5
  let E36 : Fin BB := E34 + E35
  let E37 : Fin BB := Main[33] * 6
  let E38 : Fin BB := E36 + E37
  let E39 : Fin BB := Main[34] * 7
  let E40 : Fin BB := E38 + E39
  let E41 : Fin BB := Main[29] * 0
  let E42 : Fin BB := Main[30] * 0
  let E43 : Fin BB := E41 + E42
  let E44 : Fin BB := Main[31] * 0
  let E45 : Fin BB := E43 + E44
  let E46 : Fin BB := Main[32] * 0
  let E47 : Fin BB := E45 + E46
  let E48 : Fin BB := Main[33] * 0
  let E49 : Fin BB := E47 + E48
  let E50 : Fin BB := Main[34] * 0
  let E51 : Fin BB := E49 + E50
  let E52 : Fin BB := Main[29] * 99
  let E53 : Fin BB := Main[30] * 99
  let E54 : Fin BB := E52 + E53
  let E55 : Fin BB := Main[31] * 99
  let E56 : Fin BB := E54 + E55
  let E57 : Fin BB := Main[32] * 99
  let E58 : Fin BB := E56 + E57
  let E59 : Fin BB := Main[33] * 99
  let E60 : Fin BB := E58 + E59
  let E61 : Fin BB := Main[34] * 99
  let E62 : Fin BB := E60 + E61
  let E63 : Fin BB := Main[29] * 32
  let E64 : Fin BB := Main[30] * 32
  let E65 : Fin BB := E63 + E64
  let E66 : Fin BB := Main[31] * 32
  let E67 : Fin BB := E65 + E66
  let E68 : Fin BB := Main[32] * 32
  let E69 : Fin BB := E67 + E68
  let E70 : Fin BB := Main[33] * 32
  let E71 : Fin BB := E69 + E70
  let E72 : Fin BB := Main[34] * 32
  let E73 : Fin BB := E71 + E72
  let CS0 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[26], Main[27], Main[28]] 8 E16
  let E74 : Fin BB := Main[1] * 65536
  let E75 : Fin BB := Main[2] + E74
  let CS1 : SP1ConstraintList := ITypeReaderImmutable.constraints Main[0] E75 #v[Main[3], Main[4], Main[5]] E29 #v[E73, E62, E40, E51] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } E16
  let E76 : Fin BB := Main[31] + Main[32]
  let CS2 : SP1ConstraintList := LtOperationSigned.constraints #v[Main[7], Main[8], Main[9], Main[10]] #v[Main[15], Main[16], Main[17], Main[18]] { result := { u16_compare_operation := { bit := Main[36] }, u16_flags := #v[Main[37], Main[38], Main[39], Main[40]], not_eq_inv := Main[41], comparison_limbs := #v[Main[42], Main[43]] }, b_msb := { msb := Main[44] }, c_msb := { msb := Main[45] } } E76 E16
  let E77 : Fin BB := Main[37] + Main[38]
  let E78 : Fin BB := E77 + Main[39]
  let E79 : Fin BB := E78 + Main[40]
  let E80 : Fin BB := 1 - E79
  let E81 : Fin BB := Main[29] * E80
  let E82 : Fin BB := 0 + E81
  let E83 : Fin BB := 1 - E80
  let E84 : Fin BB := Main[30] * E83
  let E85 : Fin BB := E82 + E84
  let E86 : Fin BB := Main[32] + Main[34]
  let E87 : Fin BB := 1 - Main[36]
  let E88 : Fin BB := E86 * E87
  let E89 : Fin BB := E85 + E88
  let E90 : Fin BB := Main[31] + Main[33]
  let E91 : Fin BB := E90 * Main[36]
  let E92 : Fin BB := E89 + E91
  let E93 : Fin BB := Main[35] - 1
  let E94 : Fin BB := Main[35] * E93
  let E95 : Fin BB := Main[35] - E92
  let E96 : Fin BB := E16 * E95
  let E97 : Fin BB := 0 + Main[3]
  let E98 : Fin BB := E97 + Main[21]
  let E99 : Fin BB := E98 - Main[26]
  let E100 : Fin BB := E99 * 2130673921
  let E101 : Fin BB := E100 - 1
  let E102 : Fin BB := E100 * E101
  let E103 : Fin BB := Main[35] * E102
  let E104 : Fin BB := E100 + Main[4]
  let E105 : Fin BB := E104 + Main[22]
  let E106 : Fin BB := E105 - Main[27]
  let E107 : Fin BB := E106 * 2130673921
  let E108 : Fin BB := E107 - 1
  let E109 : Fin BB := E107 * E108
  let E110 : Fin BB := Main[35] * E109
  let E111 : Fin BB := E107 + Main[5]
  let E112 : Fin BB := E111 + Main[23]
  let E113 : Fin BB := E112 - Main[28]
  let E114 : Fin BB := E113 * 2130673921
  let E115 : Fin BB := E114 - 1
  let E116 : Fin BB := E114 * E115
  let E117 : Fin BB := Main[35] * E116
  let E118 : Fin BB := E114 + 0
  let E119 : Fin BB := E118 + Main[24]
  let E120 : Fin BB := E119 - 0
  let E121 : Fin BB := E120 * 2130673921
  let E122 : Fin BB := E121 - 1
  let E123 : Fin BB := E121 * E122
  let E124 : Fin BB := Main[35] * E123
  let E125 : Fin BB := 0 + Main[3]
  let E126 : Fin BB := E125 + 4
  let E127 : Fin BB := E126 - Main[26]
  let E128 : Fin BB := E127 * 2130673921
  let E129 : Fin BB := E16 - Main[35]
  let E130 : Fin BB := E128 - 1
  let E131 : Fin BB := E128 * E130
  let E132 : Fin BB := E129 * E131
  let E133 : Fin BB := E128 + Main[4]
  let E134 : Fin BB := E133 + 0
  let E135 : Fin BB := E134 - Main[27]
  let E136 : Fin BB := E135 * 2130673921
  let E137 : Fin BB := E16 - Main[35]
  let E138 : Fin BB := E136 - 1
  let E139 : Fin BB := E136 * E138
  let E140 : Fin BB := E137 * E139
  let E141 : Fin BB := E136 + Main[5]
  let E142 : Fin BB := E141 + 0
  let E143 : Fin BB := E142 - Main[28]
  let E144 : Fin BB := E143 * 2130673921
  let E145 : Fin BB := E16 - Main[35]
  let E146 : Fin BB := E144 - 1
  let E147 : Fin BB := E144 * E146
  let E148 : Fin BB := E145 * E147
  let E149 : Fin BB := E144 + 0
  let E150 : Fin BB := E149 + 0
  let E151 : Fin BB := E150 - 0
  let E152 : Fin BB := E151 * 2130673921
  let E153 : Fin BB := E16 - Main[35]
  let E154 : Fin BB := E152 - 1
  let E155 : Fin BB := E152 * E154
  let E156 : Fin BB := E153 * E155
  let E157 : Fin BB := Main[26] * 1598029825
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
    (.send (.byte (ByteOpcode.ofNat 6) Main[27] 16 0) E16),
    (.send (.byte (ByteOpcode.ofNat 6) Main[28] 16 0) E16),
  ]

end constraints

end Branch
