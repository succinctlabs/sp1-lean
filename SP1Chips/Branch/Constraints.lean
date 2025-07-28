import SP1Foundations
import SP1Operations.Reader.CPUState
import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.ITypeReaderImmutable

namespace Branch

section constraints

-- Generated Lean code for chip BranchChip
def constraints (Main : Vector (Fin BB) 45) : SP1ConstraintList :=
  let E0 : Fin BB := Main[28] - 1
  let E1 : Fin BB := Main[28] * E0
  let E2 : Fin BB := Main[29] - 1
  let E3 : Fin BB := Main[29] * E2
  let E4 : Fin BB := Main[30] - 1
  let E5 : Fin BB := Main[30] * E4
  let E6 : Fin BB := Main[31] - 1
  let E7 : Fin BB := Main[31] * E6
  let E8 : Fin BB := Main[32] - 1
  let E9 : Fin BB := Main[32] * E8
  let E10 : Fin BB := Main[33] - 1
  let E11 : Fin BB := Main[33] * E10
  let E12 : Fin BB := Main[28] + Main[29]
  let E13 : Fin BB := E12 + Main[30]
  let E14 : Fin BB := E13 + Main[31]
  let E15 : Fin BB := E14 + Main[32]
  let E16 : Fin BB := E15 + Main[33]
  let E17 : Fin BB := E16 - 1
  let E18 : Fin BB := E16 * E17
  let E19 : Fin BB := Main[28] * 27
  let E20 : Fin BB := Main[29] * 28
  let E21 : Fin BB := E19 + E20
  let E22 : Fin BB := Main[30] * 29
  let E23 : Fin BB := E21 + E22
  let E24 : Fin BB := Main[31] * 30
  let E25 : Fin BB := E23 + E24
  let E26 : Fin BB := Main[32] * 31
  let E27 : Fin BB := E25 + E26
  let E28 : Fin BB := Main[33] * 32
  let E29 : Fin BB := E27 + E28
  let E30 : Fin BB := Main[28] * 0
  let E31 : Fin BB := Main[29] * 1
  let E32 : Fin BB := E30 + E31
  let E33 : Fin BB := Main[30] * 4
  let E34 : Fin BB := E32 + E33
  let E35 : Fin BB := Main[31] * 5
  let E36 : Fin BB := E34 + E35
  let E37 : Fin BB := Main[32] * 6
  let E38 : Fin BB := E36 + E37
  let E39 : Fin BB := Main[33] * 7
  let E40 : Fin BB := E38 + E39
  let E41 : Fin BB := Main[28] * 0
  let E42 : Fin BB := Main[29] * 0
  let E43 : Fin BB := E41 + E42
  let E44 : Fin BB := Main[30] * 0
  let E45 : Fin BB := E43 + E44
  let E46 : Fin BB := Main[31] * 0
  let E47 : Fin BB := E45 + E46
  let E48 : Fin BB := Main[32] * 0
  let E49 : Fin BB := E47 + E48
  let E50 : Fin BB := Main[33] * 0
  let E51 : Fin BB := E49 + E50
  let E52 : Fin BB := Main[28] * 99
  let E53 : Fin BB := Main[29] * 99
  let E54 : Fin BB := E52 + E53
  let E55 : Fin BB := Main[30] * 99
  let E56 : Fin BB := E54 + E55
  let E57 : Fin BB := Main[31] * 99
  let E58 : Fin BB := E56 + E57
  let E59 : Fin BB := Main[32] * 99
  let E60 : Fin BB := E58 + E59
  let E61 : Fin BB := Main[33] * 99
  let E62 : Fin BB := E60 + E61
  let CS0 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[25], Main[26], Main[27]] 8 E16
  let E63 : Fin BB := Main[1] * 65536
  let E64 : Fin BB := Main[2] + E63
  let CS1 : SP1ConstraintList := ITypeReaderImmutable.constraints Main[0] E64 #v[Main[3], Main[4], Main[5]] E29 #v[E62, E40, E51] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E16
  let E65 : Fin BB := Main[30] + Main[31]
  let CS2 : SP1ConstraintList := LtOperationSigned.constraints #v[Main[7], Main[8], Main[9], Main[10]] #v[Main[15], Main[16], Main[17], Main[18]] { result := { u16_compare_operation := { bit := Main[35] }, u16_flags := #v[Main[36], Main[37], Main[38], Main[39]], not_eq_inv := Main[40], comparison_limbs := #v[Main[41], Main[42]] }, b_msb := { msb := Main[43] }, c_msb := { msb := Main[44] } } E65 E16
  let E66 : Fin BB := Main[36] + Main[37]
  let E67 : Fin BB := E66 + Main[38]
  let E68 : Fin BB := E67 + Main[39]
  let E69 : Fin BB := 1 - E68
  let E70 : Fin BB := Main[28] * E69
  let E71 : Fin BB := 0 + E70
  let E72 : Fin BB := 1 - E69
  let E73 : Fin BB := Main[29] * E72
  let E74 : Fin BB := E71 + E73
  let E75 : Fin BB := Main[31] + Main[33]
  let E76 : Fin BB := 1 - Main[35]
  let E77 : Fin BB := E75 * E76
  let E78 : Fin BB := E74 + E77
  let E79 : Fin BB := Main[30] + Main[32]
  let E80 : Fin BB := E79 * Main[35]
  let E81 : Fin BB := E78 + E80
  let E82 : Fin BB := Main[34] - 1
  let E83 : Fin BB := Main[34] * E82
  let E84 : Fin BB := Main[34] - E81
  let E85 : Fin BB := E16 * E84
  let E86 : Fin BB := 0 + Main[3]
  let E87 : Fin BB := E86 + Main[21]
  let E88 : Fin BB := E87 - Main[25]
  let E89 : Fin BB := E88 * 2013235201
  let E90 : Fin BB := E89 - 1
  let E91 : Fin BB := E89 * E90
  let E92 : Fin BB := Main[34] * E91
  let E93 : Fin BB := E89 + Main[4]
  let E94 : Fin BB := E93 + Main[22]
  let E95 : Fin BB := E94 - Main[26]
  let E96 : Fin BB := E95 * 2013235201
  let E97 : Fin BB := E96 - 1
  let E98 : Fin BB := E96 * E97
  let E99 : Fin BB := Main[34] * E98
  let E100 : Fin BB := E96 + Main[5]
  let E101 : Fin BB := E100 + Main[23]
  let E102 : Fin BB := E101 - Main[27]
  let E103 : Fin BB := E102 * 2013235201
  let E104 : Fin BB := E103 - 1
  let E105 : Fin BB := E103 * E104
  let E106 : Fin BB := Main[34] * E105
  let E107 : Fin BB := E103 + 0
  let E108 : Fin BB := E107 + Main[24]
  let E109 : Fin BB := E108 - 0
  let E110 : Fin BB := E109 * 2013235201
  let E111 : Fin BB := E110 - 1
  let E112 : Fin BB := E110 * E111
  let E113 : Fin BB := Main[34] * E112
  let E114 : Fin BB := 0 + Main[3]
  let E115 : Fin BB := E114 + 4
  let E116 : Fin BB := E115 - Main[25]
  let E117 : Fin BB := E116 * 2013235201
  let E118 : Fin BB := E16 - Main[34]
  let E119 : Fin BB := E117 - 1
  let E120 : Fin BB := E117 * E119
  let E121 : Fin BB := E118 * E120
  let E122 : Fin BB := E117 + Main[4]
  let E123 : Fin BB := E122 + 0
  let E124 : Fin BB := E123 - Main[26]
  let E125 : Fin BB := E124 * 2013235201
  let E126 : Fin BB := E16 - Main[34]
  let E127 : Fin BB := E125 - 1
  let E128 : Fin BB := E125 * E127
  let E129 : Fin BB := E126 * E128
  let E130 : Fin BB := E125 + Main[5]
  let E131 : Fin BB := E130 + 0
  let E132 : Fin BB := E131 - Main[27]
  let E133 : Fin BB := E132 * 2013235201
  let E134 : Fin BB := E16 - Main[34]
  let E135 : Fin BB := E133 - 1
  let E136 : Fin BB := E133 * E135
  let E137 : Fin BB := E134 * E136
  let E138 : Fin BB := E133 + 0
  let E139 : Fin BB := E138 + 0
  let E140 : Fin BB := E139 - 0
  let E141 : Fin BB := E140 * 2013235201
  let E142 : Fin BB := E16 - Main[34]
  let E143 : Fin BB := E141 - 1
  let E144 : Fin BB := E141 * E143
  let E145 : Fin BB := E142 * E144
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E11),
    (.assertZero E18),
    (.assertZero E83),
    (.assertZero E85),
    (.assertZero E92),
    (.assertZero E99),
    (.assertZero E106),
    (.assertZero E113),
    (.assertZero E121),
    (.assertZero E129),
    (.assertZero E137),
    (.assertZero E145),
    (.send (.byte (ByteOpcode.ofNat 6) Main[25] 16 0) E16),
    (.send (.byte (ByteOpcode.ofNat 6) Main[26] 16 0) E16),
    (.send (.byte (ByteOpcode.ofNat 6) Main[27] 16 0) E16),
  ]

end constraints

end Branch
