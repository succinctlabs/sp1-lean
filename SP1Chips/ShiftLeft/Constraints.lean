import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace ShiftLeft

section constraints

-- Generated Lean code for chip ShiftLeftChip
def constraints (Main : Vector (Fin BB) 65) : SP1ConstraintList :=
  let E0 : Fin BB := Main[62] + Main[63]
  let E1 : Fin BB := E0 - 1
  let E2 : Fin BB := E0 * E1
  let E3 : Fin BB := Main[62] - 1
  let E4 : Fin BB := Main[62] * E3
  let E5 : Fin BB := Main[63] - 1
  let E6 : Fin BB := Main[63] * E5
  let E7 : Fin BB := Main[36] - 1
  let E8 : Fin BB := Main[36] * E7
  let E9 : Fin BB := Main[37] - 1
  let E10 : Fin BB := Main[37] * E9
  let E11 : Fin BB := Main[38] - 1
  let E12 : Fin BB := Main[38] * E11
  let E13 : Fin BB := Main[39] - 1
  let E14 : Fin BB := Main[39] * E13
  let E15 : Fin BB := Main[40] - 1
  let E16 : Fin BB := Main[40] * E15
  let E17 : Fin BB := Main[41] - 1
  let E18 : Fin BB := Main[41] * E17
  let E19 : Fin BB := Main[36] * 1
  let E20 : Fin BB := 0 + E19
  let E21 : Fin BB := Main[37] * 2
  let E22 : Fin BB := E20 + E21
  let E23 : Fin BB := Main[38] * 4
  let E24 : Fin BB := E22 + E23
  let E25 : Fin BB := Main[39] * 8
  let E26 : Fin BB := E24 + E25
  let E27 : Fin BB := Main[40] * 16
  let E28 : Fin BB := E26 + E27
  let E29 : Fin BB := Main[41] * 32
  let E30 : Fin BB := E28 + E29
  let E31 : Fin BB := Main[25] - E30
  let E32 : Fin BB := E31 * 1981808641
  let E33 : Fin BB := Main[41] * 2
  let E34 : Fin BB := E33 * Main[62]
  let E35 : Fin BB := Main[40] + E34
  let E36 : Fin BB := E35 - 0
  let E37 : Fin BB := Main[45] * E36
  let E38 : Fin BB := Main[45] - 1
  let E39 : Fin BB := Main[45] * E38
  let E40 : Fin BB := Main[41] * 2
  let E41 : Fin BB := E40 * Main[62]
  let E42 : Fin BB := Main[40] + E41
  let E43 : Fin BB := E42 - 1
  let E44 : Fin BB := Main[46] * E43
  let E45 : Fin BB := Main[46] - 1
  let E46 : Fin BB := Main[46] * E45
  let E47 : Fin BB := Main[41] * 2
  let E48 : Fin BB := E47 * Main[62]
  let E49 : Fin BB := Main[40] + E48
  let E50 : Fin BB := E49 - 2
  let E51 : Fin BB := Main[47] * E50
  let E52 : Fin BB := Main[47] - 1
  let E53 : Fin BB := Main[47] * E52
  let E54 : Fin BB := Main[41] * 2
  let E55 : Fin BB := E54 * Main[62]
  let E56 : Fin BB := Main[40] + E55
  let E57 : Fin BB := E56 - 3
  let E58 : Fin BB := Main[48] * E57
  let E59 : Fin BB := Main[48] - 1
  let E60 : Fin BB := Main[48] * E59
  let E61 : Fin BB := Main[45] + Main[46]
  let E62 : Fin BB := E61 + Main[47]
  let E63 : Fin BB := E62 + Main[48]
  let E64 : Fin BB := E63 - 1
  let E65 : Fin BB := E0 * E64
  let E66 : Fin BB := Main[36] + 1
  let E67 : Fin BB := Main[37] * 3
  let E68 : Fin BB := E67 + 1
  let E69 : Fin BB := E66 * E68
  let E70 : Fin BB := Main[42] - E69
  let E71 : Fin BB := Main[38] * 15
  let E72 : Fin BB := E71 + 1
  let E73 : Fin BB := Main[42] * E72
  let E74 : Fin BB := Main[43] - E73
  let E75 : Fin BB := Main[39] * 255
  let E76 : Fin BB := E75 + 1
  let E77 : Fin BB := Main[43] * E76
  let E78 : Fin BB := Main[44] - E77
  let E79 : Fin BB := 16 - E26
  let E80 : Fin BB := Main[15] * Main[44]
  let E81 : Fin BB := Main[53] * 65536
  let E82 : Fin BB := Main[49] * Main[44]
  let E83 : Fin BB := E81 + E82
  let E84 : Fin BB := E80 - E83
  let E85 : Fin BB := 16 - E26
  let E86 : Fin BB := Main[16] * Main[44]
  let E87 : Fin BB := Main[54] * 65536
  let E88 : Fin BB := Main[50] * Main[44]
  let E89 : Fin BB := E87 + E88
  let E90 : Fin BB := E86 - E89
  let E91 : Fin BB := 16 - E26
  let E92 : Fin BB := Main[17] * Main[44]
  let E93 : Fin BB := Main[55] * 65536
  let E94 : Fin BB := Main[51] * Main[44]
  let E95 : Fin BB := E93 + E94
  let E96 : Fin BB := E92 - E95
  let E97 : Fin BB := 16 - E26
  let E98 : Fin BB := Main[18] * Main[44]
  let E99 : Fin BB := Main[56] * 65536
  let E100 : Fin BB := Main[52] * Main[44]
  let E101 : Fin BB := E99 + E100
  let E102 : Fin BB := E98 - E101
  let E103 : Fin BB := Main[49] * Main[44]
  let E104 : Fin BB := Main[57] - E103
  let E105 : Fin BB := Main[50] * Main[44]
  let E106 : Fin BB := E105 + Main[53]
  let E107 : Fin BB := Main[58] - E106
  let E108 : Fin BB := Main[51] * Main[44]
  let E109 : Fin BB := E108 + Main[54]
  let E110 : Fin BB := Main[59] - E109
  let E111 : Fin BB := Main[52] * Main[44]
  let E112 : Fin BB := E111 + Main[55]
  let E113 : Fin BB := Main[60] - E112
  let E114 : Fin BB := Main[32] - Main[57]
  let E115 : Fin BB := Main[45] * E114
  let E116 : Fin BB := Main[62] * E115
  let E117 : Fin BB := Main[33] - Main[58]
  let E118 : Fin BB := Main[45] * E117
  let E119 : Fin BB := Main[62] * E118
  let E120 : Fin BB := Main[34] - Main[59]
  let E121 : Fin BB := Main[45] * E120
  let E122 : Fin BB := Main[62] * E121
  let E123 : Fin BB := Main[35] - Main[60]
  let E124 : Fin BB := Main[45] * E123
  let E125 : Fin BB := Main[62] * E124
  let E126 : Fin BB := Main[46] * Main[32]
  let E127 : Fin BB := Main[62] * E126
  let E128 : Fin BB := Main[33] - Main[57]
  let E129 : Fin BB := Main[46] * E128
  let E130 : Fin BB := Main[62] * E129
  let E131 : Fin BB := Main[34] - Main[58]
  let E132 : Fin BB := Main[46] * E131
  let E133 : Fin BB := Main[62] * E132
  let E134 : Fin BB := Main[35] - Main[59]
  let E135 : Fin BB := Main[46] * E134
  let E136 : Fin BB := Main[62] * E135
  let E137 : Fin BB := Main[47] * Main[32]
  let E138 : Fin BB := Main[62] * E137
  let E139 : Fin BB := Main[47] * Main[33]
  let E140 : Fin BB := Main[62] * E139
  let E141 : Fin BB := Main[34] - Main[57]
  let E142 : Fin BB := Main[47] * E141
  let E143 : Fin BB := Main[62] * E142
  let E144 : Fin BB := Main[35] - Main[58]
  let E145 : Fin BB := Main[47] * E144
  let E146 : Fin BB := Main[62] * E145
  let E147 : Fin BB := Main[48] * Main[32]
  let E148 : Fin BB := Main[62] * E147
  let E149 : Fin BB := Main[48] * Main[33]
  let E150 : Fin BB := Main[62] * E149
  let E151 : Fin BB := Main[48] * Main[34]
  let E152 : Fin BB := Main[62] * E151
  let E153 : Fin BB := Main[35] - Main[57]
  let E154 : Fin BB := Main[48] * E153
  let E155 : Fin BB := Main[62] * E154
  let E156 : Fin BB := Main[32] - Main[57]
  let E157 : Fin BB := Main[45] * E156
  let E158 : Fin BB := Main[63] * E157
  let E159 : Fin BB := Main[33] - Main[58]
  let E160 : Fin BB := Main[45] * E159
  let E161 : Fin BB := Main[63] * E160
  let E162 : Fin BB := Main[46] * Main[32]
  let E163 : Fin BB := Main[63] * E162
  let E164 : Fin BB := Main[33] - Main[57]
  let E165 : Fin BB := Main[46] * E164
  let E166 : Fin BB := Main[63] * E165
  let E167 : Fin BB := Main[61] * 65535
  let E168 : Fin BB := E167 - Main[34]
  let E169 : Fin BB := Main[63] * E168
  let E170 : Fin BB := Main[61] * 65535
  let E171 : Fin BB := E170 - Main[35]
  let E172 : Fin BB := Main[63] * E171
  let CS0 : SP1ConstraintList := U16MSBOperation.constraints Main[33] { msb := Main[61] } Main[63]
  let E173 : Fin BB := Main[62] * 6
  let E174 : Fin BB := Main[63] * 41
  let E175 : Fin BB := E173 + E174
  let E176 : Fin BB := Main[62] * 1
  let E177 : Fin BB := Main[63] * 1
  let E178 : Fin BB := E176 + E177
  let E179 : Fin BB := Main[62] * 0
  let E180 : Fin BB := Main[63] * 0
  let E181 : Fin BB := E179 + E180
  let E182 : Fin BB := Main[62] * 19
  let E183 : Fin BB := Main[63] * 27
  let E184 : Fin BB := E182 + E183
  let E185 : Fin BB := Main[62] * 51
  let E186 : Fin BB := Main[63] * 59
  let E187 : Fin BB := E185 + E186
  let E188 : Fin BB := Main[31] * E184
  let E189 : Fin BB := 1 - Main[31]
  let E190 : Fin BB := E189 * E187
  let E191 : Fin BB := E188 + E190
  let E192 : Fin BB := Main[64] - E191
  let E193 : Fin BB := E0 * E192
  let E194 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E194, Main[4], Main[5]] 8 E0
  let E195 : Fin BB := Main[1] * 65536
  let E196 : Fin BB := Main[2] + E195
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E196 #v[Main[3], Main[4], Main[5]] E175 #v[Main[64], E178, E181] #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E0
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E2),
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.assertZero E12),
    (.assertZero E14),
    (.assertZero E16),
    (.assertZero E18),
    (.send (.byte (ByteOpcode.ofNat 6) E32 10 0) E0),
    (.assertZero E37),
    (.assertZero E39),
    (.assertZero E44),
    (.assertZero E46),
    (.assertZero E51),
    (.assertZero E53),
    (.assertZero E58),
    (.assertZero E60),
    (.assertZero E65),
    (.assertZero E70),
    (.assertZero E74),
    (.assertZero E78),
    (.send (.byte (ByteOpcode.ofNat 6) Main[49] E79 0) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[53] E26 0) E0),
    (.assertZero E84),
    (.send (.byte (ByteOpcode.ofNat 6) Main[50] E85 0) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[54] E26 0) E0),
    (.assertZero E90),
    (.send (.byte (ByteOpcode.ofNat 6) Main[51] E91 0) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[55] E26 0) E0),
    (.assertZero E96),
    (.send (.byte (ByteOpcode.ofNat 6) Main[52] E97 0) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[56] E26 0) E0),
    (.assertZero E102),
    (.assertZero E104),
    (.assertZero E107),
    (.assertZero E110),
    (.assertZero E113),
    (.assertZero E116),
    (.assertZero E119),
    (.assertZero E122),
    (.assertZero E125),
    (.assertZero E127),
    (.assertZero E130),
    (.assertZero E133),
    (.assertZero E136),
    (.assertZero E138),
    (.assertZero E140),
    (.assertZero E143),
    (.assertZero E146),
    (.assertZero E148),
    (.assertZero E150),
    (.assertZero E152),
    (.assertZero E155),
    (.assertZero E158),
    (.assertZero E161),
    (.assertZero E163),
    (.assertZero E166),
    (.assertZero E169),
    (.assertZero E172),
    (.assertZero E193),
  ]

end constraints

end ShiftLeft
