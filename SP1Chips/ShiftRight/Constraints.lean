import SP1Operations

namespace ShiftRight

set_option maxHeartbeats 4000000

section constraints

-- Generated Lean code for chip ShiftRightChip
def constraints (Main : Vector (Fin BB) 69) : SP1ConstraintList :=
  let E0 : Fin BB := Main[64] + Main[65]
  let E1 : Fin BB := E0 + Main[66]
  let E2 : Fin BB := E1 + Main[67]
  let E3 : Fin BB := Main[64] - 1
  let E4 : Fin BB := Main[64] * E3
  let E5 : Fin BB := Main[65] - 1
  let E6 : Fin BB := Main[65] * E5
  let E7 : Fin BB := Main[66] - 1
  let E8 : Fin BB := Main[66] * E7
  let E9 : Fin BB := Main[67] - 1
  let E10 : Fin BB := Main[67] * E9
  let E11 : Fin BB := E2 - 1
  let E12 : Fin BB := E2 * E11
  let E13 : Fin BB := Main[66] + Main[67]
  let E14 : Fin BB := Main[64] + Main[65]
  let E15 : Fin BB := Main[64] * 7
  let E16 : Fin BB := Main[65] * 8
  let E17 : Fin BB := E15 + E16
  let E18 : Fin BB := Main[66] * 42
  let E19 : Fin BB := E17 + E18
  let E20 : Fin BB := Main[67] * 43
  let E21 : Fin BB := E19 + E20
  let E22 : Fin BB := Main[64] * 5
  let E23 : Fin BB := Main[65] * 5
  let E24 : Fin BB := E22 + E23
  let E25 : Fin BB := Main[66] * 5
  let E26 : Fin BB := E24 + E25
  let E27 : Fin BB := Main[67] * 5
  let E28 : Fin BB := E26 + E27
  let E29 : Fin BB := Main[64] * 0
  let E30 : Fin BB := Main[65] * 32
  let E31 : Fin BB := E29 + E30
  let E32 : Fin BB := Main[66] * 0
  let E33 : Fin BB := E31 + E32
  let E34 : Fin BB := Main[67] * 32
  let E35 : Fin BB := E33 + E34
  let E36 : Fin BB := Main[64] * 19
  let E37 : Fin BB := Main[65] * 19
  let E38 : Fin BB := E36 + E37
  let E39 : Fin BB := Main[66] * 27
  let E40 : Fin BB := E38 + E39
  let E41 : Fin BB := Main[67] * 27
  let E42 : Fin BB := E40 + E41
  let E43 : Fin BB := Main[64] * 51
  let E44 : Fin BB := Main[65] * 51
  let E45 : Fin BB := E43 + E44
  let E46 : Fin BB := Main[66] * 59
  let E47 : Fin BB := E45 + E46
  let E48 : Fin BB := Main[67] * 59
  let E49 : Fin BB := E47 + E48
  let E50 : Fin BB := Main[31] * E42
  let E51 : Fin BB := 1 - Main[31]
  let E52 : Fin BB := E51 * E49
  let E53 : Fin BB := E50 + E52
  let E54 : Fin BB := Main[68] - E53
  let E55 : Fin BB := E2 * E54
  let E56 : Fin BB := Main[64] * 19
  let E57 : Fin BB := Main[65] * 19
  let E58 : Fin BB := E56 + E57
  let E59 : Fin BB := Main[66] * 27
  let E60 : Fin BB := E58 + E59
  let E61 : Fin BB := Main[67] * 27
  let E62 : Fin BB := E60 + E61
  let E63 : Fin BB := Main[64] * 51
  let E64 : Fin BB := Main[65] * 51
  let E65 : Fin BB := E63 + E64
  let E66 : Fin BB := Main[66] * 59
  let E67 : Fin BB := E65 + E66
  let E68 : Fin BB := Main[67] * 59
  let E69 : Fin BB := E67 + E68
  let E70 : Fin BB := Main[31] * E62
  let E71 : Fin BB := 1 - Main[31]
  let E72 : Fin BB := E71 * E69
  let E73 : Fin BB := E70 + E72
  let E74 : Fin BB := Main[68] - E73
  let E75 : Fin BB := E2 * E74
  let E76 : Fin BB := Main[38] - 1
  let E77 : Fin BB := Main[38] * E76
  let E78 : Fin BB := Main[39] - 1
  let E79 : Fin BB := Main[39] * E78
  let E80 : Fin BB := Main[40] - 1
  let E81 : Fin BB := Main[40] * E80
  let E82 : Fin BB := Main[41] - 1
  let E83 : Fin BB := Main[41] * E82
  let E84 : Fin BB := Main[42] - 1
  let E85 : Fin BB := Main[42] * E84
  let E86 : Fin BB := Main[43] - 1
  let E87 : Fin BB := Main[43] * E86
  let E88 : Fin BB := Main[38] * 1
  let E89 : Fin BB := 0 + E88
  let E90 : Fin BB := Main[39] * 2
  let E91 : Fin BB := E89 + E90
  let E92 : Fin BB := Main[40] * 4
  let E93 : Fin BB := E91 + E92
  let E94 : Fin BB := Main[41] * 8
  let E95 : Fin BB := E93 + E94
  let E96 : Fin BB := Main[42] * 16
  let E97 : Fin BB := E95 + E96
  let E98 : Fin BB := Main[43] * 32
  let E99 : Fin BB := E97 + E98
  let E100 : Fin BB := Main[25] - E99
  let E101 : Fin BB := E100 * 1981808641
  let E102 : Fin BB := Main[43] * 2
  let E103 : Fin BB := E102 * E14
  let E104 : Fin BB := Main[42] + E103
  let E105 : Fin BB := E104 - 0
  let E106 : Fin BB := Main[60] * E105
  let E107 : Fin BB := Main[60] - 1
  let E108 : Fin BB := Main[60] * E107
  let E109 : Fin BB := Main[43] * 2
  let E110 : Fin BB := E109 * E14
  let E111 : Fin BB := Main[42] + E110
  let E112 : Fin BB := E111 - 1
  let E113 : Fin BB := Main[61] * E112
  let E114 : Fin BB := Main[61] - 1
  let E115 : Fin BB := Main[61] * E114
  let E116 : Fin BB := Main[43] * 2
  let E117 : Fin BB := E116 * E14
  let E118 : Fin BB := Main[42] + E117
  let E119 : Fin BB := E118 - 2
  let E120 : Fin BB := Main[62] * E119
  let E121 : Fin BB := Main[62] - 1
  let E122 : Fin BB := Main[62] * E121
  let E123 : Fin BB := Main[43] * 2
  let E124 : Fin BB := E123 * E14
  let E125 : Fin BB := Main[42] + E124
  let E126 : Fin BB := E125 - 3
  let E127 : Fin BB := Main[63] * E126
  let E128 : Fin BB := Main[63] - 1
  let E129 : Fin BB := Main[63] * E128
  let E130 : Fin BB := Main[60] + Main[61]
  let E131 : Fin BB := E130 + Main[62]
  let E132 : Fin BB := E131 + Main[63]
  let E133 : Fin BB := E132 - 1
  let E134 : Fin BB := E2 * E133
  let E135 : Fin BB := 1 - Main[38]
  let E136 : Fin BB := E135 + 1
  let E137 : Fin BB := E136 * 2
  let E138 : Fin BB := 1 - Main[39]
  let E139 : Fin BB := E138 * 3
  let E140 : Fin BB := E139 + 1
  let E141 : Fin BB := E137 * E140
  let E142 : Fin BB := Main[47] - E141
  let E143 : Fin BB := 1 - Main[40]
  let E144 : Fin BB := E143 * 15
  let E145 : Fin BB := E144 + 1
  let E146 : Fin BB := Main[47] * E145
  let E147 : Fin BB := Main[46] - E146
  let E148 : Fin BB := 1 - Main[41]
  let E149 : Fin BB := E148 * 255
  let E150 : Fin BB := E149 + 1
  let E151 : Fin BB := Main[46] * E150
  let E152 : Fin BB := Main[45] - E151
  let E153 : Fin BB := 16 - E95
  let E154 : Fin BB := Main[15] * Main[45]
  let E155 : Fin BB := Main[52] * 65536
  let E156 : Fin BB := Main[48] * Main[45]
  let E157 : Fin BB := E155 + E156
  let E158 : Fin BB := E154 - E157
  let E159 : Fin BB := 16 - E95
  let E160 : Fin BB := Main[16] * Main[45]
  let E161 : Fin BB := Main[53] * 65536
  let E162 : Fin BB := Main[49] * Main[45]
  let E163 : Fin BB := E161 + E162
  let E164 : Fin BB := E160 - E163
  let E165 : Fin BB := 16 - E95
  let E166 : Fin BB := Main[17] * Main[45]
  let E167 : Fin BB := E166 * E14
  let E168 : Fin BB := Main[54] * 65536
  let E169 : Fin BB := Main[50] * Main[45]
  let E170 : Fin BB := E168 + E169
  let E171 : Fin BB := E167 - E170
  let E172 : Fin BB := 16 - E95
  let E173 : Fin BB := Main[18] * Main[45]
  let E174 : Fin BB := E173 * E14
  let E175 : Fin BB := Main[55] * 65536
  let E176 : Fin BB := Main[51] * Main[45]
  let E177 : Fin BB := E175 + E176
  let E178 : Fin BB := E174 - E177
  let E179 : Fin BB := Main[49] * Main[45]
  let E180 : Fin BB := Main[52] + E179
  let E181 : Fin BB := Main[56] - E180
  let E182 : Fin BB := Main[50] * Main[45]
  let E183 : Fin BB := Main[53] + E182
  let E184 : Fin BB := Main[57] - E183
  let E185 : Fin BB := Main[51] * Main[45]
  let E186 : Fin BB := Main[54] + E185
  let E187 : Fin BB := Main[58] - E186
  let E188 : Fin BB := Main[59] - Main[55]
  let CS0 : SP1ConstraintList := U16MSBOperation.constraints Main[18] { msb := Main[36] } Main[65]
  let CS1 : SP1ConstraintList := U16MSBOperation.constraints Main[16] { msb := Main[36] } Main[67]
  let E189 : Fin BB := Main[64] + Main[66]
  let E190 : Fin BB := E189 * Main[36]
  let E191 : Fin BB := Main[36] * Main[45]
  let E192 : Fin BB := Main[44] - E191
  let CS2 : SP1ConstraintList := U16MSBOperation.constraints Main[33] { msb := Main[37] } E13
  let E193 : Fin BB := E13 - 1
  let E194 : Fin BB := E193 * Main[37]
  let E195 : Fin BB := Main[32] - Main[56]
  let E196 : Fin BB := Main[60] * E195
  let E197 : Fin BB := E14 * E196
  let E198 : Fin BB := Main[33] - Main[57]
  let E199 : Fin BB := Main[60] * E198
  let E200 : Fin BB := E14 * E199
  let E201 : Fin BB := Main[34] - Main[58]
  let E202 : Fin BB := Main[60] * E201
  let E203 : Fin BB := E14 * E202
  let E204 : Fin BB := Main[36] * 65536
  let E205 : Fin BB := E204 - Main[44]
  let E206 : Fin BB := Main[59] + E205
  let E207 : Fin BB := Main[35] - E206
  let E208 : Fin BB := Main[60] * E207
  let E209 : Fin BB := E14 * E208
  let E210 : Fin BB := Main[32] - Main[57]
  let E211 : Fin BB := Main[61] * E210
  let E212 : Fin BB := E14 * E211
  let E213 : Fin BB := Main[33] - Main[58]
  let E214 : Fin BB := Main[61] * E213
  let E215 : Fin BB := E14 * E214
  let E216 : Fin BB := Main[36] * 65536
  let E217 : Fin BB := E216 - Main[44]
  let E218 : Fin BB := Main[59] + E217
  let E219 : Fin BB := Main[34] - E218
  let E220 : Fin BB := Main[61] * E219
  let E221 : Fin BB := E14 * E220
  let E222 : Fin BB := Main[36] * 65535
  let E223 : Fin BB := Main[35] - E222
  let E224 : Fin BB := Main[61] * E223
  let E225 : Fin BB := E14 * E224
  let E226 : Fin BB := Main[32] - Main[58]
  let E227 : Fin BB := Main[62] * E226
  let E228 : Fin BB := E14 * E227
  let E229 : Fin BB := Main[36] * 65536
  let E230 : Fin BB := E229 - Main[44]
  let E231 : Fin BB := Main[59] + E230
  let E232 : Fin BB := Main[33] - E231
  let E233 : Fin BB := Main[62] * E232
  let E234 : Fin BB := E14 * E233
  let E235 : Fin BB := Main[36] * 65535
  let E236 : Fin BB := Main[34] - E235
  let E237 : Fin BB := Main[62] * E236
  let E238 : Fin BB := E14 * E237
  let E239 : Fin BB := Main[36] * 65535
  let E240 : Fin BB := Main[35] - E239
  let E241 : Fin BB := Main[62] * E240
  let E242 : Fin BB := E14 * E241
  let E243 : Fin BB := Main[36] * 65536
  let E244 : Fin BB := E243 - Main[44]
  let E245 : Fin BB := Main[59] + E244
  let E246 : Fin BB := Main[32] - E245
  let E247 : Fin BB := Main[63] * E246
  let E248 : Fin BB := E14 * E247
  let E249 : Fin BB := Main[36] * 65535
  let E250 : Fin BB := Main[33] - E249
  let E251 : Fin BB := Main[63] * E250
  let E252 : Fin BB := E14 * E251
  let E253 : Fin BB := Main[36] * 65535
  let E254 : Fin BB := Main[34] - E253
  let E255 : Fin BB := Main[63] * E254
  let E256 : Fin BB := E14 * E255
  let E257 : Fin BB := Main[36] * 65535
  let E258 : Fin BB := Main[35] - E257
  let E259 : Fin BB := Main[63] * E258
  let E260 : Fin BB := E14 * E259
  let E261 : Fin BB := Main[32] - Main[56]
  let E262 : Fin BB := Main[60] * E261
  let E263 : Fin BB := E13 * E262
  let E264 : Fin BB := Main[36] * 65536
  let E265 : Fin BB := E264 - Main[44]
  let E266 : Fin BB := Main[57] + E265
  let E267 : Fin BB := Main[33] - E266
  let E268 : Fin BB := Main[60] * E267
  let E269 : Fin BB := E13 * E268
  let E270 : Fin BB := Main[36] * 65536
  let E271 : Fin BB := E270 - Main[44]
  let E272 : Fin BB := Main[57] + E271
  let E273 : Fin BB := Main[32] - E272
  let E274 : Fin BB := Main[61] * E273
  let E275 : Fin BB := E13 * E274
  let E276 : Fin BB := Main[36] * 65535
  let E277 : Fin BB := Main[33] - E276
  let E278 : Fin BB := Main[61] * E277
  let E279 : Fin BB := E13 * E278
  let E280 : Fin BB := Main[37] * 65535
  let E281 : Fin BB := Main[34] - E280
  let E282 : Fin BB := E13 * E281
  let E283 : Fin BB := Main[37] * 65535
  let E284 : Fin BB := Main[35] - E283
  let E285 : Fin BB := E13 * E284
  let E286 : Fin BB := Main[3] + 4
  let CS3 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E286, Main[4], Main[5]] 8 E2
  let E287 : Fin BB := Main[1] * 65536
  let E288 : Fin BB := Main[2] + E287
  let CS4 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E288 #v[Main[3], Main[4], Main[5]] E21 #v[Main[68], E28, E35] #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E2
  CS0 ++ CS1 ++ CS2 ++ CS3 ++ CS4 ++ [
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.assertZero E12),
    (.assertZero E55),
    (.assertZero E75),
    (.assertZero E77),
    (.assertZero E79),
    (.assertZero E81),
    (.assertZero E83),
    (.assertZero E85),
    (.assertZero E87),
    (.send (.byte (ByteOpcode.ofNat 6) E101 10 0) E2),
    (.assertZero E106),
    (.assertZero E108),
    (.assertZero E113),
    (.assertZero E115),
    (.assertZero E120),
    (.assertZero E122),
    (.assertZero E127),
    (.assertZero E129),
    (.assertZero E134),
    (.assertZero E142),
    (.assertZero E147),
    (.assertZero E152),
    (.send (.byte (ByteOpcode.ofNat 6) Main[48] E95 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[52] E153 0) E2),
    (.assertZero E158),
    (.send (.byte (ByteOpcode.ofNat 6) Main[49] E95 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[53] E159 0) E2),
    (.assertZero E164),
    (.send (.byte (ByteOpcode.ofNat 6) Main[50] E95 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[54] E165 0) E2),
    (.assertZero E171),
    (.send (.byte (ByteOpcode.ofNat 6) Main[51] E95 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[55] E172 0) E2),
    (.assertZero E178),
    (.assertZero E181),
    (.assertZero E184),
    (.assertZero E187),
    (.assertZero E188),
    (.assertZero E190),
    (.assertZero E192),
    (.assertZero E194),
    (.assertZero E197),
    (.assertZero E200),
    (.assertZero E203),
    (.assertZero E209),
    (.assertZero E212),
    (.assertZero E215),
    (.assertZero E221),
    (.assertZero E225),
    (.assertZero E228),
    (.assertZero E234),
    (.assertZero E238),
    (.assertZero E242),
    (.assertZero E248),
    (.assertZero E252),
    (.assertZero E256),
    (.assertZero E260),
    (.assertZero E263),
    (.assertZero E269),
    (.assertZero E275),
    (.assertZero E279),
    (.assertZero E282),
    (.assertZero E285),
  ]

end constraints

end ShiftRight
