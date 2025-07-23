import SP1Foundations
import SP1Operations

-- Generated Lean code for chip ShiftLeftChip
namespace ShiftLeftChip

set_option maxHeartbeats 1000000 in
def constraints (Main : Vector (Fin BB) 70) : SP1ConstraintList :=
  let E0 : Fin BB := Main[68] + Main[69]
  let E1 : Fin BB := E0 - 1
  let E2 : Fin BB := E0 * E1
  let E3 : Fin BB := Main[68] - 1
  let E4 : Fin BB := Main[68] * E3
  let E5 : Fin BB := Main[69] - 1
  let E6 : Fin BB := Main[69] * E5
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
  let E19 : Fin BB := Main[42] - 1
  let E20 : Fin BB := Main[42] * E19
  let E21 : Fin BB := Main[43] - 1
  let E22 : Fin BB := Main[43] * E21
  let E23 : Fin BB := Main[36] * 1
  let E24 : Fin BB := 0 + E23
  let E25 : Fin BB := Main[37] * 2
  let E26 : Fin BB := E24 + E25
  let E27 : Fin BB := Main[38] * 4
  let E28 : Fin BB := E26 + E27
  let E29 : Fin BB := Main[39] * 8
  let E30 : Fin BB := E28 + E29
  let E31 : Fin BB := Main[40] * 16
  let E32 : Fin BB := E30 + E31
  let E33 : Fin BB := Main[41] * 32
  let E34 : Fin BB := E32 + E33
  let E35 : Fin BB := Main[42] * 64
  let E36 : Fin BB := E34 + E35
  let E37 : Fin BB := Main[43] * 128
  let E38 : Fin BB := E36 + E37
  let E39 : Fin BB := Main[25] - E38
  let E40 : Fin BB := E39 * 2005401601
  let ⟨⟨⟨[E41, E42, E43, E44, E45, E46, E47, E48]⟩, _⟩, CS0⟩ := U16toU8OperationUnsafe.constraints #v[Main[15], Main[16], Main[17], Main[18]] { low_bytes := #v[Main[51], Main[52], Main[53], Main[54]] }
  let E49 : Fin BB := 8 - Main[36]
  let E50 : Fin BB := Main[37] * 2
  let E51 : Fin BB := E49 - E50
  let E52 : Fin BB := Main[38] * 4
  let E53 : Fin BB := E51 - E52
  let E54 : Fin BB := Main[41] * 2
  let E55 : Fin BB := E54 * Main[68]
  let E56 : Fin BB := Main[40] + E55
  let E57 : Fin BB := E56 - 0
  let E58 : Fin BB := Main[47] * E57
  let E59 : Fin BB := Main[47] - 1
  let E60 : Fin BB := Main[47] * E59
  let E61 : Fin BB := Main[41] * 2
  let E62 : Fin BB := E61 * Main[68]
  let E63 : Fin BB := Main[40] + E62
  let E64 : Fin BB := E63 - 1
  let E65 : Fin BB := Main[48] * E64
  let E66 : Fin BB := Main[48] - 1
  let E67 : Fin BB := Main[48] * E66
  let E68 : Fin BB := Main[41] * 2
  let E69 : Fin BB := E68 * Main[68]
  let E70 : Fin BB := Main[40] + E69
  let E71 : Fin BB := E70 - 2
  let E72 : Fin BB := Main[49] * E71
  let E73 : Fin BB := Main[49] - 1
  let E74 : Fin BB := Main[49] * E73
  let E75 : Fin BB := Main[41] * 2
  let E76 : Fin BB := E75 * Main[68]
  let E77 : Fin BB := Main[40] + E76
  let E78 : Fin BB := E77 - 3
  let E79 : Fin BB := Main[50] * E78
  let E80 : Fin BB := Main[50] - 1
  let E81 : Fin BB := Main[50] * E80
  let E82 : Fin BB := Main[47] + Main[48]
  let E83 : Fin BB := E82 + Main[49]
  let E84 : Fin BB := E83 + Main[50]
  let E85 : Fin BB := E84 - 1
  let E86 : Fin BB := E0 * E85
  let E87 : Fin BB := Main[45] - Main[46]
  let E88 : Fin BB := Main[36] + 1
  let E89 : Fin BB := Main[37] * 3
  let E90 : Fin BB := E89 + 1
  let E91 : Fin BB := E88 * E90
  let E92 : Fin BB := Main[44] - E91
  let E93 : Fin BB := Main[38] * 15
  let E94 : Fin BB := E93 + 1
  let E95 : Fin BB := Main[44] * E94
  let E96 : Fin BB := Main[45] - E95
  let E97 : Fin BB := Main[45] * Main[39]
  let E98 : Fin BB := Main[46] - E97
  let E99 : Fin BB := 256 * Main[55]
  let E100 : Fin BB := 0 - E99
  let E101 : Fin BB := 256 * Main[56]
  let E102 : Fin BB := 0 - E101
  let E103 : Fin BB := E102 + Main[55]
  let E104 : Fin BB := 256 * Main[57]
  let E105 : Fin BB := 0 - E104
  let E106 : Fin BB := E105 + Main[56]
  let E107 : Fin BB := 256 * Main[58]
  let E108 : Fin BB := 0 - E107
  let E109 : Fin BB := E108 + Main[57]
  let E110 : Fin BB := 256 * Main[59]
  let E111 : Fin BB := 0 - E110
  let E112 : Fin BB := E111 + Main[58]
  let E113 : Fin BB := 256 * Main[60]
  let E114 : Fin BB := 0 - E113
  let E115 : Fin BB := E114 + Main[59]
  let E116 : Fin BB := 256 * Main[61]
  let E117 : Fin BB := 0 - E116
  let E118 : Fin BB := E117 + Main[60]
  let E119 : Fin BB := 256 * Main[62]
  let E120 : Fin BB := 0 - E119
  let E121 : Fin BB := E120 + Main[61]
  let E122 : Fin BB := 256 * E41
  let E123 : Fin BB := 0 + E122
  let E124 : Fin BB := 256 * E42
  let E125 : Fin BB := E41 + E124
  let E126 : Fin BB := 0 + E42
  let E127 : Fin BB := 256 * E43
  let E128 : Fin BB := E126 + E127
  let E129 : Fin BB := 256 * E44
  let E130 : Fin BB := E43 + E129
  let E131 : Fin BB := 0 + E44
  let E132 : Fin BB := 256 * E45
  let E133 : Fin BB := E131 + E132
  let E134 : Fin BB := 256 * E46
  let E135 : Fin BB := E45 + E134
  let E136 : Fin BB := 0 + E46
  let E137 : Fin BB := 256 * E47
  let E138 : Fin BB := E136 + E137
  let E139 : Fin BB := 256 * E48
  let E140 : Fin BB := E47 + E139
  let E141 : Fin BB := E123 * Main[46]
  let E142 : Fin BB := E125 * E87
  let E143 : Fin BB := E141 + E142
  let E144 : Fin BB := 256 * E100
  let E145 : Fin BB := E144 * Main[39]
  let E146 : Fin BB := E143 + E145
  let E147 : Fin BB := 1 - Main[39]
  let E148 : Fin BB := E100 * E147
  let E149 : Fin BB := E146 + E148
  let E150 : Fin BB := 256 * E103
  let E151 : Fin BB := 1 - Main[39]
  let E152 : Fin BB := E150 * E151
  let E153 : Fin BB := E149 + E152
  let E154 : Fin BB := Main[63] - E153
  let E155 : Fin BB := E128 * Main[46]
  let E156 : Fin BB := E130 * E87
  let E157 : Fin BB := E155 + E156
  let E158 : Fin BB := E103 * Main[39]
  let E159 : Fin BB := E157 + E158
  let E160 : Fin BB := 256 * E106
  let E161 : Fin BB := E160 * Main[39]
  let E162 : Fin BB := E159 + E161
  let E163 : Fin BB := 1 - Main[39]
  let E164 : Fin BB := E106 * E163
  let E165 : Fin BB := E162 + E164
  let E166 : Fin BB := 256 * E109
  let E167 : Fin BB := 1 - Main[39]
  let E168 : Fin BB := E166 * E167
  let E169 : Fin BB := E165 + E168
  let E170 : Fin BB := Main[64] - E169
  let E171 : Fin BB := E133 * Main[46]
  let E172 : Fin BB := E135 * E87
  let E173 : Fin BB := E171 + E172
  let E174 : Fin BB := E109 * Main[39]
  let E175 : Fin BB := E173 + E174
  let E176 : Fin BB := 256 * E112
  let E177 : Fin BB := E176 * Main[39]
  let E178 : Fin BB := E175 + E177
  let E179 : Fin BB := 1 - Main[39]
  let E180 : Fin BB := E112 * E179
  let E181 : Fin BB := E178 + E180
  let E182 : Fin BB := 256 * E115
  let E183 : Fin BB := 1 - Main[39]
  let E184 : Fin BB := E182 * E183
  let E185 : Fin BB := E181 + E184
  let E186 : Fin BB := Main[65] - E185
  let E187 : Fin BB := E138 * Main[46]
  let E188 : Fin BB := E140 * E87
  let E189 : Fin BB := E187 + E188
  let E190 : Fin BB := E115 * Main[39]
  let E191 : Fin BB := E189 + E190
  let E192 : Fin BB := 256 * E118
  let E193 : Fin BB := E192 * Main[39]
  let E194 : Fin BB := E191 + E193
  let E195 : Fin BB := 1 - Main[39]
  let E196 : Fin BB := E118 * E195
  let E197 : Fin BB := E194 + E196
  let E198 : Fin BB := 256 * E121
  let E199 : Fin BB := 1 - Main[39]
  let E200 : Fin BB := E198 * E199
  let E201 : Fin BB := E197 + E200
  let E202 : Fin BB := Main[66] - E201
  let E203 : Fin BB := Main[32] - Main[63]
  let E204 : Fin BB := Main[47] * E203
  let E205 : Fin BB := E204 - 0
  let E206 : Fin BB := Main[68] * E205
  let E207 : Fin BB := Main[33] - Main[64]
  let E208 : Fin BB := Main[47] * E207
  let E209 : Fin BB := E208 - 0
  let E210 : Fin BB := Main[68] * E209
  let E211 : Fin BB := Main[34] - Main[65]
  let E212 : Fin BB := Main[47] * E211
  let E213 : Fin BB := E212 - 0
  let E214 : Fin BB := Main[68] * E213
  let E215 : Fin BB := Main[35] - Main[66]
  let E216 : Fin BB := Main[47] * E215
  let E217 : Fin BB := E216 - 0
  let E218 : Fin BB := Main[68] * E217
  let E219 : Fin BB := Main[48] * Main[32]
  let E220 : Fin BB := E219 - 0
  let E221 : Fin BB := Main[68] * E220
  let E222 : Fin BB := Main[33] - Main[63]
  let E223 : Fin BB := Main[48] * E222
  let E224 : Fin BB := E223 - 0
  let E225 : Fin BB := Main[68] * E224
  let E226 : Fin BB := Main[34] - Main[64]
  let E227 : Fin BB := Main[48] * E226
  let E228 : Fin BB := E227 - 0
  let E229 : Fin BB := Main[68] * E228
  let E230 : Fin BB := Main[35] - Main[65]
  let E231 : Fin BB := Main[48] * E230
  let E232 : Fin BB := E231 - 0
  let E233 : Fin BB := Main[68] * E232
  let E234 : Fin BB := Main[49] * Main[32]
  let E235 : Fin BB := E234 - 0
  let E236 : Fin BB := Main[68] * E235
  let E237 : Fin BB := Main[49] * Main[33]
  let E238 : Fin BB := E237 - 0
  let E239 : Fin BB := Main[68] * E238
  let E240 : Fin BB := Main[34] - Main[63]
  let E241 : Fin BB := Main[49] * E240
  let E242 : Fin BB := E241 - 0
  let E243 : Fin BB := Main[68] * E242
  let E244 : Fin BB := Main[35] - Main[64]
  let E245 : Fin BB := Main[49] * E244
  let E246 : Fin BB := E245 - 0
  let E247 : Fin BB := Main[68] * E246
  let E248 : Fin BB := Main[50] * Main[32]
  let E249 : Fin BB := E248 - 0
  let E250 : Fin BB := Main[68] * E249
  let E251 : Fin BB := Main[50] * Main[33]
  let E252 : Fin BB := E251 - 0
  let E253 : Fin BB := Main[68] * E252
  let E254 : Fin BB := Main[50] * Main[34]
  let E255 : Fin BB := E254 - 0
  let E256 : Fin BB := Main[68] * E255
  let E257 : Fin BB := Main[35] - Main[63]
  let E258 : Fin BB := Main[50] * E257
  let E259 : Fin BB := E258 - 0
  let E260 : Fin BB := Main[68] * E259
  let E261 : Fin BB := Main[32] - Main[63]
  let E262 : Fin BB := Main[47] * E261
  let E263 : Fin BB := E262 - 0
  let E264 : Fin BB := Main[69] * E263
  let E265 : Fin BB := Main[33] - Main[64]
  let E266 : Fin BB := Main[47] * E265
  let E267 : Fin BB := E266 - 0
  let E268 : Fin BB := Main[69] * E267
  let E269 : Fin BB := Main[48] * Main[32]
  let E270 : Fin BB := E269 - 0
  let E271 : Fin BB := Main[69] * E270
  let E272 : Fin BB := Main[33] - Main[63]
  let E273 : Fin BB := Main[48] * E272
  let E274 : Fin BB := E273 - 0
  let E275 : Fin BB := Main[69] * E274
  let E276 : Fin BB := Main[67] * 65535
  let E277 : Fin BB := E276 - Main[34]
  let E278 : Fin BB := Main[69] * E277
  let E279 : Fin BB := Main[67] * 65535
  let E280 : Fin BB := E279 - Main[35]
  let E281 : Fin BB := Main[69] * E280
  let CS1 : SP1ConstraintList := U16MSBOperation.constraints Main[33] { msb := Main[67] } Main[69]
  let E282 : Fin BB := Main[68] * 6
  let E283 : Fin BB := Main[69] * 41
  let E284 : Fin BB := E282 + E283
  let E285 : Fin BB := Main[3] + 4
  let CS2 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E285, Main[4], Main[5]] 8 E0
  let E286 : Fin BB := Main[1] * 65536
  let E287 : Fin BB := Main[2] + E286
  let CS3 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E287 #v[Main[3], Main[4], Main[5]] E284 #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E0
  [
    (.assertZero E2),
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.assertZero E12),
    (.assertZero E14),
    (.assertZero E16),
    (.assertZero E18),
    (.assertZero E20),
    (.assertZero E22),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E40 0) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[55] E41 E53) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[56] E42 E53) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[57] E43 E53) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[58] E44 E53) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[59] E45 E53) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[60] E46 E53) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[61] E47 E53) E0),
    (.send (.byte (ByteOpcode.ofNat 6) Main[62] E48 E53) E0),
    (.assertZero E58),
    (.assertZero E60),
    (.assertZero E65),
    (.assertZero E67),
    (.assertZero E72),
    (.assertZero E74),
    (.assertZero E79),
    (.assertZero E81),
    (.assertZero E86),
    (.assertZero E92),
    (.assertZero E96),
    (.assertZero E98),
    (.assertZero E154),
    (.assertZero E170),
    (.assertZero E186),
    (.assertZero E202),
    (.assertZero E206),
    (.assertZero E210),
    (.assertZero E214),
    (.assertZero E218),
    (.assertZero E221),
    (.assertZero E225),
    (.assertZero E229),
    (.assertZero E233),
    (.assertZero E236),
    (.assertZero E239),
    (.assertZero E243),
    (.assertZero E247),
    (.assertZero E250),
    (.assertZero E253),
    (.assertZero E256),
    (.assertZero E260),
    (.assertZero E264),
    (.assertZero E268),
    (.assertZero E271),
    (.assertZero E275),
    (.assertZero E278),
    (.assertZero E281),
  ] ++ CS0 ++ CS1 ++ CS2 ++ CS3

end ShiftLeftChip

