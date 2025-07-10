-- Generated Lean code for chip ShiftRightChip
import SP1Foundations
import SP1Operations

namespace ShiftRightChip

set_option maxHeartbeats 1000000 in
def constraints (Main : Vector (Fin BB) 78) : SP1ConstraintList :=
  let E0 : Fin BB := Main[74] + Main[75]
  let E1 : Fin BB := E0 + Main[76]
  let E2 : Fin BB := E1 + Main[77]
  let E3 : Fin BB := Main[74] - 1
  let E4 : Fin BB := Main[74] * E3
  let E5 : Fin BB := Main[75] - 1
  let E6 : Fin BB := Main[75] * E5
  let E7 : Fin BB := Main[76] - 1
  let E8 : Fin BB := Main[76] * E7
  let E9 : Fin BB := Main[77] - 1
  let E10 : Fin BB := Main[77] * E9
  let E11 : Fin BB := E2 - 1
  let E12 : Fin BB := E2 * E11
  let E13 : Fin BB := Main[76] + Main[77]
  let E14 : Fin BB := 1 - E13
  let E15 : Fin BB := Main[74] * 7
  let E16 : Fin BB := Main[75] * 8
  let E17 : Fin BB := E15 + E16
  let E18 : Fin BB := Main[76] * 42
  let E19 : Fin BB := E17 + E18
  let E20 : Fin BB := Main[77] * 43
  let E21 : Fin BB := E19 + E20
  let E22 : Fin BB := Main[41] - 1
  let E23 : Fin BB := Main[41] * E22
  let E24 : Fin BB := Main[42] - 1
  let E25 : Fin BB := Main[42] * E24
  let E26 : Fin BB := Main[43] - 1
  let E27 : Fin BB := Main[43] * E26
  let E28 : Fin BB := Main[44] - 1
  let E29 : Fin BB := Main[44] * E28
  let E30 : Fin BB := Main[45] - 1
  let E31 : Fin BB := Main[45] * E30
  let E32 : Fin BB := Main[46] - 1
  let E33 : Fin BB := Main[46] * E32
  let E34 : Fin BB := Main[47] - 1
  let E35 : Fin BB := Main[47] * E34
  let E36 : Fin BB := Main[48] - 1
  let E37 : Fin BB := Main[48] * E36
  let E38 : Fin BB := Main[41] * 1
  let E39 : Fin BB := 0 + E38
  let E40 : Fin BB := Main[42] * 2
  let E41 : Fin BB := E39 + E40
  let E42 : Fin BB := Main[43] * 4
  let E43 : Fin BB := E41 + E42
  let E44 : Fin BB := Main[44] * 8
  let E45 : Fin BB := E43 + E44
  let E46 : Fin BB := Main[45] * 16
  let E47 : Fin BB := E45 + E46
  let E48 : Fin BB := Main[46] * 32
  let E49 : Fin BB := E47 + E48
  let E50 : Fin BB := Main[47] * 64
  let E51 : Fin BB := E49 + E50
  let E52 : Fin BB := Main[48] * 128
  let E53 : Fin BB := E51 + E52
  let E54 : Fin BB := Main[25] - E53
  let E55 : Fin BB := E54 * 2005401601
  let E56 : Fin BB := 1 - Main[41]
  let E57 : Fin BB := E56 + 1
  let E58 : Fin BB := E57 * 2
  let E59 : Fin BB := 1 - Main[42]
  let E60 : Fin BB := E59 * 3
  let E61 : Fin BB := E60 + 1
  let E62 : Fin BB := E58 * E61
  let E63 : Fin BB := Main[53] - E62
  let E64 : Fin BB := 1 - Main[43]
  let E65 : Fin BB := E64 * 15
  let E66 : Fin BB := E65 + 1
  let E67 : Fin BB := Main[53] * E66
  let E68 : Fin BB := Main[52] - E67
  let E69 : Fin BB := 1 - Main[44]
  let E70 : Fin BB := E69 * 255
  let E71 : Fin BB := E70 + 1
  let E72 : Fin BB := Main[52] * E71
  let E73 : Fin BB := Main[51] - E72
  let E74 : Fin BB := Main[52] * 256
  let E75 : Fin BB := E74 - Main[51]
  let E76 : Fin BB := E75 * 465814468
  let ⟨⟨⟨[E77, E78, E79, E80, E81, E82, E83, E84]⟩, _⟩, CS0⟩ := U16toU8OperationUnsafe.constraints #v[Main[37], Main[38], Main[39], Main[40]] { low_bytes := #v[Main[54], Main[55], Main[56], Main[57]] }
  let E85 : Fin BB := Main[37] - Main[15]
  let E86 : Fin BB := Main[38] - Main[16]
  let E87 : Fin BB := Main[17] * E14
  let E88 : Fin BB := E13 * 0
  let E89 : Fin BB := E87 + E88
  let E90 : Fin BB := Main[39] - E89
  let E91 : Fin BB := Main[18] * E14
  let E92 : Fin BB := E13 * 0
  let E93 : Fin BB := E91 + E92
  let E94 : Fin BB := Main[40] - E93
  let E95 : Fin BB := Main[42] * 2
  let E96 : Fin BB := Main[41] + E95
  let E97 : Fin BB := Main[43] * 4
  let E98 : Fin BB := E96 + E97
  let E99 : Fin BB := Main[59] * 256
  let E100 : Fin BB := Main[58] - E99
  let E101 : Fin BB := Main[60] * 256
  let E102 : Fin BB := Main[59] - E101
  let E103 : Fin BB := Main[61] * 256
  let E104 : Fin BB := Main[60] - E103
  let E105 : Fin BB := Main[62] * 256
  let E106 : Fin BB := Main[61] - E105
  let E107 : Fin BB := Main[63] * 256
  let E108 : Fin BB := Main[62] - E107
  let E109 : Fin BB := Main[64] * 256
  let E110 : Fin BB := Main[63] - E109
  let E111 : Fin BB := Main[65] * 256
  let E112 : Fin BB := Main[64] - E111
  let E113 : Fin BB := 0 + E79
  let E114 : Fin BB := E80 * 256
  let E115 : Fin BB := E113 + E114
  let E116 : Fin BB := E79 * 256
  let E117 : Fin BB := 0 + E116
  let E118 : Fin BB := E117 + E78
  let E119 : Fin BB := 0 + E81
  let E120 : Fin BB := E82 * 256
  let E121 : Fin BB := E119 + E120
  let E122 : Fin BB := E81 * 256
  let E123 : Fin BB := 0 + E122
  let E124 : Fin BB := E123 + E80
  let E125 : Fin BB := 0 + E83
  let E126 : Fin BB := E84 * 256
  let E127 : Fin BB := E125 + E126
  let E128 : Fin BB := E83 * 256
  let E129 : Fin BB := 0 + E128
  let E130 : Fin BB := E129 + E82
  let E131 : Fin BB := 0 + E84
  let E132 : Fin BB := E115 * E76
  let E133 : Fin BB := Main[52] - E76
  let E134 : Fin BB := E118 * E133
  let E135 : Fin BB := E132 + E134
  let E136 : Fin BB := E102 * Main[44]
  let E137 : Fin BB := E135 + E136
  let E138 : Fin BB := E104 * Main[44]
  let E139 : Fin BB := E138 * 256
  let E140 : Fin BB := E137 + E139
  let E141 : Fin BB := 1 - Main[44]
  let E142 : Fin BB := E100 * E141
  let E143 : Fin BB := E140 + E142
  let E144 : Fin BB := 1 - Main[44]
  let E145 : Fin BB := E102 * E144
  let E146 : Fin BB := E145 * 256
  let E147 : Fin BB := E143 + E146
  let E148 : Fin BB := Main[66] - E147
  let E149 : Fin BB := E121 * E76
  let E150 : Fin BB := Main[52] - E76
  let E151 : Fin BB := E124 * E150
  let E152 : Fin BB := E149 + E151
  let E153 : Fin BB := E106 * Main[44]
  let E154 : Fin BB := E152 + E153
  let E155 : Fin BB := E108 * Main[44]
  let E156 : Fin BB := E155 * 256
  let E157 : Fin BB := E154 + E156
  let E158 : Fin BB := 1 - Main[44]
  let E159 : Fin BB := E104 * E158
  let E160 : Fin BB := E157 + E159
  let E161 : Fin BB := 1 - Main[44]
  let E162 : Fin BB := E106 * E161
  let E163 : Fin BB := E162 * 256
  let E164 : Fin BB := E160 + E163
  let E165 : Fin BB := Main[67] - E164
  let E166 : Fin BB := E127 * E76
  let E167 : Fin BB := Main[52] - E76
  let E168 : Fin BB := E130 * E167
  let E169 : Fin BB := E166 + E168
  let E170 : Fin BB := E110 * Main[44]
  let E171 : Fin BB := E169 + E170
  let E172 : Fin BB := E112 * Main[44]
  let E173 : Fin BB := E172 * 256
  let E174 : Fin BB := E171 + E173
  let E175 : Fin BB := 1 - Main[44]
  let E176 : Fin BB := E108 * E175
  let E177 : Fin BB := E174 + E176
  let E178 : Fin BB := 1 - Main[44]
  let E179 : Fin BB := E110 * E178
  let E180 : Fin BB := E179 * 256
  let E181 : Fin BB := E177 + E180
  let E182 : Fin BB := Main[68] - E181
  let E183 : Fin BB := 0 * E76
  let E184 : Fin BB := Main[52] - E76
  let E185 : Fin BB := E131 * E184
  let E186 : Fin BB := E183 + E185
  let E187 : Fin BB := Main[65] * Main[44]
  let E188 : Fin BB := E186 + E187
  let E189 : Fin BB := 1 - Main[44]
  let E190 : Fin BB := E112 * E189
  let E191 : Fin BB := E188 + E190
  let E192 : Fin BB := 1 - Main[44]
  let E193 : Fin BB := Main[65] * E192
  let E194 : Fin BB := E193 * 256
  let E195 : Fin BB := E191 + E194
  let E196 : Fin BB := Main[69] - E195
  let CS1 : SP1ConstraintList := U16MSBOperation.constraints Main[40] { msb := Main[49] } Main[75]
  let CS2 : SP1ConstraintList := U16MSBOperation.constraints Main[38] { msb := Main[49] } Main[77]
  let E197 : Fin BB := Main[49] * Main[51]
  let E198 : Fin BB := Main[50] - E197
  let CS3 : SP1ConstraintList := U16MSBOperation.constraints Main[33] { msb := Main[36] } E13
  let E199 : Fin BB := Main[76] + Main[74]
  let E200 : Fin BB := Main[49] - 0
  let E201 : Fin BB := E199 * E200
  let E202 : Fin BB := Main[46] * 2
  let E203 : Fin BB := E202 * E14
  let E204 : Fin BB := Main[45] + E203
  let E205 : Fin BB := E204 - 0
  let E206 : Fin BB := Main[70] * E205
  let E207 : Fin BB := Main[70] - 1
  let E208 : Fin BB := Main[70] * E207
  let E209 : Fin BB := Main[46] * 2
  let E210 : Fin BB := E209 * E14
  let E211 : Fin BB := Main[45] + E210
  let E212 : Fin BB := E211 - 1
  let E213 : Fin BB := Main[71] * E212
  let E214 : Fin BB := Main[71] - 1
  let E215 : Fin BB := Main[71] * E214
  let E216 : Fin BB := Main[46] * 2
  let E217 : Fin BB := E216 * E14
  let E218 : Fin BB := Main[45] + E217
  let E219 : Fin BB := E218 - 2
  let E220 : Fin BB := Main[72] * E219
  let E221 : Fin BB := Main[72] - 1
  let E222 : Fin BB := Main[72] * E221
  let E223 : Fin BB := Main[46] * 2
  let E224 : Fin BB := E223 * E14
  let E225 : Fin BB := Main[45] + E224
  let E226 : Fin BB := E225 - 3
  let E227 : Fin BB := Main[73] * E226
  let E228 : Fin BB := Main[73] - 1
  let E229 : Fin BB := Main[73] * E228
  let E230 : Fin BB := Main[70] + Main[71]
  let E231 : Fin BB := E230 + Main[72]
  let E232 : Fin BB := E231 + Main[73]
  let E233 : Fin BB := E232 - 1
  let E234 : Fin BB := E2 * E233
  let E235 : Fin BB := Main[32] - Main[66]
  let E236 : Fin BB := Main[70] * E235
  let E237 : Fin BB := E236 - 0
  let E238 : Fin BB := E14 * E237
  let E239 : Fin BB := Main[33] - Main[67]
  let E240 : Fin BB := Main[70] * E239
  let E241 : Fin BB := E240 - 0
  let E242 : Fin BB := E14 * E241
  let E243 : Fin BB := Main[34] - Main[68]
  let E244 : Fin BB := Main[70] * E243
  let E245 : Fin BB := E244 - 0
  let E246 : Fin BB := E14 * E245
  let E247 : Fin BB := Main[35] - Main[69]
  let E248 : Fin BB := Main[49] * 65536
  let E249 : Fin BB := E248 - Main[50]
  let E250 : Fin BB := E247 - E249
  let E251 : Fin BB := Main[70] * E250
  let E252 : Fin BB := E251 - 0
  let E253 : Fin BB := E14 * E252
  let E254 : Fin BB := Main[32] - Main[67]
  let E255 : Fin BB := Main[71] * E254
  let E256 : Fin BB := E255 - 0
  let E257 : Fin BB := E14 * E256
  let E258 : Fin BB := Main[33] - Main[68]
  let E259 : Fin BB := Main[71] * E258
  let E260 : Fin BB := E259 - 0
  let E261 : Fin BB := E14 * E260
  let E262 : Fin BB := Main[34] - Main[69]
  let E263 : Fin BB := Main[49] * 65536
  let E264 : Fin BB := E263 - Main[50]
  let E265 : Fin BB := E262 - E264
  let E266 : Fin BB := Main[71] * E265
  let E267 : Fin BB := E266 - 0
  let E268 : Fin BB := E14 * E267
  let E269 : Fin BB := Main[49] * 65535
  let E270 : Fin BB := Main[35] - E269
  let E271 : Fin BB := Main[71] * E270
  let E272 : Fin BB := E271 - 0
  let E273 : Fin BB := E14 * E272
  let E274 : Fin BB := Main[32] - Main[68]
  let E275 : Fin BB := Main[72] * E274
  let E276 : Fin BB := E275 - 0
  let E277 : Fin BB := E14 * E276
  let E278 : Fin BB := Main[33] - Main[69]
  let E279 : Fin BB := Main[49] * 65536
  let E280 : Fin BB := E279 - Main[50]
  let E281 : Fin BB := E278 - E280
  let E282 : Fin BB := Main[72] * E281
  let E283 : Fin BB := E282 - 0
  let E284 : Fin BB := E14 * E283
  let E285 : Fin BB := Main[49] * 65535
  let E286 : Fin BB := Main[34] - E285
  let E287 : Fin BB := Main[72] * E286
  let E288 : Fin BB := E287 - 0
  let E289 : Fin BB := E14 * E288
  let E290 : Fin BB := Main[49] * 65535
  let E291 : Fin BB := Main[35] - E290
  let E292 : Fin BB := Main[72] * E291
  let E293 : Fin BB := E292 - 0
  let E294 : Fin BB := E14 * E293
  let E295 : Fin BB := Main[32] - Main[69]
  let E296 : Fin BB := Main[49] * 65536
  let E297 : Fin BB := E296 - Main[50]
  let E298 : Fin BB := E295 - E297
  let E299 : Fin BB := Main[73] * E298
  let E300 : Fin BB := E299 - 0
  let E301 : Fin BB := E14 * E300
  let E302 : Fin BB := Main[49] * 65535
  let E303 : Fin BB := Main[33] - E302
  let E304 : Fin BB := Main[73] * E303
  let E305 : Fin BB := E304 - 0
  let E306 : Fin BB := E14 * E305
  let E307 : Fin BB := Main[49] * 65535
  let E308 : Fin BB := Main[34] - E307
  let E309 : Fin BB := Main[73] * E308
  let E310 : Fin BB := E309 - 0
  let E311 : Fin BB := E14 * E310
  let E312 : Fin BB := Main[49] * 65535
  let E313 : Fin BB := Main[35] - E312
  let E314 : Fin BB := Main[73] * E313
  let E315 : Fin BB := E314 - 0
  let E316 : Fin BB := E14 * E315
  let E317 : Fin BB := Main[32] - Main[66]
  let E318 : Fin BB := Main[70] * E317
  let E319 : Fin BB := E318 - 0
  let E320 : Fin BB := E13 * E319
  let E321 : Fin BB := Main[32] - Main[67]
  let E322 : Fin BB := Main[49] * 65536
  let E323 : Fin BB := E322 - Main[50]
  let E324 : Fin BB := E321 - E323
  let E325 : Fin BB := Main[71] * E324
  let E326 : Fin BB := E325 - 0
  let E327 : Fin BB := E13 * E326
  let E328 : Fin BB := Main[49] * 65535
  let E329 : Fin BB := Main[33] - E328
  let E330 : Fin BB := Main[71] * E329
  let E331 : Fin BB := E330 - 0
  let E332 : Fin BB := E13 * E331
  let E333 : Fin BB := Main[36] * 65535
  let E334 : Fin BB := Main[34] - E333
  let E335 : Fin BB := E13 * E334
  let E336 : Fin BB := Main[36] * 65535
  let E337 : Fin BB := Main[35] - E336
  let E338 : Fin BB := E13 * E337
  let E339 : Fin BB := Main[3] + 4
  let CS4 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E339, Main[4], Main[5]] 8 E2
  let E340 : Fin BB := Main[1] * 65536
  let E341 : Fin BB := Main[2] + E340
  let CS5 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E341 #v[Main[3], Main[4], Main[5]] E21 #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E2
  [
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.assertZero E12),
    (.assertZero E23),
    (.assertZero E25),
    (.assertZero E27),
    (.assertZero E29),
    (.assertZero E31),
    (.assertZero E33),
    (.assertZero E35),
    (.assertZero E37),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E55 0) E2),
    (.assertZero E63),
    (.assertZero E68),
    (.assertZero E73),
    (.assertZero E85),
    (.assertZero E86),
    (.assertZero E90),
    (.assertZero E94),
    (.send (.byte (ByteOpcode.ofNat 6) Main[58] E77 E98) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[59] E78 E98) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[60] E79 E98) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[61] E80 E98) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[62] E81 E98) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[63] E82 E98) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[64] E83 E98) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[65] E84 E98) E2),
    (.assertZero E148),
    (.assertZero E165),
    (.assertZero E182),
    (.assertZero E196),
    (.assertZero E198),
    (.assertZero E201),
    (.assertZero E206),
    (.assertZero E208),
    (.assertZero E213),
    (.assertZero E215),
    (.assertZero E220),
    (.assertZero E222),
    (.assertZero E227),
    (.assertZero E229),
    (.assertZero E234),
    (.assertZero E238),
    (.assertZero E242),
    (.assertZero E246),
    (.assertZero E253),
    (.assertZero E257),
    (.assertZero E261),
    (.assertZero E268),
    (.assertZero E273),
    (.assertZero E277),
    (.assertZero E284),
    (.assertZero E289),
    (.assertZero E294),
    (.assertZero E301),
    (.assertZero E306),
    (.assertZero E311),
    (.assertZero E316),
    (.assertZero E320),
    (.assertZero E327),
    (.assertZero E332),
    (.assertZero E335),
    (.assertZero E338),
  ] ++ CS0 ++ CS1 ++ CS2 ++ CS3 ++ CS4 ++ CS5

end ShiftRightChip
