import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace ShiftRight

set_option maxHeartbeats 100000000

variable (Main : Vector (Fin BB) 69)
def is_real : Prop := Main[64] = 1 ∨ Main[65] = 1 ∨ Main[66] = 1 ∨ Main[67] = 1

section constraints

-- Generated Lean code for chip ShiftRightChip
def constraints : SP1ConstraintList :=
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

lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    let b0 := Main[15]
    let b1 := Main[16]
    let b2 := Main[17]
    let b3 := Main[18]
    let c0 := Main[25]
    let c1 := Main[26]
    let c2 := Main[27]
    let c3 := Main[28]
    let imm := Main[31]
    let a0 := Main[32]
    let a1 := Main[33]
    let a2 := Main[34]
    let a3 := Main[35]
    let msb_b := Main[36]
    let msb_srw := Main[37]
    let cb0 := Main[38]
    let cb1 := Main[39]
    let cb2 := Main[40]
    let cb3 := Main[41]
    let cb4 := Main[42]
    let cb5 := Main[43]
    let smv := Main[44]
    let v0123 := Main[45]
    let v012 := Main[46]
    let v01 := Main[47]
    let ll0 := Main[48]
    let ll1 := Main[49]
    let ll2 := Main[50]
    let ll3 := Main[51]
    let hl0 := Main[52]
    let hl1 := Main[53]
    let hl2 := Main[54]
    let hl3 := Main[55]
    let lr0 := Main[56]
    let lr1 := Main[57]
    let lr2 := Main[58]
    let lr3 := Main[59]
    let su160 := Main[60]
    let su161 := Main[61]
    let su162 := Main[62]
    let su163 := Main[63]
    let srl := Main[64]
    let sra := Main[65]
    let srlw := Main[66]
    let sraw := Main[67]
    let bop := Main[68]
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints b3 { msb := msb_b } sra) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints b1 { msb := msb_b } sraw) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints a1 { msb := msb_srw } (srlw + sraw)) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (srl + sra + srlw + sraw)) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (srl * 7 + sra * 8 + srlw * 42 + sraw * 43) #v[bop, (srl * 5 + sra * 5 + srlw * 5 + sraw * 5), (sra * 32 + sraw * 32)] #v[a0, a1, a2, a3] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[c0, c1, c2, c3], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := imm } (srl + sra + srlw + sraw)) ∧
    (srl = 0 ∨ srl = 1) ∧
    (sra = 0 ∨ sra = 1) ∧
    (srlw = 0 ∨ srlw = 1) ∧
    (sraw = 0 ∨ sraw = 1) ∧
    (srl + sra + srlw + sraw = 0 ∨ srl + sra + srlw + sraw = 1) ∧
    (srl + sra + srlw + sraw = 0 ∨ bop = imm * (srl * 19 + sra * 19 + srlw * 27 + sraw * 27) + (1 - imm) * (srl * 51 + sra * 51 + srlw * 59 + sraw * 59)) ∧
    (cb0 = 0 ∨ cb0 = 1) ∧
    (cb1 = 0 ∨ cb1 = 1) ∧
    (cb2 = 0 ∨ cb2 = 1) ∧
    (cb3 = 0 ∨ cb3 = 1) ∧
    (cb4 = 0 ∨ cb4 = 1) ∧
    (cb5 = 0 ∨ cb5 = 1) ∧
    (¬srl + sra + srlw + sraw = 0 → ((Main[25] - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)) * 1981808641).val < 1024) ∧
    (su160 = 0 ∨ cb4 + cb5 * 2 * (srl + sra) = 0) ∧
    (su160 = 0 ∨ su160 = 1) ∧
    (su161 = 0 ∨ cb4 + cb5 * 2 * (srl + sra) = 1) ∧
    (su161 = 0 ∨ su161 = 1) ∧
    (su162 = 0 ∨ cb4 + cb5 * 2 * (srl + sra) = 2) ∧
    (su162 = 0 ∨ su162 = 1) ∧
    (su163 = 0 ∨ cb4 + cb5 * 2 * (srl + sra) = 3) ∧
    (su163 = 0 ∨ su163 = 1) ∧
    (srl + sra + srlw + sraw = 0 ∨ su160 + su161 + su162 + su163 = 1) ∧
    (v01 = (1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1)) ∧
    (v012 = v01 * ((1 - cb2) * 15 + 1)) ∧
    (v0123 = v012 * ((1 - cb3) * 255 + 1)) ∧
    (¬srl + sra + srlw + sraw = 0 → ll0.val < 2 ^ (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8).val) ∧
    (¬srl + sra + srlw + sraw = 0 → hl0.val < 2 ^ (16 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8)).val) ∧
    (b0 * v0123 = hl0 * 65536 + ll0 * v0123) ∧
    (¬srl + sra + srlw + sraw = 0 → ll1.val < 2 ^ (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8).val) ∧
    (¬srl + sra + srlw + sraw = 0 → hl1.val < 2 ^ (16 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8)).val) ∧
    (b1 * v0123 = hl1 * 65536 + ll1 * v0123) ∧
    (¬srl + sra + srlw + sraw = 0 → ll2.val < 2 ^ (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8).val) ∧
    (¬srl + sra + srlw + sraw = 0 → hl2.val < 2 ^ (16 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8)).val) ∧
    (b2 * v0123 * (srl + sra) = hl2 * 65536 + ll2 * v0123) ∧
    (¬srl + sra + srlw + sraw = 0 → ll3.val < 2 ^ (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8).val) ∧
    (¬srl + sra + srlw + sraw = 0 → hl3.val < 2 ^ (16 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8)).val) ∧
    (b3 * v0123 * (srl + sra) = hl3 * 65536 + ll3 * v0123) ∧
    (lr0 = hl0 + ll1 * v0123) ∧
    (lr1 = hl1 + ll2 * v0123) ∧
    (lr2 = hl2 + ll3 * v0123) ∧
    (lr3 = hl3) ∧
    (srl + srlw = 0 ∨ msb_b = 0) ∧
    (smv = msb_b * v0123) ∧
    (srlw + sraw = 1 ∨ msb_srw = 0) ∧
    (srl + sra = 0 ∨ su160 = 0 ∨ a0 = lr0) ∧
    (srl + sra = 0 ∨ su160 = 0 ∨ a1 = lr1) ∧
    (srl + sra = 0 ∨ su160 = 0 ∨ a2 = lr2) ∧
    (srl + sra = 0 ∨ su160 = 0 ∨ a3 = lr3 + (msb_b * 65536 - smv)) ∧
    (srl + sra = 0 ∨ su161 = 0 ∨ a0 = lr1) ∧
    (srl + sra = 0 ∨ su161 = 0 ∨ a1 = lr2) ∧
    (srl + sra = 0 ∨ su161 = 0 ∨ a2 = lr3 + (msb_b * 65536 - smv)) ∧
    (srl + sra = 0 ∨ su161 = 0 ∨ a3 = msb_b * 65535) ∧
    (srl + sra = 0 ∨ su162 = 0 ∨ a0 = lr2) ∧
    (srl + sra = 0 ∨ su162 = 0 ∨ a1 = lr3 + (msb_b * 65536 - smv)) ∧
    (srl + sra = 0 ∨ su162 = 0 ∨ a2 = msb_b * 65535) ∧
    (srl + sra = 0 ∨ su162 = 0 ∨ a3 = msb_b * 65535) ∧
    (srl + sra = 0 ∨ su163 = 0 ∨ a0 = lr3 + (msb_b * 65536 - smv)) ∧
    (srl + sra = 0 ∨ su163 = 0 ∨ a1 = msb_b * 65535) ∧
    (srl + sra = 0 ∨ su163 = 0 ∨ a2 = msb_b * 65535) ∧
    (srl + sra = 0 ∨ su163 = 0 ∨ a3 = msb_b * 65535) ∧
    (srlw + sraw = 0 ∨ su160 = 0 ∨ a0 = lr0) ∧
    (srlw + sraw = 0 ∨ su160 = 0 ∨ a1 = lr1 + (msb_b * 65536 - smv)) ∧
    (srlw + sraw = 0 ∨ su161 = 0 ∨ a0 = lr1 + (msb_b * 65536 - smv)) ∧
    (srlw + sraw = 0 ∨ su161 = 0 ∨ a1 = msb_b * 65535) ∧
    (srlw + sraw = 0 ∨ a2 = msb_srw * 65535) ∧
    (srlw + sraw = 0 ∨ a3 = msb_srw * 65535)
  := by
    simp [constraints, sub_eq_zero]

end constraints

section field_arithmetic

lemma cancel_mul_65536_v1 { a b c x : Fin BB } (h_dvd : (x : ℕ) ∣ 65536) : a * x = b * 65536 + c * x → a = b * ((65536 : ℕ) / (x : ℕ)) + c
  := by
  obtain ⟨ z, h_eq ⟩ := h_dvd; rw [h_eq]
  have x_pos : 0 < (x : ℕ) := by nlinarith
  have xz_BB : (x : ℕ) * z < 2013265921 := by nlinarith
  have h_eq_BB : 65536 = x * z := by simp [Fin.ext_iff, Fin.mul_def]; omega
  rw [h_eq_BB]
  rw [mul_comm x z, ← mul_assoc, ← right_distrib]
  intro eq; apply mul_right_cancel₀ (by omega) at eq; rw [eq]
  congr
  rw [Fin.ext_iff]; simp [Fin.mul_def]
  rw [Nat.mod_eq_of_lt (by nlinarith)]
  rw [Nat.mod_eq_of_lt (by omega)]
  aesop

lemma cancel_mul_65536_v2 { b c x : Fin BB } (h_dvd : (x : ℕ) ∣ 65536) : b * 65536 + c * x = 0 → b * ((65536 : ℕ) / (x : ℕ)) + c = 0
  := by intro h_eq; symm; apply cancel_mul_65536_v1 <;> aesop

lemma is_mod_64 {c0 m : Fin BB} : m < 64 → c0 < 65536 → ((c0 - m) * 1981808641).val < 1024 → c0.val % 64 = m := by
  simp [Fin.sub_def, Fin.mul_def, Fin.lt_def]; ring_nf
  intro hm hc hdiff
  suffices : (BitVec.ofNat 64 c0.val) % 64#64 = BitVec.ofNat 64 m.val
  . simp [BitVec.toNat_eq] at this
    repeat rw [Nat.mod_eq_of_lt (b := 18446744073709551616) (by omega)] at this
    assumption
  . suffices : ((2013265921 - BitVec.ofNat 64 ↑m) * BitVec.ofNat 64 1981808641 + BitVec.ofNat 64 ↑c0 * 1981808641#64) % 2013265921#64 < 1024#64
    . clear hdiff
      have : BitVec.ofNat 64 c0.val < 65536 := by simp; omega
      have : BitVec.ofNat 64 m.val < 64 := by simp; omega
      clear hm
      trans (BitVec.ofNat 64 ↑c0) &&& 63#64
      . bv_decide
      . bv_decide
    . rw [← BitVec.ult_iff_lt]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul]
      simp [-BitVec.toNat_sub]
      rw [BitVec.toNat_sub_of_le] <;> simp
      . repeat rw [Nat.mod_eq_of_lt (b := 18446744073709551616) (by omega)]
        assumption
      . omega

end field_arithmetic

section opcodes

@[simp] def is_srl := Main[64] = 1 ∧ Main[31] = 0
@[simp] def is_sra := Main[65] = 1 ∧ Main[31] = 0
@[simp] def is_srlw := Main[66] = 1 ∧ Main[31] = 0
@[simp] def is_sraw := Main[67] = 1 ∧ Main[31] = 0
@[simp] def is_srli := Main[64] = 1 ∧ Main[31] = 1
@[simp] def is_srai := Main[65] = 1 ∧ Main[31] = 1
@[simp] def is_srliw := Main[66] = 1 ∧ Main[31] = 1
@[simp] def is_sraiw := Main[67] = 1 ∧ Main[31] = 1

lemma single_op : List.Forall SP1Constraint.toProp (constraints Main) →
  (Main[64] = 1 → Main[65] = 0 ∧ Main[66] = 0 ∧ Main[67] = 0) ∧
  (Main[65] = 1 → Main[64] = 0 ∧ Main[66] = 0 ∧ Main[67] = 0) ∧
  (Main[66] = 1 → Main[64] = 0 ∧ Main[65] = 0 ∧ Main[67] = 0) ∧
  (Main[67] = 1 → Main[64] = 0 ∧ Main[65] = 0 ∧ Main[66] = 0)
   := by
  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, rest ⟩ := cstrs
  clear *- b_srl b_sra b_srlw b_sraw one_of_ops
  aesop

lemma single_su16 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  (Main[60] = 1 → Main[61] = 0 ∧ Main[62] = 0 ∧ Main[63] = 0) ∧
  (Main[61] = 1 → Main[60] = 0 ∧ Main[62] = 0 ∧ Main[63] = 0) ∧
  (Main[62] = 1 → Main[60] = 0 ∧ Main[61] = 0 ∧ Main[63] = 0) ∧
  (Main[63] = 1 → Main[60] = 0 ∧ Main[61] = 0 ∧ Main[62] = 0)
   := by
  intro cstrs real
  have ⟨ srl, srlw, sra, sraw ⟩ := single_op Main cstrs
  simp [allHold_constraints_iff] at cstrs; simp [is_real] at real
  obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
            b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
            h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
            eq_v01, eq_v012, eq_v0123,
            lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
            lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
            eq_lr0, eq_lr1, eq_lr2, eq_lr3,
            w_msb_b, eq_smv, w_msb_srv,
            nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
            w_00, w_01, w_02, w_03, w_04, w_05 ⟩ := cstrs
  clear *- real srl srlw sra sraw b_su160 b_su161 b_su162 b_su163 one_of_su16s
  rcases one_of_su16s
  . rcases real with _ | _ | _ | _ <;> simp_all
  . clear real srl srlw sra sraw; aesop

end opcodes

section is_real

lemma srl_real : Main[64] = 1 → is_real Main := by simp [is_real]; aesop
lemma sra_real : Main[65] = 1 → is_real Main := by simp [is_real]; aesop
lemma srlw_real : Main[66] = 1 → is_real Main := by simp [is_real]; aesop
lemma sraw_real : Main[67] = 1 → is_real Main := by simp [is_real]; aesop

end is_real

section entailed_constraints

lemma register_bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let imm := Main[31]
  Main[6] < 32 ∧ Main[14] < 32 ∧ (imm = 0 → Main[21] < 32) ∧ Main[3] < 65536
    := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h0, h1, h2, h3, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, h4 ⟩ := cstrs
  clear h0 h1 h2 h3 h4
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  . obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19 ⟩ := alu
    rcases real with srl | sra | srlw | sraw <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq] <;>
    rcases b_imm <;> simp_all
  . clear alu; rcases real with srl | sra | srlw | sraw <;> simp_all

lemma immediate_bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let imm := Main[31]
  (imm = 1 →
    (Main[21] = Main[25] ∧ Main[26] = 0 ∧ Main[27] = 0 ∧ Main[28] = 0 ∧
      ((Main[64] = 1 ∨ Main[65] = 1 → Main[25] < 64) ∧
       (Main[66] = 1 ∨ Main[67] = 1 → Main[25] < 32)))) := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h0, h1, h2, h3, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, h4 ⟩ := cstrs
  clear h0 h1 h2 h3 h4
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  . obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19 ⟩ := alu
    rcases real with srl | sra | srlw | sraw <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq]
  . clear alu; rcases real with srl | sra | srlw | sraw <;> simp_all

lemma op_a_is_0 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  (Main[6] = 0 → Main[32] = 0 ∧ Main[33] = 0 ∧ Main[34] = 0 ∧ Main[35] = 0) := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
  have ⟨ su1, su2, su3, su4 ⟩ := single_su16 Main cstrs real
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h0, h1, h2, h3, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, h4 ⟩ := cstrs
  clear h0 h1 h2 h3 h4
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  . obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19 ⟩ := alu
    clear *- h4 h5 h18; simp_all; aesop
  . clear alu; rcases real with srl | sra | srlw | sraw <;> simp_all

lemma ops_U64_b_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := by
  intro cstrs real
  have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h0, h1, h2, h3, alu,
          b_srl, b_sra, b_srlw, b_sraw, one_of_ops, h4 ⟩ := cstrs
  clear h0 h1 h2 h3 h4
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  . obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19 ⟩ := alu
    rcases real with srl | sra | srlw | sraw <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq] <;>
    rcases b_imm <;> simp_all <;> apply Word.isU64_of_cases <;> simp <;> omega
  . clear alu; rcases real with srl | sra | srlw | sraw <;> simp_all

lemma ops_U64_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[32], Main[33], Main[34], Main[35]] := by
  intro cstrs real
  have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs real
  obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
  obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
  have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op Main cstrs
  have ⟨ su1, su2, su3, su4 ⟩ := single_su16 Main cstrs real
  simp [is_real] at real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
            b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
            h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
            eq_v01, eq_v012, eq_v0123,
            lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
            lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
            eq_lr0, eq_lr1, eq_lr2, eq_lr3,
            w_msb_b, eq_smv, w_msb_srv,
            nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
            w_00, w_01, w_02, w_03, w_04, w_05 ⟩ := cstrs
  clear cpu alu

  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]
  set c0 := Main[25]
  set c1 := Main[26]
  set c2 := Main[27]
  set c3 := Main[28]
  set imm := Main[31]
  set a0 := Main[32]
  set a1 := Main[33]
  set a2 := Main[34]
  set a3 := Main[35]
  set msb_b := Main[36]
  set msb_srw := Main[37]
  set cb0 := Main[38]
  set cb1 := Main[39]
  set cb2 := Main[40]
  set cb3 := Main[41]
  set cb4 := Main[42]
  set cb5 := Main[43]
  set smv := Main[44]
  set v0123 := Main[45]
  set v012 := Main[46]
  set v01 := Main[47]
  set ll0 := Main[48]
  set ll1 := Main[49]
  set ll2 := Main[50]
  set ll3 := Main[51]
  set hl0 := Main[52]
  set hl1 := Main[53]
  set hl2 := Main[54]
  set hl3 := Main[55]
  set lr0 := Main[56]
  set lr1 := Main[57]
  set lr2 := Main[58]
  set lr3 := Main[59]
  set su160 := Main[60]
  set su161 := Main[61]
  set su162 := Main[62]
  set su163 := Main[63]
  set srl := Main[64]
  set sra := Main[65]
  set srlw := Main[66]
  set sraw := Main[67]
  set bop := Main[68]

  suffices : a0.val < 65536 ∧ a1.val < 65536 ∧ a2.val < 65536 ∧ a3.val < 65536
  . clear *- this; apply Word.isU64_of_cases <;> simp <;> tauto
  . clear diff eq_bop
    rcases real with hsrl | hsra | hsrlw | hsraw

    . simp_all

      have a0_16 : (hl0 + ll1 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b0_16 b1_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b0_dec h_b1_dec lt_ll0 lt_ll1 lt_hl0 lt_hl1
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b0_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          try omega
        }
      have a1_16 : (hl1 + ll2 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b1_16 b2_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b1_dec h_b2_dec lt_ll1 lt_ll2 lt_hl1 lt_hl2
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
          try simp [Fin.val_add, Fin.val_mul] at b1_16 b2_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          try omega
        }
      have a2_16 : (hl2 + ll3 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b2_16 b3_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec h_b3_dec lt_ll2 lt_ll3 lt_hl2 lt_hl3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b3_dec
          try simp [Fin.val_add, Fin.val_mul] at b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          try omega
        }
      have a3_16 : hl3.val < 65536 := by
        clear *- b_cb0 b_cb1 b_cb2 b_cb3 b3_16 h_b3_dec lt_ll3 lt_hl3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals { clear *- lt_hl3; omega }

      rcases b_su160 <;> simp_all
      rcases b_su161 <;> simp_all
      rcases b_su162 <;> simp_all

    . simp_all

      have a0_16 : (hl0 + ll1 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b0_16 b1_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b0_dec h_b1_dec lt_ll0 lt_ll1 lt_hl0 lt_hl1
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b0_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          try omega
        }
      have a1_16 : (hl1 + ll2 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b1_16 b2_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b1_dec h_b2_dec lt_ll1 lt_ll2 lt_hl1 lt_hl2
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
          try simp [Fin.val_add, Fin.val_mul] at b1_16 b2_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          try omega
        }
      have a2_16 : (hl2 + ll3 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b2_16 b3_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec h_b3_dec lt_ll2 lt_ll3 lt_hl2 lt_hl3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b3_dec
          try simp [Fin.val_add, Fin.val_mul] at b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          try omega
        }
      have a3_16 : (hl3 + (msb_b * 65536 - msb_b * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1)))).val < 65536 := by
        clear *- h_msb_b3 b_cb0 b_cb1 b_cb2 b_cb3 b3_16 h_b3_dec lt_ll3 lt_hl3
        rw [← SP1ConstraintList.allHold, U16MSBOperation.allHold_constraints_iff] at h_msb_b3
        obtain ⟨ _, b_msb_b3, _ ⟩ := h_msb_b3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> rcases b_msb_b3 <;> simp_all
        all_goals { clear *- lt_hl3; omega }
      have msb_b : (msb_b * 65535).val < 65536 := by
        suffices b_msb : msb_b = 0 ∨ msb_b = 1
        . clear *- b_msb;rcases b_msb <;> simp_all
        . rw [← SP1ConstraintList.allHold, U16MSBOperation.allHold_constraints_iff] at h_msb_b3
          clear *- h_msb_b3; simp_all
      rcases b_su160 <;> simp_all
      rcases b_su161 <;> simp_all
      rcases b_su162 <;> simp_all

    . symm at h_b2_dec h_b3_dec
      simp_all

      have ⟨ eq_hl2, eq_ll2 ⟩ : hl2 = 0 ∧ ll2 = 0 := by
        clear *- lt_hl2 lt_ll2 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
        apply (cancel_mul_65536_v2 (by simp)) at h_b2_dec <;>
        simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b2_dec <;>
        rw [Nat.mod_eq_of_lt (by omega)] at h_b2_dec <;>
        split_ands <;> omega

      have ⟨ eq_hl3, eq_ll3 ⟩ : hl3 = 0 ∧ ll3 = 0 := by
        clear *- lt_hl3 lt_ll3 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
        apply (cancel_mul_65536_v2 (by simp)) at h_b3_dec <;>
        simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b3_dec <;>
        rw [Nat.mod_eq_of_lt (by omega)] at h_b3_dec <;>
        split_ands <;> omega

      simp [eq_hl2, eq_ll2, eq_hl3, eq_ll3] at *
      simp_all

      have a0_16 : (hl0 + ll1 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b0_16 b1_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b0_dec h_b1_dec lt_ll0 lt_ll1 lt_hl0 lt_hl1
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b0_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          try omega
        }
      have a1_16 : hl1.val < 65536 := by
        clear *- b1_16 b2_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b1_dec lt_ll1 lt_hl1
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          try simp [Fin.val_add, Fin.val_mul] at b1_16 b2_16 ⊢
          try omega
        }
      have msb_16 : (msb_srw * 65535).val < 65536 := by
        suffices b_msb : msb_srw = 0 ∨ msb_srw = 1
        . clear *- b_msb; rcases b_msb <;> simp_all
        . rw [← SP1ConstraintList.allHold, U16MSBOperation.allHold_constraints_iff] at h_msb_a1
          clear *- h_msb_a1; simp_all

      rcases b_su160 <;> simp_all
      rcases b_su161 <;> simp_all
      rcases b_su162 <;> simp_all

    . symm at h_b2_dec h_b3_dec
      simp_all

      have ⟨ eq_hl2, eq_ll2 ⟩ : hl2 = 0 ∧ ll2 = 0 := by
        clear *- lt_hl2 lt_ll2 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
        apply (cancel_mul_65536_v2 (by simp)) at h_b2_dec <;>
        simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b2_dec <;>
        rw [Nat.mod_eq_of_lt (by omega)] at h_b2_dec <;>
        split_ands <;> omega

      have ⟨ eq_hl3, eq_ll3 ⟩ : hl3 = 0 ∧ ll3 = 0 := by
        clear *- lt_hl3 lt_ll3 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
        apply (cancel_mul_65536_v2 (by simp)) at h_b3_dec <;>
        simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b3_dec <;>
        rw [Nat.mod_eq_of_lt (by omega)] at h_b3_dec <;>
        split_ands <;> omega

      simp [eq_hl2, eq_ll2, eq_hl3, eq_ll3] at *
      simp_all

      have a0_16 : (hl0 + ll1 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b0_16 b1_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b0_dec h_b1_dec lt_ll0 lt_ll1 lt_hl0 lt_hl1
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b0_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          try omega
        }
      have a1_16 : (hl1 + (msb_b * 65536 - msb_b * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1)))).val < 65536 := by
        clear *- h_msb_b3 b1_16 b2_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b1_dec lt_ll1 lt_hl1
        rw [← SP1ConstraintList.allHold, U16MSBOperation.allHold_constraints_iff] at h_msb_b3
        obtain ⟨ _, b_msb_b3, _ ⟩ := h_msb_b3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> rcases b_msb_b3 <;> simp_all
        all_goals { clear *- lt_hl1; omega }
      have msb_b: (msb_b * 65535).val < 65536 := by
        suffices b_msb_b : msb_b = 0 ∨ msb_b = 1
        . clear *- b_msb_b; rcases b_msb_b <;> simp_all
        . rw [← SP1ConstraintList.allHold, U16MSBOperation.allHold_constraints_iff] at h_msb_b1
          clear *- h_msb_b1; simp_all
      have msb_srw : (msb_srw * 65535).val < 65536 := by
        suffices b_msb_srw : msb_srw = 0 ∨ msb_srw = 1
        . clear *- b_msb_srw; rcases b_msb_srw <;> simp_all
        . rw [← SP1ConstraintList.allHold, U16MSBOperation.allHold_constraints_iff] at h_msb_a1
          clear *- h_msb_a1; simp_all

      rcases b_su160 <;> simp_all
      rcases b_su161 <;> simp_all
      rcases b_su162 <;> simp_all

lemma ops_U64 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[32], Main[33], Main[34], Main[35]] ∧
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]]
    := by
  intro cstrs real
  constructor
  . exact ops_U64_a Main cstrs real
  . exact ops_U64_b_c Main cstrs real

end entailed_constraints

section operands

@[simp]
def sp1_op_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[6] ?_
  show Main[6] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_b : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[14] ?_
  show Main[14] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 0 → BitVec 5 := by
  intro cstrs real imm
  refine BitVec.ofNatLT Main[21] ?_
  show Main[21] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c_imm : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[64] = 1 ∨ Main[65] = 1 → BitVec 6 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have := immediate_bounds Main cstrs real
  simp_all
  omega

@[simp]
def sp1_op_c_imm_w : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[66] = 1 ∨ Main[67] = 1 → BitVec 5 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have := immediate_bounds Main cstrs real
  simp_all
  omega

end operands

section srl

lemma spec.srl (h : is_srl Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRL
  := by
    intro cstrs
    obtain ⟨ eq_srl, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (srl_real Main eq_srl)
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨ sop_1, sop_2, sop_3, sop_4 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set msb_b := Main[36]
    set msb_srw := Main[37]
    set cb0 := Main[38]
    set cb1 := Main[39]
    set cb2 := Main[40]
    set cb3 := Main[41]
    set cb4 := Main[42]
    set cb5 := Main[43]
    set smv := Main[44]
    set v0123 := Main[45]
    set v012 := Main[46]
    set v01 := Main[47]
    set ll0 := Main[48]
    set ll1 := Main[49]
    set ll2 := Main[50]
    set ll3 := Main[51]
    set hl0 := Main[52]
    set hl1 := Main[53]
    set hl2 := Main[54]
    set hl3 := Main[55]
    set lr0 := Main[56]
    set lr1 := Main[57]
    set lr2 := Main[58]
    set lr3 := Main[59]
    set su160 := Main[60]
    set su161 := Main[61]
    set su162 := Main[62]
    set su163 := Main[63]
    set srl := Main[64]
    set sra := Main[65]
    set srlw := Main[66]
    set sraw := Main[67]
    set bop := Main[68]

    obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
             b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             w_msb_b, eq_smv, w_msb_srv,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05 ⟩ := cstrs
    clear h_msb_b3 h_msb_b1 h_msb_a1 cpu alu

    simp_all

    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

    have : ((Word.toBitVec64 #v[c0, c1, c2, c3]).toNat % 64) = c0.val % 64 := by
      rw [Word.toBitVec64_toNat is_U64_c]; simp [Word.toNat]
      omega
    rw [this]; clear this
    have : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . omega
      . exact diff
    clear diff

    rw [this]; clear this
    rw [Word.toBitVec64_toNat is_U64_a, Word.toBitVec64_toNat is_U64_b]
    simp [Word.toNat]

    -- 64-way case split
    rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
    rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
    simp_all <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b0_dec) <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b1_dec) <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b2_dec) <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b3_dec) <;>
    simp_all

    all_goals {
      try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
      repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      try omega
    }

end srl

section srli

lemma spec.srli (h : is_srli Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRL
  := by
    intro cstrs
    obtain ⟨ eq_srl, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (srl_real Main eq_srl)
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    have immediate_bounds := immediate_bounds Main cstrs (srl_real Main eq_srl)
    rw [eq_imm] at immediate_bounds; simp_all
    obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3, lt_c0, h0 ⟩ := immediate_bounds
    obtain ⟨ sop_1, sop_2, sop_3, sop_4 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set msb_b := Main[36]
    set msb_srw := Main[37]
    set cb0 := Main[38]
    set cb1 := Main[39]
    set cb2 := Main[40]
    set cb3 := Main[41]
    set cb4 := Main[42]
    set cb5 := Main[43]
    set smv := Main[44]
    set v0123 := Main[45]
    set v012 := Main[46]
    set v01 := Main[47]
    set ll0 := Main[48]
    set ll1 := Main[49]
    set ll2 := Main[50]
    set ll3 := Main[51]
    set hl0 := Main[52]
    set hl1 := Main[53]
    set hl2 := Main[54]
    set hl3 := Main[55]
    set lr0 := Main[56]
    set lr1 := Main[57]
    set lr2 := Main[58]
    set lr3 := Main[59]
    set su160 := Main[60]
    set su161 := Main[61]
    set su162 := Main[62]
    set su163 := Main[63]
    set srl := Main[64]
    set sra := Main[65]
    set srlw := Main[66]
    set sraw := Main[67]
    set bop := Main[68]

    obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
             b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             w_msb_b, eq_smv, w_msb_srv,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05 ⟩ := cstrs
    clear h_msb_b3 h_msb_b1 h_msb_a1 cpu alu

    simp_all

    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

    have : ((Word.toBitVec64 #v[c0, 0, 0, 0]).toNat % 64) = c0.val % 64 := by
      rw [Word.toBitVec64_toNat is_U64_c]; simp [Word.toNat]
    rw [this]; clear this
    have : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . omega
      . exact diff

    rw [this]; clear this
    rw [Word.toBitVec64_toNat is_U64_a, Word.toBitVec64_toNat is_U64_b]
    simp [Word.toNat]

    -- 64-way case split
    rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
    rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
    simp_all <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b0_dec) <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b1_dec) <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b2_dec) <;>
    (try apply cancel_mul_65536_v1 (by simp) at h_b3_dec) <;>
    simp_all

    all_goals {
      try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
      repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      try omega
    }

end srli

section srlw

lemma spec.srlw (h : is_srlw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRLW
  := by
    intro cstrs
    obtain ⟨ eq_srlw, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (srlw_real Main eq_srlw)
    obtain ⟨ a0_16, a1_16, a2_16, a3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_a
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨ sop_1, sop_2, sop_3, sop_4 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set msb_b := Main[36]
    set msb_srw := Main[37]
    set cb0 := Main[38]
    set cb1 := Main[39]
    set cb2 := Main[40]
    set cb3 := Main[41]
    set cb4 := Main[42]
    set cb5 := Main[43]
    set smv := Main[44]
    set v0123 := Main[45]
    set v012 := Main[46]
    set v01 := Main[47]
    set ll0 := Main[48]
    set ll1 := Main[49]
    set ll2 := Main[50]
    set ll3 := Main[51]
    set hl0 := Main[52]
    set hl1 := Main[53]
    set hl2 := Main[54]
    set hl3 := Main[55]
    set lr0 := Main[56]
    set lr1 := Main[57]
    set lr2 := Main[58]
    set lr3 := Main[59]
    set su160 := Main[60]
    set su161 := Main[61]
    set su162 := Main[62]
    set su163 := Main[63]
    set srl := Main[64]
    set sra := Main[65]
    set srlw := Main[66]
    set sraw := Main[67]
    set bop := Main[68]

    obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
             b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             w_msb_b, eq_smv, w_msb_srv,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05 ⟩ := cstrs
    clear h_msb_b3 h_msb_b1 cpu alu

    symm at h_b2_dec h_b3_dec
    simp_all

    have is_U32_a : HalfWord.isU32 #v[ a0, a1 ] := by apply HalfWord.isU32_of_cases <;> assumption
    have is_U32_b : HalfWord.isU32 #v[ b0, b1 ] := by apply HalfWord.isU32_of_cases <;> assumption
    have is_U32_c : HalfWord.isU32 #v[ c0, c1 ] := by apply HalfWord.isU32_of_cases <;> assumption

    have ⟨ eq_hl2, eq_ll2 ⟩ : hl2 = 0 ∧ ll2 = 0 := by
      clear *- lt_hl2 lt_ll2 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
      apply (cancel_mul_65536_v2 (by simp)) at h_b2_dec <;>
      simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b2_dec <;>
      rw [Nat.mod_eq_of_lt (by omega)] at h_b2_dec <;>
      split_ands <;> omega

    have ⟨ eq_hl3, eq_ll3 ⟩ : hl3 = 0 ∧ ll3 = 0 := by
      clear *- lt_hl3 lt_ll3 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
      apply (cancel_mul_65536_v2 (by simp)) at h_b3_dec <;>
      simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b3_dec <;>
      rw [Nat.mod_eq_of_lt (by omega)] at h_b3_dec <;>
      split_ands <;> omega

    simp [eq_hl2, eq_ll2, eq_hl3, eq_ll3] at *
    simp_all

    have : ((Word.low32 #v[c0, c1, c2, c3]).toBitVec32.toNat % 32) = c0.val % 32 := by
      simp [Word.low32, HalfWord.toBitVec32_toNat is_U32_c, HalfWord.toNat];
      omega
    rw [this]; clear this
    simp [Word.low32]

    have c0_mod_64 : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . omega
      . exact diff
    clear diff

    have : c0.val % 32 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
      trans (c0.val % 64) % 32
      . omega
      . rw [c0_mod_64]
        clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
    clear c0_mod_64

    have h_a3 : a3 = if (HalfWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      have h_msb := U16MSBOperation.spec a1 { msb := msb_srw } 1 (by assumption) h_msb_a1 (by simp)
      simp at h_msb; rw [h_msb]
      trans (if HalfWord.isNegative #v[a0, a1] then 65535 else 0)
      . unfold HalfWord.isNegative; split_ifs <;> simp_all; omega
      . congr; rw [HalfWord.isNegative_msb _ is_U32_a]

    . suffices hw_shift : HalfWord.toBitVec32 #v[ a0, a1 ] = (HalfWord.toBitVec32 #v[b0, b1] >>> (c0.val % 32))
      . rw [← hw_shift]
        rw [HalfWord.sign_extend_32_to_64_msb]
        simp_all; congr
      . rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        rw [HalfWord.toBitVec32_toNat is_U32_a, HalfWord.toBitVec32_toNat is_U32_b]
        rw [this]; clear this h_a3

        cases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
        rcases b_cb3 <;> rcases b_cb4 <;> simp_all

        all_goals {
          (try apply cancel_mul_65536_v1 (by simp) at h_b0_dec)
          (try apply cancel_mul_65536_v1 (by simp) at h_b1_dec)
          simp_all [HalfWord.toNat]
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          omega
        }

end srlw

section srliw

lemma spec.srliw (h : is_srliw Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRLW
  := by
    intro cstrs
    obtain ⟨ eq_srlw, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (srlw_real Main eq_srlw)
    obtain ⟨ a0_16, a1_16, a2_16, a3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_a
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
    have immediate_bounds := immediate_bounds Main cstrs (srlw_real Main eq_srlw)
    rw [eq_imm] at immediate_bounds; simp_all
    obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3, lt_c0, h0 ⟩ := immediate_bounds
    obtain ⟨ sop_1, sop_2, sop_3, sop_4 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set msb_b := Main[36]
    set msb_srw := Main[37]
    set cb0 := Main[38]
    set cb1 := Main[39]
    set cb2 := Main[40]
    set cb3 := Main[41]
    set cb4 := Main[42]
    set cb5 := Main[43]
    set smv := Main[44]
    set v0123 := Main[45]
    set v012 := Main[46]
    set v01 := Main[47]
    set ll0 := Main[48]
    set ll1 := Main[49]
    set ll2 := Main[50]
    set ll3 := Main[51]
    set hl0 := Main[52]
    set hl1 := Main[53]
    set hl2 := Main[54]
    set hl3 := Main[55]
    set lr0 := Main[56]
    set lr1 := Main[57]
    set lr2 := Main[58]
    set lr3 := Main[59]
    set su160 := Main[60]
    set su161 := Main[61]
    set su162 := Main[62]
    set su163 := Main[63]
    set srl := Main[64]
    set sra := Main[65]
    set srlw := Main[66]
    set sraw := Main[67]
    set bop := Main[68]

    obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
             b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             w_msb_b, eq_smv, w_msb_srv,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05 ⟩ := cstrs
    clear h_msb_b3 h_msb_b1 cpu alu

    symm at h_b2_dec h_b3_dec
    simp_all

    have is_U32_a : HalfWord.isU32 #v[ a0, a1 ] := by apply HalfWord.isU32_of_cases <;> assumption
    have is_U32_b : HalfWord.isU32 #v[ b0, b1 ] := by apply HalfWord.isU32_of_cases <;> assumption
    have is_U32_c : HalfWord.isU32 #v[ c0, 0 ] := by apply HalfWord.isU32_of_cases <;> simp; omega

    have ⟨ eq_hl2, eq_ll2 ⟩ : hl2 = 0 ∧ ll2 = 0 := by
      clear *- lt_hl2 lt_ll2 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
      apply (cancel_mul_65536_v2 (by simp)) at h_b2_dec <;>
      simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b2_dec <;>
      rw [Nat.mod_eq_of_lt (by omega)] at h_b2_dec <;>
      split_ands <;> omega

    have ⟨ eq_hl3, eq_ll3 ⟩ : hl3 = 0 ∧ ll3 = 0 := by
      clear *- lt_hl3 lt_ll3 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
      apply (cancel_mul_65536_v2 (by simp)) at h_b3_dec <;>
      simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b3_dec <;>
      rw [Nat.mod_eq_of_lt (by omega)] at h_b3_dec <;>
      split_ands <;> omega

    simp [eq_hl2, eq_ll2, eq_hl3, eq_ll3] at *
    simp_all

    have : ((Word.low32 #v[c0, 0, 0, 0]).toBitVec32.toNat % 32) = c0.val % 32 := by
      simp [Word.low32, HalfWord.toBitVec32_toNat is_U32_c, HalfWord.toNat]
    rw [this]; clear this
    simp [Word.low32]

    have c0_mod_64 : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . omega
      . exact diff
    clear diff

    have : c0.val % 32 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
      trans (c0.val % 64) % 32
      . omega
      . rw [c0_mod_64]
        clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
    clear c0_mod_64

    have h_a3 : a3 = if (HalfWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      have h_msb := U16MSBOperation.spec a1 { msb := msb_srw } 1 (by assumption) h_msb_a1 (by simp)
      simp at h_msb; rw [h_msb]
      trans (if HalfWord.isNegative #v[a0, a1] then 65535 else 0)
      . unfold HalfWord.isNegative; split_ifs <;> simp_all; omega
      . congr; rw [HalfWord.isNegative_msb _ is_U32_a]

    . suffices hw_shift : HalfWord.toBitVec32 #v[ a0, a1 ] = (HalfWord.toBitVec32 #v[b0, b1] >>> (c0.val % 32))
      . rw [← hw_shift]
        rw [HalfWord.sign_extend_32_to_64_msb]
        simp_all; congr
      . rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        rw [HalfWord.toBitVec32_toNat is_U32_a, HalfWord.toBitVec32_toNat is_U32_b]
        rw [this]; clear this h_a3

        cases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
        rcases b_cb3 <;> rcases b_cb4 <;> simp_all

        all_goals {
          (try apply cancel_mul_65536_v1 (by simp) at h_b0_dec)
          (try apply cancel_mul_65536_v1 (by simp) at h_b1_dec)
          simp_all [HalfWord.toNat]
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          omega
        }

end srliw

section sra

lemma spec.sra (h : is_sra Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRA
  := by
    intro cstrs
    obtain ⟨ eq_sra, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (sra_real Main eq_sra)
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨ sop_1, sop_2, sop_3, sop_4 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set msb_b := Main[36]
    set msb_srw := Main[37]
    set cb0 := Main[38]
    set cb1 := Main[39]
    set cb2 := Main[40]
    set cb3 := Main[41]
    set cb4 := Main[42]
    set cb5 := Main[43]
    set smv := Main[44]
    set v0123 := Main[45]
    set v012 := Main[46]
    set v01 := Main[47]
    set ll0 := Main[48]
    set ll1 := Main[49]
    set ll2 := Main[50]
    set ll3 := Main[51]
    set hl0 := Main[52]
    set hl1 := Main[53]
    set hl2 := Main[54]
    set hl3 := Main[55]
    set lr0 := Main[56]
    set lr1 := Main[57]
    set lr2 := Main[58]
    set lr3 := Main[59]
    set su160 := Main[60]
    set su161 := Main[61]
    set su162 := Main[62]
    set su163 := Main[63]
    set srl := Main[64]
    set sra := Main[65]
    set srlw := Main[66]
    set sraw := Main[67]
    set bop := Main[68]

    obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
             b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             w_msb_b, eq_smv, w_msb_srv,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05 ⟩ := cstrs
    clear h_msb_b1 h_msb_a1 cpu alu

    simp_all

    rw [← BitVec.toInt_inj, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]

    have : ((Word.toBitVec64 #v[c0, c1, c2, c3]).toNat % 64) = c0.val % 64 := by
      rw [Word.toBitVec64_toNat is_U64_c]; simp [Word.toNat]
      omega
    rw [this]; clear this
    have : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . omega
      . exact diff
    clear diff

    rw [this]; clear this
    rw [Word.toBitVec64_toInt (w := #v[a0, a1, a2, a3]) is_U64_a]
    rw [Word.toBitVec64_toInt (w := #v[b0, b1, b2, b3]) is_U64_b]

    have msb_b3_spec := U16MSBOperation.spec _ _ _ b3_16 h_msb_b3 (by simp)
    simp at msb_b3_spec

    have b_msb : msb_b = 0 ∨ msb_b = 1 := by
      clear *- msb_b3_spec
      split_ifs at msb_b3_spec <;> simp_all

    have b_msb_iff_neg_b : Word.isNegative #v[b0, b1, b2, b3] ↔ msb_b = 1 := by rw [msb_b3_spec, Word.isNegative]; aesop

    have b_msb_iff_neg_a : Word.isNegative #v[a0, a1, a2, a3] ↔ msb_b = 1 := by
      simp [msb_b3_spec, Word.isNegative]
      rcases b_su163 with h_su163 | h_su163 <;> simp_all
      . rcases b_su162 with h_su162 | h_su162 <;> simp_all
        . rcases b_su161 with h_su161 | h_su161 <;> simp_all
          . have ⟨ h_cb4, h_cb5 ⟩ : cb4 = 0 ∧ cb5 = 0 := by clear *- b_cb4 b_cb5 h_su160; aesop
            simp_all
            clear *- b3_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec lt_hl3 lt_ll3
            rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;>
            split_ifs <;> simp_all <;>
            (try apply cancel_mul_65536_v1 (by simp) at h_b3_dec) <;>
            omega
          . clear *-; split_ifs <;> omega
        . clear *-; split_ifs <;> omega
      . clear *-; split_ifs <;> omega

    by_cases h_neg : 32768 ≤ b3 <;> simp_all

    all_goals
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
      rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
      simp_all

    all_goals {
      try apply cancel_mul_65536_v1 (by simp) at h_b0_dec
      try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
      try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
      try apply cancel_mul_65536_v1 (by simp) at h_b3_dec
      simp_all
      iterate 2 rw [Word.toInt]
      try rw [if_pos b_msb_iff_neg_a, if_pos b_msb_iff_neg_b]
      try rw [if_neg b_msb_iff_neg_a, if_neg b_msb_iff_neg_b]
      iterate 2 rw [Word.toNat]
      iterate 8 rw [Vector.getElem_mk]
      simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
      clear *- lt_ll0 lt_hl0 lt_ll1 lt_hl1 lt_ll2 lt_hl2 lt_ll3 lt_hl3
      try simp only [Fin.add_def, Fin.mul_def]
      repeat rw [Nat.mod_eq_of_lt (a := _ * _) (b := 2013265921) (by omega)]
      repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      simp_all
      omega
    }

end sra

section srai

lemma spec.srai (h : is_srai Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRA
  := by
    intro cstrs
    obtain ⟨ eq_sra, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (sra_real Main eq_sra)
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
    have immediate_bounds := immediate_bounds Main cstrs (sra_real Main eq_sra)
    rw [eq_imm] at immediate_bounds; simp_all
    obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3, lt_c0, h0 ⟩ := immediate_bounds
    obtain ⟨ sop_1, sop_2, sop_3, sop_4 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set msb_b := Main[36]
    set msb_srw := Main[37]
    set cb0 := Main[38]
    set cb1 := Main[39]
    set cb2 := Main[40]
    set cb3 := Main[41]
    set cb4 := Main[42]
    set cb5 := Main[43]
    set smv := Main[44]
    set v0123 := Main[45]
    set v012 := Main[46]
    set v01 := Main[47]
    set ll0 := Main[48]
    set ll1 := Main[49]
    set ll2 := Main[50]
    set ll3 := Main[51]
    set hl0 := Main[52]
    set hl1 := Main[53]
    set hl2 := Main[54]
    set hl3 := Main[55]
    set lr0 := Main[56]
    set lr1 := Main[57]
    set lr2 := Main[58]
    set lr3 := Main[59]
    set su160 := Main[60]
    set su161 := Main[61]
    set su162 := Main[62]
    set su163 := Main[63]
    set srl := Main[64]
    set sra := Main[65]
    set srlw := Main[66]
    set sraw := Main[67]
    set bop := Main[68]

    obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
             b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             w_msb_b, eq_smv, w_msb_srv,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05 ⟩ := cstrs
    clear h_msb_b1 h_msb_a1 cpu alu

    simp_all

    rw [← BitVec.toInt_inj, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]

    have : ((Word.toBitVec64 #v[c0, 0, 0, 0]).toNat % 64) = c0.val % 64 := by
      rw [Word.toBitVec64_toNat is_U64_c]; simp [Word.toNat]
    rw [this]; clear this
    have : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . omega
      . exact diff
    clear diff

    rw [this]; clear this
    rw [Word.toBitVec64_toInt (w := #v[a0, a1, a2, a3]) is_U64_a]
    rw [Word.toBitVec64_toInt (w := #v[b0, b1, b2, b3]) is_U64_b]

    have msb_b3_spec := U16MSBOperation.spec _ _ _ b3_16 h_msb_b3 (by simp)
    simp at msb_b3_spec

    have b_msb : msb_b = 0 ∨ msb_b = 1 := by
      clear *- msb_b3_spec
      split_ifs at msb_b3_spec <;> simp_all

    have b_msb_iff_neg_b : Word.isNegative #v[b0, b1, b2, b3] ↔ msb_b = 1 := by rw [msb_b3_spec, Word.isNegative]; aesop

    have b_msb_iff_neg_a : Word.isNegative #v[a0, a1, a2, a3] ↔ msb_b = 1 := by
      simp [msb_b3_spec, Word.isNegative]
      rcases b_su163 with h_su163 | h_su163 <;> simp_all
      . rcases b_su162 with h_su162 | h_su162 <;> simp_all
        . rcases b_su161 with h_su161 | h_su161 <;> simp_all
          . have ⟨ h_cb4, h_cb5 ⟩ : cb4 = 0 ∧ cb5 = 0 := by clear *- b_cb4 b_cb5 h_su160; aesop
            simp_all
            clear *- b3_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec lt_hl3 lt_ll3
            rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;>
            split_ifs <;> simp_all <;>
            (try apply cancel_mul_65536_v1 (by simp) at h_b3_dec) <;>
            omega
          . clear *-; split_ifs <;> omega
        . clear *-; split_ifs <;> omega
      . clear *-; split_ifs <;> omega

    by_cases h_neg : 32768 ≤ b3 <;> simp_all

    all_goals
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
      rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
      simp_all

    all_goals {
      try apply cancel_mul_65536_v1 (by simp) at h_b0_dec
      try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
      try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
      try apply cancel_mul_65536_v1 (by simp) at h_b3_dec
      simp_all
      iterate 2 rw [Word.toInt]
      try rw [if_pos b_msb_iff_neg_a, if_pos b_msb_iff_neg_b]
      try rw [if_neg b_msb_iff_neg_a, if_neg b_msb_iff_neg_b]
      iterate 2 rw [Word.toNat]
      iterate 8 rw [Vector.getElem_mk]
      simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
      clear *- lt_ll0 lt_hl0 lt_ll1 lt_hl1 lt_ll2 lt_hl2 lt_ll3 lt_hl3
      try simp only [Fin.add_def, Fin.mul_def]
      repeat rw [Nat.mod_eq_of_lt (a := _ * _) (b := 2013265921) (by omega)]
      repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      simp_all
      omega
    }

end srai

section sraw

lemma spec.sraw (h : is_sraw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRAW
  := by
    intro cstrs
    obtain ⟨ eq_sraw, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (sraw_real Main eq_sraw)
    obtain ⟨ a0_16, a1_16, a2_16, a3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_a
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨ sop_1, sop_2, sop_3, sop_4 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set msb_b := Main[36]
    set msb_srw := Main[37]
    set cb0 := Main[38]
    set cb1 := Main[39]
    set cb2 := Main[40]
    set cb3 := Main[41]
    set cb4 := Main[42]
    set cb5 := Main[43]
    set smv := Main[44]
    set v0123 := Main[45]
    set v012 := Main[46]
    set v01 := Main[47]
    set ll0 := Main[48]
    set ll1 := Main[49]
    set ll2 := Main[50]
    set ll3 := Main[51]
    set hl0 := Main[52]
    set hl1 := Main[53]
    set hl2 := Main[54]
    set hl3 := Main[55]
    set lr0 := Main[56]
    set lr1 := Main[57]
    set lr2 := Main[58]
    set lr3 := Main[59]
    set su160 := Main[60]
    set su161 := Main[61]
    set su162 := Main[62]
    set su163 := Main[63]
    set srl := Main[64]
    set sra := Main[65]
    set srlw := Main[66]
    set sraw := Main[67]
    set bop := Main[68]

    obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
             b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             w_msb_b, eq_smv, w_msb_srv,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05 ⟩ := cstrs
    clear h_msb_b3 cpu alu

    symm at h_b2_dec h_b3_dec
    simp_all

    have is_U32_a : HalfWord.isU32 #v[ a0, a1 ] := by apply HalfWord.isU32_of_cases <;> assumption
    have is_U32_b : HalfWord.isU32 #v[ b0, b1 ] := by apply HalfWord.isU32_of_cases <;> assumption
    have is_U32_c : HalfWord.isU32 #v[ c0, c1 ] := by apply HalfWord.isU32_of_cases <;> assumption

    have ⟨ eq_hl2, eq_ll2 ⟩ : hl2 = 0 ∧ ll2 = 0 := by
      clear *- lt_hl2 lt_ll2 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
      apply (cancel_mul_65536_v2 (by simp)) at h_b2_dec <;>
      simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b2_dec <;>
      rw [Nat.mod_eq_of_lt (by omega)] at h_b2_dec <;>
      split_ands <;> omega

    have ⟨ eq_hl3, eq_ll3 ⟩ : hl3 = 0 ∧ ll3 = 0 := by
      clear *- lt_hl3 lt_ll3 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
      apply (cancel_mul_65536_v2 (by simp)) at h_b3_dec <;>
      simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b3_dec <;>
      rw [Nat.mod_eq_of_lt (by omega)] at h_b3_dec <;>
      split_ands <;> omega

    simp [eq_hl2, eq_ll2, eq_hl3, eq_ll3] at *
    simp_all

    have : ((Word.low32 #v[c0, c1, c2, c3]).toBitVec32.toNat % 32) = c0.val % 32 := by
      simp [Word.low32, HalfWord.toBitVec32_toNat is_U32_c, HalfWord.toNat];
      omega
    rw [this]; clear this
    simp [Word.low32]

    have c0_mod_64 : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . omega
      . exact diff
    clear diff

    have : c0.val % 32 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
      trans (c0.val % 64) % 32
      . omega
      . rw [c0_mod_64]
        clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
    clear c0_mod_64

    have h_a3 : a3 = if (HalfWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      have h_msb := U16MSBOperation.spec a1 { msb := msb_srw } 1 (by assumption) h_msb_a1 (by simp)
      simp at h_msb; rw [h_msb]
      trans (if HalfWord.isNegative #v[a0, a1] then 65535 else 0)
      . unfold HalfWord.isNegative; split_ifs <;> simp_all; omega
      . congr; rw [HalfWord.isNegative_msb _ is_U32_a]

    . suffices hw_shift : HalfWord.toBitVec32 #v[ a0, a1 ] = BitVec.sshiftRight (HalfWord.toBitVec32 #v[b0, b1]) (c0.val % 32)
      . rw [← hw_shift]
        rw [HalfWord.sign_extend_32_to_64_msb]
        simp_all; congr
      . rw [this]; clear this h_a3
        rw [← BitVec.toInt_inj, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
        rw [HalfWord.toBitVec32_toInt (w := #v[a0, a1]) is_U32_a]
        rw [HalfWord.toBitVec32_toInt (w := #v[b0, b1]) is_U32_b]

        have msb_b1_spec := U16MSBOperation.spec _ _ _ b1_16 h_msb_b1 (by simp)
        simp at msb_b1_spec

        have b_msb : msb_b = 0 ∨ msb_b = 1 := by
          clear *- msb_b1_spec
          split_ifs at msb_b1_spec <;> simp_all

        have b_msb_iff_neg_b : HalfWord.isNegative #v[b0, b1] ↔ msb_b = 1 := by rw [msb_b1_spec, HalfWord.isNegative]; aesop

        have b_msb_iff_neg_a : HalfWord.isNegative #v[a0, a1] ↔ msb_b = 1 := by
          simp [msb_b1_spec, HalfWord.isNegative]
          obtain ⟨ h_su162, h_su163 ⟩ : su162 = 0 ∧ su163 = 0 := by clear *- b_cb4 h_su162 h_su163; aesop
          simp_all
          . rcases b_su161 with h_su161 | h_su161
            all_goals {
              simp_all
              clear *- b3_16 h_b1_dec b_cb0 b_cb1 b_cb2 b_cb3 lt_hl1 lt_ll1
              by_cases h_if : b1 < 32768 <;>
              rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;>
              split_ifs <;> simp_all <;>
              (try apply cancel_mul_65536_v1 (by simp) at h_b1_dec) <;>
              omega
            }

        by_cases h_neg : 32768 ≤ b1 <;> simp_all

        all_goals
          rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
          rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
          simp_all

        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b0_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          simp_all
          iterate 2 rw [HalfWord.toInt]
          try rw [if_pos b_msb_iff_neg_a, if_pos b_msb_iff_neg_b]
          try rw [if_neg b_msb_iff_neg_a, if_neg b_msb_iff_neg_b]
          iterate 2 rw [HalfWord.toNat]
          iterate 4 rw [Vector.getElem_mk]
          simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
          clear *- lt_ll0 lt_hl0 lt_ll1 lt_hl1
          try simp only [Fin.add_def, Fin.mul_def]
          repeat rw [Nat.mod_eq_of_lt (a := _ * _) (b := 2013265921) (by omega)]
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          simp_all
          omega
        }

end sraw

section sraiw

lemma spec.sraiw (h : is_sraiw Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRAW
  := by
    intro cstrs
    obtain ⟨ eq_sraw, eq_imm ⟩ := h
    have ⟨ is_U64_a, is_U64_b, is_U64_c ⟩ := ops_U64 Main cstrs (sraw_real Main eq_sraw)
    obtain ⟨ a0_16, a1_16, a2_16, a3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_a
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
    have immediate_bounds := immediate_bounds Main cstrs (sraw_real Main eq_sraw)
    rw [eq_imm] at immediate_bounds; simp_all
    obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3, lt_c0, h0 ⟩ := immediate_bounds
    obtain ⟨ sop_1, sop_2, sop_3, sop_4 ⟩ := single_op Main cstrs

    simp [allHold_constraints_iff] at cstrs

    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set msb_b := Main[36]
    set msb_srw := Main[37]
    set cb0 := Main[38]
    set cb1 := Main[39]
    set cb2 := Main[40]
    set cb3 := Main[41]
    set cb4 := Main[42]
    set cb5 := Main[43]
    set smv := Main[44]
    set v0123 := Main[45]
    set v012 := Main[46]
    set v01 := Main[47]
    set ll0 := Main[48]
    set ll1 := Main[49]
    set ll2 := Main[50]
    set ll3 := Main[51]
    set hl0 := Main[52]
    set hl1 := Main[53]
    set hl2 := Main[54]
    set hl3 := Main[55]
    set lr0 := Main[56]
    set lr1 := Main[57]
    set lr2 := Main[58]
    set lr3 := Main[59]
    set su160 := Main[60]
    set su161 := Main[61]
    set su162 := Main[62]
    set su163 := Main[63]
    set srl := Main[64]
    set sra := Main[65]
    set srlw := Main[66]
    set sraw := Main[67]
    set bop := Main[68]

    obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
             b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             w_msb_b, eq_smv, w_msb_srv,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05 ⟩ := cstrs
    clear h_msb_b3 cpu alu

    symm at h_b2_dec h_b3_dec
    simp_all

    have is_U32_a : HalfWord.isU32 #v[ a0, a1 ] := by apply HalfWord.isU32_of_cases <;> assumption
    have is_U32_b : HalfWord.isU32 #v[ b0, b1 ] := by apply HalfWord.isU32_of_cases <;> assumption
    have is_U32_c : HalfWord.isU32 #v[ c0, 0 ] := by apply HalfWord.isU32_of_cases <;> [ assumption; simp ]

    have ⟨ eq_hl2, eq_ll2 ⟩ : hl2 = 0 ∧ ll2 = 0 := by
      clear *- lt_hl2 lt_ll2 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
      apply (cancel_mul_65536_v2 (by simp)) at h_b2_dec <;>
      simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b2_dec <;>
      rw [Nat.mod_eq_of_lt (by omega)] at h_b2_dec <;>
      split_ands <;> omega

    have ⟨ eq_hl3, eq_ll3 ⟩ : hl3 = 0 ∧ ll3 = 0 := by
      clear *- lt_hl3 lt_ll3 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
      apply (cancel_mul_65536_v2 (by simp)) at h_b3_dec <;>
      simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b3_dec <;>
      rw [Nat.mod_eq_of_lt (by omega)] at h_b3_dec <;>
      split_ands <;> omega

    simp [eq_hl2, eq_ll2, eq_hl3, eq_ll3] at *
    simp_all

    have : ((Word.low32 #v[c0, 0, 0, 0]).toBitVec32.toNat % 32) = c0.val % 32 := by
      simp [Word.low32, HalfWord.toBitVec32_toNat is_U32_c, HalfWord.toNat]
    rw [this]; clear this
    simp [Word.low32]

    have c0_mod_64 : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      . omega
      . exact diff
    clear diff

    have : c0.val % 32 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
      trans (c0.val % 64) % 32
      . omega
      . rw [c0_mod_64]
        clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
    clear c0_mod_64

    have h_a3 : a3 = if (HalfWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      have h_msb := U16MSBOperation.spec a1 { msb := msb_srw } 1 (by assumption) h_msb_a1 (by simp)
      simp at h_msb; rw [h_msb]
      trans (if HalfWord.isNegative #v[a0, a1] then 65535 else 0)
      . unfold HalfWord.isNegative; split_ifs <;> simp_all; omega
      . congr; rw [HalfWord.isNegative_msb _ is_U32_a]

    . suffices hw_shift : HalfWord.toBitVec32 #v[ a0, a1 ] = BitVec.sshiftRight (HalfWord.toBitVec32 #v[b0, b1]) (c0.val % 32)
      . rw [← hw_shift]
        rw [HalfWord.sign_extend_32_to_64_msb]
        simp_all; congr
      . rw [this]; clear this h_a3
        rw [← BitVec.toInt_inj, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
        rw [HalfWord.toBitVec32_toInt (w := #v[a0, a1]) is_U32_a]
        rw [HalfWord.toBitVec32_toInt (w := #v[b0, b1]) is_U32_b]

        have msb_b1_spec := U16MSBOperation.spec _ _ _ b1_16 h_msb_b1 (by simp)
        simp at msb_b1_spec

        have b_msb : msb_b = 0 ∨ msb_b = 1 := by
          clear *- msb_b1_spec
          split_ifs at msb_b1_spec <;> simp_all

        have b_msb_iff_neg_b : HalfWord.isNegative #v[b0, b1] ↔ msb_b = 1 := by rw [msb_b1_spec, HalfWord.isNegative]; aesop

        have b_msb_iff_neg_a : HalfWord.isNegative #v[a0, a1] ↔ msb_b = 1 := by
          simp [msb_b1_spec, HalfWord.isNegative]
          obtain ⟨ h_su162, h_su163 ⟩ : su162 = 0 ∧ su163 = 0 := by clear *- b_cb4 h_su162 h_su163; aesop
          simp_all
          . rcases b_su161 with h_su161 | h_su161
            all_goals {
              simp_all
              clear *- b3_16 h_b1_dec b_cb0 b_cb1 b_cb2 b_cb3 lt_hl1 lt_ll1
              by_cases h_if : b1 < 32768 <;>
              rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;>
              split_ifs <;> simp_all <;>
              (try apply cancel_mul_65536_v1 (by simp) at h_b1_dec) <;>
              omega
            }

        by_cases h_neg : 32768 ≤ b1 <;> simp_all

        all_goals
          rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
          rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
          simp_all

        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b0_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          simp_all
          iterate 2 rw [HalfWord.toInt]
          try rw [if_pos b_msb_iff_neg_a, if_pos b_msb_iff_neg_b]
          try rw [if_neg b_msb_iff_neg_a, if_neg b_msb_iff_neg_b]
          iterate 2 rw [HalfWord.toNat]
          iterate 4 rw [Vector.getElem_mk]
          simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
          clear *- lt_ll0 lt_hl0 lt_ll1 lt_hl1
          try simp only [Fin.add_def, Fin.mul_def]
          repeat rw [Nat.mod_eq_of_lt (a := _ * _) (b := 2013265921) (by omega)]
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          simp_all
          omega
        }

end sraiw

end ShiftRight
