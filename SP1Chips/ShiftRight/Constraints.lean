import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace ShiftRight

set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 70)
def is_real : Prop := Main[65] = 1 ∨ Main[66] = 1 ∨ Main[67] = 1 ∨ Main[68] = 1

section constraints

-- Generated Lean code for chip ShiftRightChip
@[irreducible] def constraints (Main : Vector (Fin KB) 70) : SP1ConstraintList :=
  let E0 : Fin KB := Main[65] + Main[66]
  let E1 : Fin KB := E0 + Main[67]
  let E2 : Fin KB := E1 + Main[68]
  let E3 : Fin KB := Main[65] - 1
  let E4 : Fin KB := Main[65] * E3
  let E5 : Fin KB := Main[66] - 1
  let E6 : Fin KB := Main[66] * E5
  let E7 : Fin KB := Main[67] - 1
  let E8 : Fin KB := Main[67] * E7
  let E9 : Fin KB := Main[68] - 1
  let E10 : Fin KB := Main[68] * E9
  let E11 : Fin KB := E2 - 1
  let E12 : Fin KB := E2 * E11
  let E13 : Fin KB := Main[67] + Main[68]
  let E14 : Fin KB := Main[65] + Main[66]
  let E15 : Fin KB := Main[65] * 7
  let E16 : Fin KB := Main[66] * 8
  let E17 : Fin KB := E15 + E16
  let E18 : Fin KB := Main[67] * 42
  let E19 : Fin KB := E17 + E18
  let E20 : Fin KB := Main[68] * 43
  let E21 : Fin KB := E19 + E20
  let E22 : Fin KB := Main[65] * 5
  let E23 : Fin KB := Main[66] * 5
  let E24 : Fin KB := E22 + E23
  let E25 : Fin KB := Main[67] * 5
  let E26 : Fin KB := E24 + E25
  let E27 : Fin KB := Main[68] * 5
  let E28 : Fin KB := E26 + E27
  let E29 : Fin KB := Main[65] * 0
  let E30 : Fin KB := Main[66] * 32
  let E31 : Fin KB := E29 + E30
  let E32 : Fin KB := Main[67] * 0
  let E33 : Fin KB := E31 + E32
  let E34 : Fin KB := Main[68] * 32
  let E35 : Fin KB := E33 + E34
  let E36 : Fin KB := Main[65] * 51
  let E37 : Fin KB := Main[66] * 51
  let E38 : Fin KB := E36 + E37
  let E39 : Fin KB := Main[67] * 59
  let E40 : Fin KB := E38 + E39
  let E41 : Fin KB := Main[68] * 59
  let E42 : Fin KB := E40 + E41
  let E43 : Fin KB := 32 * Main[31]
  let E44 : Fin KB := E42 - E43
  let E45 : Fin KB := Main[67] + Main[68]
  let E46 : Fin KB := E45 * Main[31]
  let E47 : Fin KB := Main[69] - E46
  let E48 : Fin KB := Main[65] * 8
  let E49 : Fin KB := Main[66] * 8
  let E50 : Fin KB := E48 + E49
  let E51 : Fin KB := Main[67] * 8
  let E52 : Fin KB := E50 + E51
  let E53 : Fin KB := Main[68] * 8
  let E54 : Fin KB := E52 + E53
  let E55 : Fin KB := 6 * Main[31]
  let E56 : Fin KB := 1 * Main[69]
  let E57 : Fin KB := E55 + E56
  let E58 : Fin KB := E54 - E57
  let E59 : Fin KB := Main[39] - 1
  let E60 : Fin KB := Main[39] * E59
  let E61 : Fin KB := Main[40] - 1
  let E62 : Fin KB := Main[40] * E61
  let E63 : Fin KB := Main[41] - 1
  let E64 : Fin KB := Main[41] * E63
  let E65 : Fin KB := Main[42] - 1
  let E66 : Fin KB := Main[42] * E65
  let E67 : Fin KB := Main[43] - 1
  let E68 : Fin KB := Main[43] * E67
  let E69 : Fin KB := Main[44] - 1
  let E70 : Fin KB := Main[44] * E69
  let E71 : Fin KB := Main[39] * 1
  let E72 : Fin KB := 0 + E71
  let E73 : Fin KB := Main[40] * 2
  let E74 : Fin KB := E72 + E73
  let E75 : Fin KB := Main[41] * 4
  let E76 : Fin KB := E74 + E75
  let E77 : Fin KB := Main[42] * 8
  let E78 : Fin KB := E76 + E77
  let E79 : Fin KB := Main[43] * 16
  let E80 : Fin KB := E78 + E79
  let E81 : Fin KB := Main[44] * 32
  let E82 : Fin KB := E80 + E81
  let E83 : Fin KB := Main[25] - E82
  let E84 : Fin KB := E83 * 2097414145
  let E85 : Fin KB := Main[44] * 2
  let E86 : Fin KB := E85 * E14
  let E87 : Fin KB := Main[43] + E86
  let E88 : Fin KB := E87 - 0
  let E89 : Fin KB := Main[61] * E88
  let E90 : Fin KB := Main[61] - 1
  let E91 : Fin KB := Main[61] * E90
  let E92 : Fin KB := Main[44] * 2
  let E93 : Fin KB := E92 * E14
  let E94 : Fin KB := Main[43] + E93
  let E95 : Fin KB := E94 - 1
  let E96 : Fin KB := Main[62] * E95
  let E97 : Fin KB := Main[62] - 1
  let E98 : Fin KB := Main[62] * E97
  let E99 : Fin KB := Main[44] * 2
  let E100 : Fin KB := E99 * E14
  let E101 : Fin KB := Main[43] + E100
  let E102 : Fin KB := E101 - 2
  let E103 : Fin KB := Main[63] * E102
  let E104 : Fin KB := Main[63] - 1
  let E105 : Fin KB := Main[63] * E104
  let E106 : Fin KB := Main[44] * 2
  let E107 : Fin KB := E106 * E14
  let E108 : Fin KB := Main[43] + E107
  let E109 : Fin KB := E108 - 3
  let E110 : Fin KB := Main[64] * E109
  let E111 : Fin KB := Main[64] - 1
  let E112 : Fin KB := Main[64] * E111
  let E113 : Fin KB := Main[61] + Main[62]
  let E114 : Fin KB := E113 + Main[63]
  let E115 : Fin KB := E114 + Main[64]
  let E116 : Fin KB := E115 - 1
  let E117 : Fin KB := E2 * E116
  let E118 : Fin KB := 1 - Main[39]
  let E119 : Fin KB := E118 + 1
  let E120 : Fin KB := E119 * 2
  let E121 : Fin KB := 1 - Main[40]
  let E122 : Fin KB := E121 * 3
  let E123 : Fin KB := E122 + 1
  let E124 : Fin KB := E120 * E123
  let E125 : Fin KB := Main[48] - E124
  let E126 : Fin KB := 1 - Main[41]
  let E127 : Fin KB := E126 * 15
  let E128 : Fin KB := E127 + 1
  let E129 : Fin KB := Main[48] * E128
  let E130 : Fin KB := Main[47] - E129
  let E131 : Fin KB := 1 - Main[42]
  let E132 : Fin KB := E131 * 255
  let E133 : Fin KB := E132 + 1
  let E134 : Fin KB := Main[47] * E133
  let E135 : Fin KB := Main[46] - E134
  let E136 : Fin KB := 16 - E78
  let E137 : Fin KB := Main[15] * Main[46]
  let E138 : Fin KB := Main[53] * 65536
  let E139 : Fin KB := Main[49] * Main[46]
  let E140 : Fin KB := E138 + E139
  let E141 : Fin KB := E137 - E140
  let E142 : Fin KB := 16 - E78
  let E143 : Fin KB := Main[16] * Main[46]
  let E144 : Fin KB := Main[54] * 65536
  let E145 : Fin KB := Main[50] * Main[46]
  let E146 : Fin KB := E144 + E145
  let E147 : Fin KB := E143 - E146
  let E148 : Fin KB := 16 - E78
  let E149 : Fin KB := Main[17] * Main[46]
  let E150 : Fin KB := E149 * E14
  let E151 : Fin KB := Main[55] * 65536
  let E152 : Fin KB := Main[51] * Main[46]
  let E153 : Fin KB := E151 + E152
  let E154 : Fin KB := E150 - E153
  let E155 : Fin KB := 16 - E78
  let E156 : Fin KB := Main[18] * Main[46]
  let E157 : Fin KB := E156 * E14
  let E158 : Fin KB := Main[56] * 65536
  let E159 : Fin KB := Main[52] * Main[46]
  let E160 : Fin KB := E158 + E159
  let E161 : Fin KB := E157 - E160
  let E162 : Fin KB := Main[50] * Main[46]
  let E163 : Fin KB := Main[53] + E162
  let E164 : Fin KB := Main[57] - E163
  let E165 : Fin KB := Main[51] * Main[46]
  let E166 : Fin KB := Main[54] + E165
  let E167 : Fin KB := Main[58] - E166
  let E168 : Fin KB := Main[52] * Main[46]
  let E169 : Fin KB := Main[55] + E168
  let E170 : Fin KB := Main[59] - E169
  let E171 : Fin KB := Main[60] - Main[56]
  let CS0 : SP1ConstraintList := U16MSBOperation.constraints Main[18] { msb := Main[37] } Main[66]
  let CS1 : SP1ConstraintList := U16MSBOperation.constraints Main[16] { msb := Main[37] } Main[68]
  let E172 : Fin KB := Main[65] + Main[67]
  let E173 : Fin KB := E172 * Main[37]
  let E174 : Fin KB := Main[37] * Main[46]
  let E175 : Fin KB := Main[45] - E174
  let CS2 : SP1ConstraintList := U16MSBOperation.constraints Main[34] { msb := Main[38] } E13
  let E176 : Fin KB := E13 - 1
  let E177 : Fin KB := E176 * Main[38]
  let E178 : Fin KB := Main[33] - Main[57]
  let E179 : Fin KB := Main[61] * E178
  let E180 : Fin KB := E14 * E179
  let E181 : Fin KB := Main[34] - Main[58]
  let E182 : Fin KB := Main[61] * E181
  let E183 : Fin KB := E14 * E182
  let E184 : Fin KB := Main[35] - Main[59]
  let E185 : Fin KB := Main[61] * E184
  let E186 : Fin KB := E14 * E185
  let E187 : Fin KB := Main[37] * 65536
  let E188 : Fin KB := E187 - Main[45]
  let E189 : Fin KB := Main[60] + E188
  let E190 : Fin KB := Main[36] - E189
  let E191 : Fin KB := Main[61] * E190
  let E192 : Fin KB := E14 * E191
  let E193 : Fin KB := Main[33] - Main[58]
  let E194 : Fin KB := Main[62] * E193
  let E195 : Fin KB := E14 * E194
  let E196 : Fin KB := Main[34] - Main[59]
  let E197 : Fin KB := Main[62] * E196
  let E198 : Fin KB := E14 * E197
  let E199 : Fin KB := Main[37] * 65536
  let E200 : Fin KB := E199 - Main[45]
  let E201 : Fin KB := Main[60] + E200
  let E202 : Fin KB := Main[35] - E201
  let E203 : Fin KB := Main[62] * E202
  let E204 : Fin KB := E14 * E203
  let E205 : Fin KB := Main[37] * 65535
  let E206 : Fin KB := Main[36] - E205
  let E207 : Fin KB := Main[62] * E206
  let E208 : Fin KB := E14 * E207
  let E209 : Fin KB := Main[33] - Main[59]
  let E210 : Fin KB := Main[63] * E209
  let E211 : Fin KB := E14 * E210
  let E212 : Fin KB := Main[37] * 65536
  let E213 : Fin KB := E212 - Main[45]
  let E214 : Fin KB := Main[60] + E213
  let E215 : Fin KB := Main[34] - E214
  let E216 : Fin KB := Main[63] * E215
  let E217 : Fin KB := E14 * E216
  let E218 : Fin KB := Main[37] * 65535
  let E219 : Fin KB := Main[35] - E218
  let E220 : Fin KB := Main[63] * E219
  let E221 : Fin KB := E14 * E220
  let E222 : Fin KB := Main[37] * 65535
  let E223 : Fin KB := Main[36] - E222
  let E224 : Fin KB := Main[63] * E223
  let E225 : Fin KB := E14 * E224
  let E226 : Fin KB := Main[37] * 65536
  let E227 : Fin KB := E226 - Main[45]
  let E228 : Fin KB := Main[60] + E227
  let E229 : Fin KB := Main[33] - E228
  let E230 : Fin KB := Main[64] * E229
  let E231 : Fin KB := E14 * E230
  let E232 : Fin KB := Main[37] * 65535
  let E233 : Fin KB := Main[34] - E232
  let E234 : Fin KB := Main[64] * E233
  let E235 : Fin KB := E14 * E234
  let E236 : Fin KB := Main[37] * 65535
  let E237 : Fin KB := Main[35] - E236
  let E238 : Fin KB := Main[64] * E237
  let E239 : Fin KB := E14 * E238
  let E240 : Fin KB := Main[37] * 65535
  let E241 : Fin KB := Main[36] - E240
  let E242 : Fin KB := Main[64] * E241
  let E243 : Fin KB := E14 * E242
  let E244 : Fin KB := Main[33] - Main[57]
  let E245 : Fin KB := Main[61] * E244
  let E246 : Fin KB := E13 * E245
  let E247 : Fin KB := Main[37] * 65536
  let E248 : Fin KB := E247 - Main[45]
  let E249 : Fin KB := Main[58] + E248
  let E250 : Fin KB := Main[34] - E249
  let E251 : Fin KB := Main[61] * E250
  let E252 : Fin KB := E13 * E251
  let E253 : Fin KB := Main[37] * 65536
  let E254 : Fin KB := E253 - Main[45]
  let E255 : Fin KB := Main[58] + E254
  let E256 : Fin KB := Main[33] - E255
  let E257 : Fin KB := Main[62] * E256
  let E258 : Fin KB := E13 * E257
  let E259 : Fin KB := Main[37] * 65535
  let E260 : Fin KB := Main[34] - E259
  let E261 : Fin KB := Main[62] * E260
  let E262 : Fin KB := E13 * E261
  let E263 : Fin KB := Main[38] * 65535
  let E264 : Fin KB := Main[35] - E263
  let E265 : Fin KB := E13 * E264
  let E266 : Fin KB := Main[38] * 65535
  let E267 : Fin KB := Main[36] - E266
  let E268 : Fin KB := E13 * E267
  let E269 : Fin KB := Main[3] + 4
  let CS3 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E269, Main[4], Main[5]] 8 E2
  let E270 : Fin KB := Main[1] * 65536
  let E271 : Fin KB := Main[2] + E270
  let CS4 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E271 #v[Main[3], Main[4], Main[5]] E21 #v[E58, E44, E28, E35] #v[Main[33], Main[34], Main[35], Main[36]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31], is_trusted := Main[32] } E2
  CS0 ++ CS1 ++ CS2 ++ CS3 ++ CS4 ++ [
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.assertZero E12),
    (.assertZero E47),
    (.assertZero E60),
    (.assertZero E62),
    (.assertZero E64),
    (.assertZero E66),
    (.assertZero E68),
    (.assertZero E70),
    (.send (.byte (ByteOpcode.ofNat 6) E84 10 0) E2),
    (.assertZero E89),
    (.assertZero E91),
    (.assertZero E96),
    (.assertZero E98),
    (.assertZero E103),
    (.assertZero E105),
    (.assertZero E110),
    (.assertZero E112),
    (.assertZero E117),
    (.assertZero E125),
    (.assertZero E130),
    (.assertZero E135),
    (.send (.byte (ByteOpcode.ofNat 6) Main[49] E78 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[53] E136 0) E2),
    (.assertZero E141),
    (.send (.byte (ByteOpcode.ofNat 6) Main[50] E78 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[54] E142 0) E2),
    (.assertZero E147),
    (.send (.byte (ByteOpcode.ofNat 6) Main[51] E78 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[55] E148 0) E2),
    (.assertZero E154),
    (.send (.byte (ByteOpcode.ofNat 6) Main[52] E78 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[56] E155 0) E2),
    (.assertZero E161),
    (.assertZero E164),
    (.assertZero E167),
    (.assertZero E170),
    (.assertZero E171),
    (.assertZero E173),
    (.assertZero E175),
    (.assertZero E177),
    (.assertZero E180),
    (.assertZero E183),
    (.assertZero E186),
    (.assertZero E192),
    (.assertZero E195),
    (.assertZero E198),
    (.assertZero E204),
    (.assertZero E208),
    (.assertZero E211),
    (.assertZero E217),
    (.assertZero E221),
    (.assertZero E225),
    (.assertZero E231),
    (.assertZero E235),
    (.assertZero E239),
    (.assertZero E243),
    (.assertZero E246),
    (.assertZero E252),
    (.assertZero E258),
    (.assertZero E262),
    (.assertZero E265),
    (.assertZero E268),
  ]

end constraints

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
    let is_trusted := Main[32]
    let a0 := Main[33]
    let a1 := Main[34]
    let a2 := Main[35]
    let a3 := Main[36]
    let msb_b := Main[37]
    let msb_srw := Main[38]
    let cb0 := Main[39]
    let cb1 := Main[40]
    let cb2 := Main[41]
    let cb3 := Main[42]
    let cb4 := Main[43]
    let cb5 := Main[44]
    let smv := Main[45]
    let v0123 := Main[46]
    let v012 := Main[47]
    let v01 := Main[48]
    let ll0 := Main[49]
    let ll1 := Main[50]
    let ll2 := Main[51]
    let ll3 := Main[52]
    let hl0 := Main[53]
    let hl1 := Main[54]
    let hl2 := Main[55]
    let hl3 := Main[56]
    let lr0 := Main[57]
    let lr1 := Main[58]
    let lr2 := Main[59]
    let lr3 := Main[60]
    let su160 := Main[61]
    let su161 := Main[62]
    let su162 := Main[63]
    let su163 := Main[64]
    let srl := Main[65]
    let sra := Main[66]
    let srlw := Main[67]
    let sraw := Main[68]
    let bop := Main[69]
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints b3 { msb := msb_b } sra) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints b1 { msb := msb_b } sraw) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints a1 { msb := msb_srw } (srlw + sraw)) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (srl + sra + srlw + sraw)) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (srl * 7 + sra * 8 + srlw * 42 + sraw * 43) (
      #v[Main[65] * 8 + Main[66] * 8 + Main[67] * 8 + Main[68] * 8 - (6 * Main[31] + Main[69]),
        Main[65] * 51 + Main[66] * 51 + Main[67] * 59 + Main[68] * 59 - 32 * Main[31],
        Main[65] * 5 + Main[66] * 5 + Main[67] * 5 + Main[68] * 5, Main[66] * 32 + Main[68] * 32]
    ) #v[a0, a1, a2, a3] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[c0, c1, c2, c3], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := imm, is_trusted := is_trusted } (srl + sra + srlw + sraw)) ∧
    (srl = 0 ∨ srl = 1) ∧
    (sra = 0 ∨ sra = 1) ∧
    (srlw = 0 ∨ srlw = 1) ∧
    (sraw = 0 ∨ sraw = 1) ∧
    (srl + sra + srlw + sraw = 0 ∨ srl + sra + srlw + sraw = 1) ∧
    (bop = (Main[67] + Main[68]) * Main[31]) ∧
    (cb0 = 0 ∨ cb0 = 1) ∧
    (cb1 = 0 ∨ cb1 = 1) ∧
    (cb2 = 0 ∨ cb2 = 1) ∧
    (cb3 = 0 ∨ cb3 = 1) ∧
    (cb4 = 0 ∨ cb4 = 1) ∧
    (cb5 = 0 ∨ cb5 = 1) ∧
    (¬srl + sra + srlw + sraw = 0 → ((Main[25] - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)) * 2097414145).val < 1024) ∧
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

section field_arithmetic

lemma cancel_mul_65536_v1 { a b c x : Fin KB } (h_dvd : (x : ℕ) ∣ 65536) : a * x = b * 65536 + c * x → a = b * ((65536 : ℕ) / (x : ℕ)) + c
  := by
  obtain ⟨ z, h_eq ⟩ := h_dvd; rw [h_eq]
  have x_pos : 0 < (x : ℕ) := by nlinarith
  have xz_BB : (x : ℕ) * z < 2130706433 := by nlinarith
  have h_eq_BB : 65536 = x * z := by simp [Fin.ext_iff, Fin.mul_def]; omega
  rw [h_eq_BB]
  rw [mul_comm x z, ← mul_assoc, ← right_distrib]
  intro eq; apply mul_right_cancel₀ (by omega) at eq; rw [eq]
  congr
  rw [Fin.ext_iff]; simp [Fin.mul_def]
  rw [Nat.mod_eq_of_lt (by nlinarith)]
  rw [Nat.mod_eq_of_lt (by omega)]
  aesop

lemma cancel_mul_65536_v2 { b c x : Fin KB } (h_dvd : (x : ℕ) ∣ 65536) : b * 65536 + c * x = 0 → b * ((65536 : ℕ) / (x : ℕ)) + c = 0
  := by intro h_eq; symm; apply cancel_mul_65536_v1 <;> aesop

lemma is_mod_64 {c0 m : Fin KB} : m < 64 → c0 < 65536 → ((c0 - m) * 2097414145).val < 1024 → c0.val % 64 = m := by
  simp [Fin.sub_def, Fin.mul_def, Fin.lt_def]; ring_nf
  intro hm hc hdiff
  suffices : (BitVec.ofNat 64 c0.val) % 64#64 = BitVec.ofNat 64 m.val
  . simp [BitVec.toNat_eq] at this
    repeat rw [Nat.mod_eq_of_lt (b := 18446744073709551616) (by omega)] at this
    assumption
  . suffices : ((2130706433 - BitVec.ofNat 64 ↑m) * BitVec.ofNat 64 2097414145 + BitVec.ofNat 64 ↑c0 * 2097414145#64) % 2130706433#64 < 1024#64
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

@[simp] def is_srl := Main[65] = 1 ∧ Main[31] = 0
@[simp] def is_sra := Main[66] = 1 ∧ Main[31] = 0
@[simp] def is_srlw := Main[67] = 1 ∧ Main[31] = 0
@[simp] def is_sraw := Main[68] = 1 ∧ Main[31] = 0
@[simp] def is_srli := Main[65] = 1 ∧ Main[31] = 1
@[simp] def is_srai := Main[66] = 1 ∧ Main[31] = 1
@[simp] def is_srliw := Main[67] = 1 ∧ Main[31] = 1
@[simp] def is_sraiw := Main[68] = 1 ∧ Main[31] = 1

lemma single_op : List.Forall SP1Constraint.toProp (constraints Main) →
  (Main[65] = 1 → Main[66] = 0 ∧ Main[67] = 0 ∧ Main[68] = 0) ∧
  (Main[66] = 1 → Main[65] = 0 ∧ Main[67] = 0 ∧ Main[68] = 0) ∧
  (Main[67] = 1 → Main[65] = 0 ∧ Main[66] = 0 ∧ Main[68] = 0) ∧
  (Main[68] = 1 → Main[65] = 0 ∧ Main[66] = 0 ∧ Main[67] = 0)
   := by
  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, rest ⟩ := cstrs
  clear *- b_srl b_sra b_srlw b_sraw one_of_ops
  aesop

lemma single_su16 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  (Main[61] = 1 → Main[62] = 0 ∧ Main[63] = 0 ∧ Main[64] = 0) ∧
  (Main[62] = 1 → Main[61] = 0 ∧ Main[63] = 0 ∧ Main[64] = 0) ∧
  (Main[63] = 1 → Main[61] = 0 ∧ Main[62] = 0 ∧ Main[64] = 0) ∧
  (Main[64] = 1 → Main[61] = 0 ∧ Main[62] = 0 ∧ Main[63] = 0)
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

lemma srl_real : Main[65] = 1 → is_real Main := by simp [is_real]; aesop
lemma sra_real : Main[66] = 1 → is_real Main := by simp [is_real]; aesop
lemma srlw_real : Main[67] = 1 → is_real Main := by simp [is_real]; aesop
lemma sraw_real : Main[68] = 1 → is_real Main := by simp [is_real]; aesop

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
      ((Main[65] = 1 ∨ Main[66] = 1 → Main[25] < 64) ∧
       (Main[67] = 1 ∨ Main[68] = 1 → Main[25] < 32)))) := by
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
  (Main[6] = 0 → Main[33] = 0 ∧ Main[34] = 0 ∧ Main[35] = 0 ∧ Main[36] = 0) := by
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
  Word.isU64 #v[Main[33], Main[34], Main[35], Main[36]] := by
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
  set is_trusted := Main[32]
  set a0 := Main[33]
  set a1 := Main[34]
  set a2 := Main[35]
  set a3 := Main[36]
  set msb_b := Main[37]
  set msb_srw := Main[38]
  set cb0 := Main[39]
  set cb1 := Main[40]
  set cb2 := Main[41]
  set cb3 := Main[42]
  set cb4 := Main[43]
  set cb5 := Main[44]
  set smv := Main[45]
  set v0123 := Main[46]
  set v012 := Main[47]
  set v01 := Main[48]
  set ll0 := Main[49]
  set ll1 := Main[50]
  set ll2 := Main[51]
  set ll3 := Main[52]
  set hl0 := Main[53]
  set hl1 := Main[54]
  set hl2 := Main[55]
  set hl3 := Main[56]
  set lr0 := Main[57]
  set lr1 := Main[58]
  set lr2 := Main[59]
  set lr3 := Main[60]
  set su160 := Main[61]
  set su161 := Main[62]
  set su162 := Main[63]
  set su163 := Main[64]
  set srl := Main[65]
  set sra := Main[66]
  set srlw := Main[67]
  set sraw := Main[68]
  set bop := Main[69]

  suffices : a0.val < 65536 ∧ a1.val < 65536 ∧ a2.val < 65536 ∧ a3.val < 65536
  . clear *- this
    apply Word.isU64_of_cases <;> simp_all
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
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          try omega
        }
      have a1_16 : (hl1 + ll2 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b1_16 b2_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b1_dec h_b2_dec lt_ll1 lt_ll2 lt_hl1 lt_hl2
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
          try simp [Fin.val_add, Fin.val_mul] at b1_16 b2_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          try omega
        }
      have a2_16 : (hl2 + ll3 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b2_16 b3_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec h_b3_dec lt_ll2 lt_ll3 lt_hl2 lt_hl3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b3_dec
          try simp [Fin.val_add, Fin.val_mul] at b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
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
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          try omega
        }
      have a1_16 : (hl1 + ll2 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b1_16 b2_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b1_dec h_b2_dec lt_ll1 lt_ll2 lt_hl1 lt_hl2
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
          try simp [Fin.val_add, Fin.val_mul] at b1_16 b2_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          try omega
        }
      have a2_16 : (hl2 + ll3 * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
        clear *- b2_16 b3_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec h_b3_dec lt_ll2 lt_ll3 lt_hl2 lt_hl3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
          try apply cancel_mul_65536_v1 (by simp) at h_b3_dec
          try simp [Fin.val_add, Fin.val_mul] at b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          try omega
        }
      have a3_16 : (hl3 + (msb_b * 65536 - msb_b * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1)))).val < 65536 := by
        clear *- h_msb_b3 b_cb0 b_cb1 b_cb2 b_cb3 b3_16 h_b3_dec lt_ll3 lt_hl3
        rw [U16MSBOperation.allHold_constraints_iff] at h_msb_b3
        obtain ⟨ _, b_msb_b3, _ ⟩ := h_msb_b3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> rcases b_msb_b3 <;> simp_all
        all_goals { clear *- lt_hl3; omega }
      have msb_b : (msb_b * 65535).val < 65536 := by
        suffices b_msb : msb_b = 0 ∨ msb_b = 1
        . clear *- b_msb;rcases b_msb <;> simp_all
        . rw [U16MSBOperation.allHold_constraints_iff] at h_msb_b3
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
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
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
        . rw [U16MSBOperation.allHold_constraints_iff] at h_msb_a1
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
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          try omega
        }
      have a1_16 : (hl1 + (msb_b * 65536 - msb_b * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1)))).val < 65536 := by
        clear *- h_msb_b3 b1_16 b2_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b1_dec lt_ll1 lt_hl1
        rw [U16MSBOperation.allHold_constraints_iff] at h_msb_b3
        obtain ⟨ _, b_msb_b3, _ ⟩ := h_msb_b3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> rcases b_msb_b3 <;> simp_all
        all_goals { clear *- lt_hl1; omega }
      have msb_b: (msb_b * 65535).val < 65536 := by
        suffices b_msb_b : msb_b = 0 ∨ msb_b = 1
        . clear *- b_msb_b; rcases b_msb_b <;> simp_all
        . rw [U16MSBOperation.allHold_constraints_iff] at h_msb_b1
          clear *- h_msb_b1; simp_all
      have msb_srw : (msb_srw * 65535).val < 65536 := by
        suffices b_msb_srw : msb_srw = 0 ∨ msb_srw = 1
        . clear *- b_msb_srw; rcases b_msb_srw <;> simp_all
        . rw [U16MSBOperation.allHold_constraints_iff] at h_msb_a1
          clear *- h_msb_a1; simp_all

      rcases b_su160 <;> simp_all
      rcases b_su161 <;> simp_all
      rcases b_su162 <;> simp_all

lemma ops_U64 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[33], Main[34], Main[35], Main[36]] ∧
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
def sp1_op_c_imm : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[65] = 1 ∨ Main[66] = 1 → BitVec 6 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have := immediate_bounds Main cstrs real
  simp_all
  omega

@[simp]
def sp1_op_c_imm_w : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[67] = 1 ∨ Main[68] = 1 → BitVec 5 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have := immediate_bounds Main cstrs real
  simp_all
  omega

end operands

section srl

lemma spec.srl (h : is_srl Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRL
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
    set is_trusted := Main[32]
    set a0 := Main[33]
    set a1 := Main[34]
    set a2 := Main[35]
    set a3 := Main[36]
    set msb_b := Main[37]
    set msb_srw := Main[38]
    set cb0 := Main[39]
    set cb1 := Main[40]
    set cb2 := Main[41]
    set cb3 := Main[42]
    set cb4 := Main[43]
    set cb5 := Main[44]
    set smv := Main[45]
    set v0123 := Main[46]
    set v012 := Main[47]
    set v01 := Main[48]
    set ll0 := Main[49]
    set ll1 := Main[50]
    set ll2 := Main[51]
    set ll3 := Main[52]
    set hl0 := Main[53]
    set hl1 := Main[54]
    set hl2 := Main[55]
    set hl3 := Main[56]
    set lr0 := Main[57]
    set lr1 := Main[58]
    set lr2 := Main[59]
    set lr3 := Main[60]
    set su160 := Main[61]
    set su161 := Main[62]
    set su162 := Main[63]
    set su163 := Main[64]
    set srl := Main[65]
    set sra := Main[66]
    set srlw := Main[67]
    set sraw := Main[68]
    set bop := Main[69]

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
      repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
      try omega
    }

end srl

section srli

lemma spec.srli (h : is_srli Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRL
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
    set is_trusted := Main[32]
    set a0 := Main[33]
    set a1 := Main[34]
    set a2 := Main[35]
    set a3 := Main[36]
    set msb_b := Main[37]
    set msb_srw := Main[38]
    set cb0 := Main[39]
    set cb1 := Main[40]
    set cb2 := Main[41]
    set cb3 := Main[42]
    set cb4 := Main[43]
    set cb5 := Main[44]
    set smv := Main[45]
    set v0123 := Main[46]
    set v012 := Main[47]
    set v01 := Main[48]
    set ll0 := Main[49]
    set ll1 := Main[50]
    set ll2 := Main[51]
    set ll3 := Main[52]
    set hl0 := Main[53]
    set hl1 := Main[54]
    set hl2 := Main[55]
    set hl3 := Main[56]
    set lr0 := Main[57]
    set lr1 := Main[58]
    set lr2 := Main[59]
    set lr3 := Main[60]
    set su160 := Main[61]
    set su161 := Main[62]
    set su162 := Main[63]
    set su163 := Main[64]
    set srl := Main[65]
    set sra := Main[66]
    set srlw := Main[67]
    set sraw := Main[68]
    set bop := Main[69]

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
      repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
      try omega
    }

end srli

section srlw

lemma spec.srlw (h : is_srlw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRLW
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
    set is_trusted := Main[32]
    set a0 := Main[33]
    set a1 := Main[34]
    set a2 := Main[35]
    set a3 := Main[36]
    set msb_b := Main[37]
    set msb_srw := Main[38]
    set cb0 := Main[39]
    set cb1 := Main[40]
    set cb2 := Main[41]
    set cb3 := Main[42]
    set cb4 := Main[43]
    set cb5 := Main[44]
    set smv := Main[45]
    set v0123 := Main[46]
    set v012 := Main[47]
    set v01 := Main[48]
    set ll0 := Main[49]
    set ll1 := Main[50]
    set ll2 := Main[51]
    set ll3 := Main[52]
    set hl0 := Main[53]
    set hl1 := Main[54]
    set hl2 := Main[55]
    set hl3 := Main[56]
    set lr0 := Main[57]
    set lr1 := Main[58]
    set lr2 := Main[59]
    set lr3 := Main[60]
    set su160 := Main[61]
    set su161 := Main[62]
    set su162 := Main[63]
    set su163 := Main[64]
    set srl := Main[65]
    set sra := Main[66]
    set srlw := Main[67]
    set sraw := Main[68]
    set bop := Main[69]

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

    have is_U32_a : HWord.isU32 #v[ a0, a1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_b : HWord.isU32 #v[ b0, b1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_c : HWord.isU32 #v[ c0, c1 ] := by apply HWord.isU32_of_cases <;> assumption

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

    have : ((Word.low #v[c0, c1, c2, c3]).toBitVec32.toNat % 32) = c0.val % 32 := by
      simp [Word.low, HWord.toBitVec32_toNat is_U32_c, HWord.toNat];
      omega
    rw [this]; clear this
    simp [Word.low]

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

    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      . unfold HWord.isNegative; split_ifs <;> simp_all; omega
      . congr; rw [HWord.isNegative_msb is_U32_a]

    . suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = (HWord.toBitVec32 #v[b0, b1] >>> (c0.val % 32))
      . rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      . rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        rw [HWord.toBitVec32_toNat is_U32_a, HWord.toBitVec32_toNat is_U32_b]
        rw [this]; clear this h_a3

        cases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
        rcases b_cb3 <;> rcases b_cb4 <;> simp_all

        all_goals {
          (try apply cancel_mul_65536_v1 (by simp) at h_b0_dec)
          (try apply cancel_mul_65536_v1 (by simp) at h_b1_dec)
          simp_all [HWord.toNat]
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          omega
        }

end srlw

section srliw

lemma spec.srliw (h : is_srliw Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRLW
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
    set is_trusted := Main[32]
    set a0 := Main[33]
    set a1 := Main[34]
    set a2 := Main[35]
    set a3 := Main[36]
    set msb_b := Main[37]
    set msb_srw := Main[38]
    set cb0 := Main[39]
    set cb1 := Main[40]
    set cb2 := Main[41]
    set cb3 := Main[42]
    set cb4 := Main[43]
    set cb5 := Main[44]
    set smv := Main[45]
    set v0123 := Main[46]
    set v012 := Main[47]
    set v01 := Main[48]
    set ll0 := Main[49]
    set ll1 := Main[50]
    set ll2 := Main[51]
    set ll3 := Main[52]
    set hl0 := Main[53]
    set hl1 := Main[54]
    set hl2 := Main[55]
    set hl3 := Main[56]
    set lr0 := Main[57]
    set lr1 := Main[58]
    set lr2 := Main[59]
    set lr3 := Main[60]
    set su160 := Main[61]
    set su161 := Main[62]
    set su162 := Main[63]
    set su163 := Main[64]
    set srl := Main[65]
    set sra := Main[66]
    set srlw := Main[67]
    set sraw := Main[68]
    set bop := Main[69]

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

    have is_U32_a : HWord.isU32 #v[ a0, a1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_b : HWord.isU32 #v[ b0, b1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_c : HWord.isU32 #v[ c0, 0 ] := by apply HWord.isU32_of_cases <;> simp; omega

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

    have : ((Word.low #v[c0, 0, 0, 0]).toBitVec32.toNat % 32) = c0.val % 32 := by
      simp [Word.low, HWord.toBitVec32_toNat is_U32_c, HWord.toNat]
    rw [this]; clear this
    simp [Word.low]

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

    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      . unfold HWord.isNegative; split_ifs <;> simp_all; omega
      . congr; rw [HWord.isNegative_msb is_U32_a]

    . suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = (HWord.toBitVec32 #v[b0, b1] >>> (c0.val % 32))
      . rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      . rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        rw [HWord.toBitVec32_toNat is_U32_a, HWord.toBitVec32_toNat is_U32_b]
        rw [this]; clear this h_a3

        cases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
        rcases b_cb3 <;> rcases b_cb4 <;> simp_all

        all_goals {
          (try apply cancel_mul_65536_v1 (by simp) at h_b0_dec)
          (try apply cancel_mul_65536_v1 (by simp) at h_b1_dec)
          simp_all [HWord.toNat]
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          omega
        }

end srliw

section sra

lemma spec.sra (h : is_sra Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRA
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
    set is_trusted := Main[32]
    set a0 := Main[33]
    set a1 := Main[34]
    set a2 := Main[35]
    set a3 := Main[36]
    set msb_b := Main[37]
    set msb_srw := Main[38]
    set cb0 := Main[39]
    set cb1 := Main[40]
    set cb2 := Main[41]
    set cb3 := Main[42]
    set cb4 := Main[43]
    set cb5 := Main[44]
    set smv := Main[45]
    set v0123 := Main[46]
    set v012 := Main[47]
    set v01 := Main[48]
    set ll0 := Main[49]
    set ll1 := Main[50]
    set ll2 := Main[51]
    set ll3 := Main[52]
    set hl0 := Main[53]
    set hl1 := Main[54]
    set hl2 := Main[55]
    set hl3 := Main[56]
    set lr0 := Main[57]
    set lr1 := Main[58]
    set lr2 := Main[59]
    set lr3 := Main[60]
    set su160 := Main[61]
    set su161 := Main[62]
    set su162 := Main[63]
    set su163 := Main[64]
    set srl := Main[65]
    set sra := Main[66]
    set srlw := Main[67]
    set sraw := Main[68]
    set bop := Main[69]

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

    have msb_b3_spec := U16MSBOperation.spec b3_16 h_msb_b3
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
      repeat rw [Nat.mod_eq_of_lt (a := _ * _) (b := 2130706433) (by omega)]
      repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
      simp_all
      omega
    }

end sra

section srai

lemma spec.srai (h : is_srai Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRA
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
    set is_trusted := Main[32]
    set a0 := Main[33]
    set a1 := Main[34]
    set a2 := Main[35]
    set a3 := Main[36]
    set msb_b := Main[37]
    set msb_srw := Main[38]
    set cb0 := Main[39]
    set cb1 := Main[40]
    set cb2 := Main[41]
    set cb3 := Main[42]
    set cb4 := Main[43]
    set cb5 := Main[44]
    set smv := Main[45]
    set v0123 := Main[46]
    set v012 := Main[47]
    set v01 := Main[48]
    set ll0 := Main[49]
    set ll1 := Main[50]
    set ll2 := Main[51]
    set ll3 := Main[52]
    set hl0 := Main[53]
    set hl1 := Main[54]
    set hl2 := Main[55]
    set hl3 := Main[56]
    set lr0 := Main[57]
    set lr1 := Main[58]
    set lr2 := Main[59]
    set lr3 := Main[60]
    set su160 := Main[61]
    set su161 := Main[62]
    set su162 := Main[63]
    set su163 := Main[64]
    set srl := Main[65]
    set sra := Main[66]
    set srlw := Main[67]
    set sraw := Main[68]
    set bop := Main[69]

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

    have msb_b3_spec := U16MSBOperation.spec b3_16 h_msb_b3
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
      repeat rw [Nat.mod_eq_of_lt (a := _ * _) (b := 2130706433) (by omega)]
      repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
      simp_all
      omega
    }

end srai

section sraw

lemma spec.sraw (h : is_sraw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRAW
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
    set is_trusted := Main[32]
    set a0 := Main[33]
    set a1 := Main[34]
    set a2 := Main[35]
    set a3 := Main[36]
    set msb_b := Main[37]
    set msb_srw := Main[38]
    set cb0 := Main[39]
    set cb1 := Main[40]
    set cb2 := Main[41]
    set cb3 := Main[42]
    set cb4 := Main[43]
    set cb5 := Main[44]
    set smv := Main[45]
    set v0123 := Main[46]
    set v012 := Main[47]
    set v01 := Main[48]
    set ll0 := Main[49]
    set ll1 := Main[50]
    set ll2 := Main[51]
    set ll3 := Main[52]
    set hl0 := Main[53]
    set hl1 := Main[54]
    set hl2 := Main[55]
    set hl3 := Main[56]
    set lr0 := Main[57]
    set lr1 := Main[58]
    set lr2 := Main[59]
    set lr3 := Main[60]
    set su160 := Main[61]
    set su161 := Main[62]
    set su162 := Main[63]
    set su163 := Main[64]
    set srl := Main[65]
    set sra := Main[66]
    set srlw := Main[67]
    set sraw := Main[68]
    set bop := Main[69]

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

    have is_U32_a : HWord.isU32 #v[ a0, a1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_b : HWord.isU32 #v[ b0, b1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_c : HWord.isU32 #v[ c0, c1 ] := by apply HWord.isU32_of_cases <;> assumption

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

    have : ((Word.low #v[c0, c1, c2, c3]).toBitVec32.toNat % 32) = c0.val % 32 := by
      simp [Word.low, HWord.toBitVec32_toNat is_U32_c, HWord.toNat];
      omega
    rw [this]; clear this
    simp [Word.low]

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

    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      . unfold HWord.isNegative; split_ifs <;> simp_all; omega
      . congr; rw [HWord.isNegative_msb is_U32_a]

    . suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = BitVec.sshiftRight (HWord.toBitVec32 #v[b0, b1]) (c0.val % 32)
      . rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      . rw [this]; clear this h_a3
        rw [← BitVec.toInt_inj, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
        rw [HWord.toBitVec32_toInt (w := #v[a0, a1]) is_U32_a]
        rw [HWord.toBitVec32_toInt (w := #v[b0, b1]) is_U32_b]

        have msb_b1_spec := U16MSBOperation.spec b1_16 h_msb_b1
        simp at msb_b1_spec

        have b_msb : msb_b = 0 ∨ msb_b = 1 := by
          clear *- msb_b1_spec
          split_ifs at msb_b1_spec <;> simp_all

        have b_msb_iff_neg_b : HWord.isNegative #v[b0, b1] ↔ msb_b = 1 := by rw [msb_b1_spec, HWord.isNegative]; aesop

        have b_msb_iff_neg_a : HWord.isNegative #v[a0, a1] ↔ msb_b = 1 := by
          simp [msb_b1_spec, HWord.isNegative]
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
          iterate 2 rw [HWord.toInt]
          try rw [if_pos b_msb_iff_neg_a, if_pos b_msb_iff_neg_b]
          try rw [if_neg b_msb_iff_neg_a, if_neg b_msb_iff_neg_b]
          iterate 2 rw [HWord.toNat]
          iterate 4 rw [Vector.getElem_mk]
          simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
          clear *- lt_ll0 lt_hl0 lt_ll1 lt_hl1
          try simp only [Fin.add_def, Fin.mul_def]
          repeat rw [Nat.mod_eq_of_lt (a := _ * _) (b := 2130706433) (by omega)]
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          simp_all
          omega
        }

end sraw

section sraiw

lemma spec.sraiw (h : is_sraiw Main ) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[33], Main[34], Main[35], Main[36]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRAW
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
    set is_trusted := Main[32]
    set a0 := Main[33]
    set a1 := Main[34]
    set a2 := Main[35]
    set a3 := Main[36]
    set msb_b := Main[37]
    set msb_srw := Main[38]
    set cb0 := Main[39]
    set cb1 := Main[40]
    set cb2 := Main[41]
    set cb3 := Main[42]
    set cb4 := Main[43]
    set cb5 := Main[44]
    set smv := Main[45]
    set v0123 := Main[46]
    set v012 := Main[47]
    set v01 := Main[48]
    set ll0 := Main[49]
    set ll1 := Main[50]
    set ll2 := Main[51]
    set ll3 := Main[52]
    set hl0 := Main[53]
    set hl1 := Main[54]
    set hl2 := Main[55]
    set hl3 := Main[56]
    set lr0 := Main[57]
    set lr1 := Main[58]
    set lr2 := Main[59]
    set lr3 := Main[60]
    set su160 := Main[61]
    set su161 := Main[62]
    set su162 := Main[63]
    set su163 := Main[64]
    set srl := Main[65]
    set sra := Main[66]
    set srlw := Main[67]
    set sraw := Main[68]
    set bop := Main[69]

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

    have is_U32_a : HWord.isU32 #v[ a0, a1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_b : HWord.isU32 #v[ b0, b1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_c : HWord.isU32 #v[ c0, 0 ] := by apply HWord.isU32_of_cases <;> [ assumption; simp ]

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

    have : ((Word.low #v[c0, 0, 0, 0]).toBitVec32.toNat % 32) = c0.val % 32 := by
      simp [Word.low, HWord.toBitVec32_toNat is_U32_c, HWord.toNat]
    rw [this]; clear this
    simp [Word.low]

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

    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      . unfold HWord.isNegative; split_ifs <;> simp_all; omega
      . congr; rw [HWord.isNegative_msb is_U32_a]

    . suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = BitVec.sshiftRight (HWord.toBitVec32 #v[b0, b1]) (c0.val % 32)
      . rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      . rw [this]; clear this h_a3
        rw [← BitVec.toInt_inj, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
        rw [HWord.toBitVec32_toInt (w := #v[a0, a1]) is_U32_a]
        rw [HWord.toBitVec32_toInt (w := #v[b0, b1]) is_U32_b]

        have msb_b1_spec := U16MSBOperation.spec b1_16 h_msb_b1
        simp at msb_b1_spec

        have b_msb : msb_b = 0 ∨ msb_b = 1 := by
          clear *- msb_b1_spec
          split_ifs at msb_b1_spec <;> simp_all

        have b_msb_iff_neg_b : HWord.isNegative #v[b0, b1] ↔ msb_b = 1 := by rw [msb_b1_spec, HWord.isNegative]; aesop

        have b_msb_iff_neg_a : HWord.isNegative #v[a0, a1] ↔ msb_b = 1 := by
          simp [msb_b1_spec, HWord.isNegative]
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
          iterate 2 rw [HWord.toInt]
          try rw [if_pos b_msb_iff_neg_a, if_pos b_msb_iff_neg_b]
          try rw [if_neg b_msb_iff_neg_a, if_neg b_msb_iff_neg_b]
          iterate 2 rw [HWord.toNat]
          iterate 4 rw [Vector.getElem_mk]
          simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
          clear *- lt_ll0 lt_hl0 lt_ll1 lt_hl1
          try simp only [Fin.add_def, Fin.mul_def]
          repeat rw [Nat.mod_eq_of_lt (a := _ * _) (b := 2130706433) (by omega)]
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          simp_all
          omega
        }

end sraiw

end ShiftRight
