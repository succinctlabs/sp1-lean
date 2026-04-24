import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace ShiftRight

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 69)
def is_real : Prop := Main[64] = 1 ∨ Main[65] = 1 ∨ Main[66] = 1 ∨ Main[67] = 1

section constraints

-- Generated Lean code for chip ShiftRightChip
@[irreducible] def constraints (Main : Vector (Fin KB) 69) : SP1ConstraintList :=
  let E0 : Fin KB := Main[64] + Main[65]
  let E1 : Fin KB := E0 + Main[66]
  let E2 : Fin KB := E1 + Main[67]
  let E3 : Fin KB := Main[64] - 1
  let E4 : Fin KB := Main[64] * E3
  let E5 : Fin KB := Main[65] - 1
  let E6 : Fin KB := Main[65] * E5
  let E7 : Fin KB := Main[66] - 1
  let E8 : Fin KB := Main[66] * E7
  let E9 : Fin KB := Main[67] - 1
  let E10 : Fin KB := Main[67] * E9
  let E11 : Fin KB := E2 - 1
  let E12 : Fin KB := E2 * E11
  let E13 : Fin KB := Main[66] + Main[67]
  let E14 : Fin KB := Main[64] + Main[65]
  let E15 : Fin KB := Main[64] * 7
  let E16 : Fin KB := Main[65] * 8
  let E17 : Fin KB := E15 + E16
  let E18 : Fin KB := Main[66] * 22
  let E19 : Fin KB := E17 + E18
  let E20 : Fin KB := Main[67] * 23
  let E21 : Fin KB := E19 + E20
  let E22 : Fin KB := Main[64] * 5
  let E23 : Fin KB := Main[65] * 5
  let E24 : Fin KB := E22 + E23
  let E25 : Fin KB := Main[66] * 5
  let E26 : Fin KB := E24 + E25
  let E27 : Fin KB := Main[67] * 5
  let E28 : Fin KB := E26 + E27
  let E29 : Fin KB := Main[64] * 0
  let E30 : Fin KB := Main[65] * 32
  let E31 : Fin KB := E29 + E30
  let E32 : Fin KB := Main[66] * 0
  let E33 : Fin KB := E31 + E32
  let E34 : Fin KB := Main[67] * 32
  let E35 : Fin KB := E33 + E34
  let E36 : Fin KB := Main[64] * 51
  let E37 : Fin KB := Main[65] * 51
  let E38 : Fin KB := E36 + E37
  let E39 : Fin KB := Main[66] * 59
  let E40 : Fin KB := E38 + E39
  let E41 : Fin KB := Main[67] * 59
  let E42 : Fin KB := E40 + E41
  let E43 : Fin KB := 32 * Main[31]
  let E44 : Fin KB := E42 - E43
  let E45 : Fin KB := Main[66] + Main[67]
  let E46 : Fin KB := E45 * Main[31]
  let E47 : Fin KB := Main[68] - E46
  let E48 : Fin KB := Main[64] * 8
  let E49 : Fin KB := Main[65] * 8
  let E50 : Fin KB := E48 + E49
  let E51 : Fin KB := Main[66] * 8
  let E52 : Fin KB := E50 + E51
  let E53 : Fin KB := Main[67] * 8
  let E54 : Fin KB := E52 + E53
  let E55 : Fin KB := 6 * Main[31]
  let E56 : Fin KB := 1 * Main[68]
  let E57 : Fin KB := E55 + E56
  let E58 : Fin KB := E54 - E57
  let E59 : Fin KB := Main[38] - 1
  let E60 : Fin KB := Main[38] * E59
  let E61 : Fin KB := Main[39] - 1
  let E62 : Fin KB := Main[39] * E61
  let E63 : Fin KB := Main[40] - 1
  let E64 : Fin KB := Main[40] * E63
  let E65 : Fin KB := Main[41] - 1
  let E66 : Fin KB := Main[41] * E65
  let E67 : Fin KB := Main[42] - 1
  let E68 : Fin KB := Main[42] * E67
  let E69 : Fin KB := Main[43] - 1
  let E70 : Fin KB := Main[43] * E69
  let E71 : Fin KB := Main[38] * 1
  let E72 : Fin KB := 0 + E71
  let E73 : Fin KB := Main[39] * 2
  let E74 : Fin KB := E72 + E73
  let E75 : Fin KB := Main[40] * 4
  let E76 : Fin KB := E74 + E75
  let E77 : Fin KB := Main[41] * 8
  let E78 : Fin KB := E76 + E77
  let E79 : Fin KB := Main[42] * 16
  let E80 : Fin KB := E78 + E79
  let E81 : Fin KB := Main[43] * 32
  let E82 : Fin KB := E80 + E81
  let E83 : Fin KB := Main[25] - E82
  let E84 : Fin KB := E83 * 2097414145
  let E85 : Fin KB := Main[43] * 2
  let E86 : Fin KB := E85 * E14
  let E87 : Fin KB := Main[42] + E86
  let E88 : Fin KB := E87 - 0
  let E89 : Fin KB := Main[60] * E88
  let E90 : Fin KB := Main[60] - 1
  let E91 : Fin KB := Main[60] * E90
  let E92 : Fin KB := Main[43] * 2
  let E93 : Fin KB := E92 * E14
  let E94 : Fin KB := Main[42] + E93
  let E95 : Fin KB := E94 - 1
  let E96 : Fin KB := Main[61] * E95
  let E97 : Fin KB := Main[61] - 1
  let E98 : Fin KB := Main[61] * E97
  let E99 : Fin KB := Main[43] * 2
  let E100 : Fin KB := E99 * E14
  let E101 : Fin KB := Main[42] + E100
  let E102 : Fin KB := E101 - 2
  let E103 : Fin KB := Main[62] * E102
  let E104 : Fin KB := Main[62] - 1
  let E105 : Fin KB := Main[62] * E104
  let E106 : Fin KB := Main[43] * 2
  let E107 : Fin KB := E106 * E14
  let E108 : Fin KB := Main[42] + E107
  let E109 : Fin KB := E108 - 3
  let E110 : Fin KB := Main[63] * E109
  let E111 : Fin KB := Main[63] - 1
  let E112 : Fin KB := Main[63] * E111
  let E113 : Fin KB := Main[60] + Main[61]
  let E114 : Fin KB := E113 + Main[62]
  let E115 : Fin KB := E114 + Main[63]
  let E116 : Fin KB := E115 - 1
  let E117 : Fin KB := E2 * E116
  let E118 : Fin KB := 1 - Main[38]
  let E119 : Fin KB := E118 + 1
  let E120 : Fin KB := E119 * 2
  let E121 : Fin KB := 1 - Main[39]
  let E122 : Fin KB := E121 * 3
  let E123 : Fin KB := E122 + 1
  let E124 : Fin KB := E120 * E123
  let E125 : Fin KB := Main[47] - E124
  let E126 : Fin KB := 1 - Main[40]
  let E127 : Fin KB := E126 * 15
  let E128 : Fin KB := E127 + 1
  let E129 : Fin KB := Main[47] * E128
  let E130 : Fin KB := Main[46] - E129
  let E131 : Fin KB := 1 - Main[41]
  let E132 : Fin KB := E131 * 255
  let E133 : Fin KB := E132 + 1
  let E134 : Fin KB := Main[46] * E133
  let E135 : Fin KB := Main[45] - E134
  let E136 : Fin KB := 16 - E78
  let E137 : Fin KB := Main[15] * Main[45]
  let E138 : Fin KB := Main[52] * 65536
  let E139 : Fin KB := Main[48] * Main[45]
  let E140 : Fin KB := E138 + E139
  let E141 : Fin KB := E137 - E140
  let E142 : Fin KB := 16 - E78
  let E143 : Fin KB := Main[16] * Main[45]
  let E144 : Fin KB := Main[53] * 65536
  let E145 : Fin KB := Main[49] * Main[45]
  let E146 : Fin KB := E144 + E145
  let E147 : Fin KB := E143 - E146
  let E148 : Fin KB := 16 - E78
  let E149 : Fin KB := Main[17] * Main[45]
  let E150 : Fin KB := E149 * E14
  let E151 : Fin KB := Main[54] * 65536
  let E152 : Fin KB := Main[50] * Main[45]
  let E153 : Fin KB := E151 + E152
  let E154 : Fin KB := E150 - E153
  let E155 : Fin KB := 16 - E78
  let E156 : Fin KB := Main[18] * Main[45]
  let E157 : Fin KB := E156 * E14
  let E158 : Fin KB := Main[55] * 65536
  let E159 : Fin KB := Main[51] * Main[45]
  let E160 : Fin KB := E158 + E159
  let E161 : Fin KB := E157 - E160
  let E162 : Fin KB := Main[49] * Main[45]
  let E163 : Fin KB := Main[52] + E162
  let E164 : Fin KB := Main[56] - E163
  let E165 : Fin KB := Main[50] * Main[45]
  let E166 : Fin KB := Main[53] + E165
  let E167 : Fin KB := Main[57] - E166
  let E168 : Fin KB := Main[51] * Main[45]
  let E169 : Fin KB := Main[54] + E168
  let E170 : Fin KB := Main[58] - E169
  let E171 : Fin KB := Main[59] - Main[55]
  let CS0 : SP1ConstraintList := U16MSBOperation.constraints Main[18] { msb := Main[36] } Main[65]
  let CS1 : SP1ConstraintList := U16MSBOperation.constraints Main[16] { msb := Main[36] } Main[67]
  let E172 : Fin KB := Main[64] + Main[66]
  let E173 : Fin KB := E172 * Main[36]
  let E174 : Fin KB := Main[36] * Main[45]
  let E175 : Fin KB := Main[44] - E174
  let CS2 : SP1ConstraintList := U16MSBOperation.constraints Main[33] { msb := Main[37] } E13
  let E176 : Fin KB := E13 - 1
  let E177 : Fin KB := E176 * Main[37]
  let E178 : Fin KB := Main[32] - Main[56]
  let E179 : Fin KB := Main[60] * E178
  let E180 : Fin KB := E14 * E179
  let E181 : Fin KB := Main[33] - Main[57]
  let E182 : Fin KB := Main[60] * E181
  let E183 : Fin KB := E14 * E182
  let E184 : Fin KB := Main[34] - Main[58]
  let E185 : Fin KB := Main[60] * E184
  let E186 : Fin KB := E14 * E185
  let E187 : Fin KB := Main[36] * 65536
  let E188 : Fin KB := E187 - Main[44]
  let E189 : Fin KB := Main[59] + E188
  let E190 : Fin KB := Main[35] - E189
  let E191 : Fin KB := Main[60] * E190
  let E192 : Fin KB := E14 * E191
  let E193 : Fin KB := Main[32] - Main[57]
  let E194 : Fin KB := Main[61] * E193
  let E195 : Fin KB := E14 * E194
  let E196 : Fin KB := Main[33] - Main[58]
  let E197 : Fin KB := Main[61] * E196
  let E198 : Fin KB := E14 * E197
  let E199 : Fin KB := Main[36] * 65536
  let E200 : Fin KB := E199 - Main[44]
  let E201 : Fin KB := Main[59] + E200
  let E202 : Fin KB := Main[34] - E201
  let E203 : Fin KB := Main[61] * E202
  let E204 : Fin KB := E14 * E203
  let E205 : Fin KB := Main[36] * 65535
  let E206 : Fin KB := Main[35] - E205
  let E207 : Fin KB := Main[61] * E206
  let E208 : Fin KB := E14 * E207
  let E209 : Fin KB := Main[32] - Main[58]
  let E210 : Fin KB := Main[62] * E209
  let E211 : Fin KB := E14 * E210
  let E212 : Fin KB := Main[36] * 65536
  let E213 : Fin KB := E212 - Main[44]
  let E214 : Fin KB := Main[59] + E213
  let E215 : Fin KB := Main[33] - E214
  let E216 : Fin KB := Main[62] * E215
  let E217 : Fin KB := E14 * E216
  let E218 : Fin KB := Main[36] * 65535
  let E219 : Fin KB := Main[34] - E218
  let E220 : Fin KB := Main[62] * E219
  let E221 : Fin KB := E14 * E220
  let E222 : Fin KB := Main[36] * 65535
  let E223 : Fin KB := Main[35] - E222
  let E224 : Fin KB := Main[62] * E223
  let E225 : Fin KB := E14 * E224
  let E226 : Fin KB := Main[36] * 65536
  let E227 : Fin KB := E226 - Main[44]
  let E228 : Fin KB := Main[59] + E227
  let E229 : Fin KB := Main[32] - E228
  let E230 : Fin KB := Main[63] * E229
  let E231 : Fin KB := E14 * E230
  let E232 : Fin KB := Main[36] * 65535
  let E233 : Fin KB := Main[33] - E232
  let E234 : Fin KB := Main[63] * E233
  let E235 : Fin KB := E14 * E234
  let E236 : Fin KB := Main[36] * 65535
  let E237 : Fin KB := Main[34] - E236
  let E238 : Fin KB := Main[63] * E237
  let E239 : Fin KB := E14 * E238
  let E240 : Fin KB := Main[36] * 65535
  let E241 : Fin KB := Main[35] - E240
  let E242 : Fin KB := Main[63] * E241
  let E243 : Fin KB := E14 * E242
  let E244 : Fin KB := Main[32] - Main[56]
  let E245 : Fin KB := Main[60] * E244
  let E246 : Fin KB := E13 * E245
  let E247 : Fin KB := Main[36] * 65536
  let E248 : Fin KB := E247 - Main[44]
  let E249 : Fin KB := Main[57] + E248
  let E250 : Fin KB := Main[33] - E249
  let E251 : Fin KB := Main[60] * E250
  let E252 : Fin KB := E13 * E251
  let E253 : Fin KB := Main[36] * 65536
  let E254 : Fin KB := E253 - Main[44]
  let E255 : Fin KB := Main[57] + E254
  let E256 : Fin KB := Main[32] - E255
  let E257 : Fin KB := Main[61] * E256
  let E258 : Fin KB := E13 * E257
  let E259 : Fin KB := Main[36] * 65535
  let E260 : Fin KB := Main[33] - E259
  let E261 : Fin KB := Main[61] * E260
  let E262 : Fin KB := E13 * E261
  let E263 : Fin KB := Main[37] * 65535
  let E264 : Fin KB := Main[34] - E263
  let E265 : Fin KB := E13 * E264
  let E266 : Fin KB := Main[37] * 65535
  let E267 : Fin KB := Main[35] - E266
  let E268 : Fin KB := E13 * E267
  let E269 : Fin KB := Main[3] + 4
  let CS3 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E269, Main[4], Main[5]] 8 E2
  let E270 : Fin KB := Main[1] * 65536
  let E271 : Fin KB := Main[2] + E270
  let CS4 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E271 #v[Main[3], Main[4], Main[5]] E21 #v[E58, E44, E28, E35] #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E2
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
    (.send (.byte (ByteOpcode.ofNat 6) Main[48] E78 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[52] E136 0) E2),
    (.assertZero E141),
    (.send (.byte (ByteOpcode.ofNat 6) Main[49] E78 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[53] E142 0) E2),
    (.assertZero E147),
    (.send (.byte (ByteOpcode.ofNat 6) Main[50] E78 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[54] E148 0) E2),
    (.assertZero E154),
    (.send (.byte (ByteOpcode.ofNat 6) Main[51] E78 0) E2),
    (.send (.byte (ByteOpcode.ofNat 6) Main[55] E155 0) E2),
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
    (.assertZero Main[13]),
  ]

end constraints

@[simp] def is_srl (Main : Vector (Fin KB) 69) := Main[64] = 1 ∧ Main[31] = 0
@[simp] def is_srli (Main : Vector (Fin KB) 69) := Main[64] = 1 ∧ Main[31] = 1
@[simp] def is_sra (Main : Vector (Fin KB) 69) := Main[65] = 1 ∧ Main[31] = 0
@[simp] def is_srai (Main : Vector (Fin KB) 69) := Main[65] = 1 ∧ Main[31] = 1
@[simp] def is_srlw (Main : Vector (Fin KB) 69) := Main[66] = 1 ∧ Main[31] = 0
@[simp] def is_srliw (Main : Vector (Fin KB) 69) := Main[66] = 1 ∧ Main[31] = 1
@[simp] def is_sraw (Main : Vector (Fin KB) 69) := Main[67] = 1 ∧ Main[31] = 0
@[simp] def is_sraiw (Main : Vector (Fin KB) 69) := Main[67] = 1 ∧ Main[31] = 1




lemma srl_real (Main : Vector (Fin KB) 69) (_ : Main[65] = 1) : is_real Main := by sorry
lemma sra_real (Main : Vector (Fin KB) 69) (_ : Main[66] = 1) : is_real Main := by sorry
lemma srlw_real (Main : Vector (Fin KB) 69) (_ : Main[67] = 1) : is_real Main := by sorry
lemma sraw_real (Main : Vector (Fin KB) 69) (_ : Main[68] = 1) : is_real Main := by sorry

@[simp]
def sp1_op_a {Main : Vector (Fin KB) 69} (_ : (constraints Main).allHold) (_ : is_real Main) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

@[simp]
def sp1_op_b {Main : Vector (Fin KB) 69} (_ : (constraints Main).allHold) (_ : is_real Main) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

@[simp]
def sp1_op_c {Main : Vector (Fin KB) 69} (_ : (constraints Main).allHold) (_ : is_real Main) (_ : Main[31] = 0) : BitVec 5 :=
  BitVec.ofNat 5 Main[21]

@[simp]
def sp1_op_c_imm {Main : Vector (Fin KB) 69} (_ : (constraints Main).allHold) (_ : is_real Main) (_ : Main[31] = 1) : BitVec 6 :=
  BitVec.ofNat 6 Main[21]

@[simp]
def sp1_op_c_imm_w {Main : Vector (Fin KB) 69} (_ : (constraints Main).allHold) (_ : is_real Main) (_ : Main[31] = 1) : BitVec 5 :=
  BitVec.ofNat 5 Main[21]

end ShiftRight
