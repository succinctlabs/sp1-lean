import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace ShiftRight

set_option linter.style.setOption false
set_option linter.style.longLine false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
-- Unused variables expected because many proofs are currently stopped.
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000

section constraints

-- Generated Lean code for chip ShiftRightChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 69) : SP1ConstraintList F :=
  let E0 : F := Main[64] + Main[65]
  let E1 : F := E0 + Main[66]
  let E2 : F := E1 + Main[67]
  let E3 : F := Main[64] - 1
  let E4 : F := Main[64] * E3
  let E5 : F := Main[65] - 1
  let E6 : F := Main[65] * E5
  let E7 : F := Main[66] - 1
  let E8 : F := Main[66] * E7
  let E9 : F := Main[67] - 1
  let E10 : F := Main[67] * E9
  let E11 : F := E2 - 1
  let E12 : F := E2 * E11
  let E13 : F := Main[66] + Main[67]
  let E14 : F := Main[64] + Main[65]
  let E15 : F := Main[64] * 7
  let E16 : F := Main[65] * 8
  let E17 : F := E15 + E16
  let E18 : F := Main[66] * 22
  let E19 : F := E17 + E18
  let E20 : F := Main[67] * 23
  let E21 : F := E19 + E20
  let E22 : F := Main[64] * 5
  let E23 : F := Main[65] * 5
  let E24 : F := E22 + E23
  let E25 : F := Main[66] * 5
  let E26 : F := E24 + E25
  let E27 : F := Main[67] * 5
  let E28 : F := E26 + E27
  let E29 : F := Main[64] * 0
  let E30 : F := Main[65] * 32
  let E31 : F := E29 + E30
  let E32 : F := Main[66] * 0
  let E33 : F := E31 + E32
  let E34 : F := Main[67] * 32
  let E35 : F := E33 + E34
  let E36 : F := Main[64] * 51
  let E37 : F := Main[65] * 51
  let E38 : F := E36 + E37
  let E39 : F := Main[66] * 59
  let E40 : F := E38 + E39
  let E41 : F := Main[67] * 59
  let E42 : F := E40 + E41
  let E43 : F := 32 * Main[31]
  let E44 : F := E42 - E43
  let E45 : F := Main[66] + Main[67]
  let E46 : F := E45 * Main[31]
  let E47 : F := Main[68] - E46
  let E48 : F := Main[64] * 8
  let E49 : F := Main[65] * 8
  let E50 : F := E48 + E49
  let E51 : F := Main[66] * 8
  let E52 : F := E50 + E51
  let E53 : F := Main[67] * 8
  let E54 : F := E52 + E53
  let E55 : F := 6 * Main[31]
  let E56 : F := 1 * Main[68]
  let E57 : F := E55 + E56
  let E58 : F := E54 - E57
  let E59 : F := Main[38] - 1
  let E60 : F := Main[38] * E59
  let E61 : F := Main[39] - 1
  let E62 : F := Main[39] * E61
  let E63 : F := Main[40] - 1
  let E64 : F := Main[40] * E63
  let E65 : F := Main[41] - 1
  let E66 : F := Main[41] * E65
  let E67 : F := Main[42] - 1
  let E68 : F := Main[42] * E67
  let E69 : F := Main[43] - 1
  let E70 : F := Main[43] * E69
  let E71 : F := Main[38] * 1
  let E72 : F := 0 + E71
  let E73 : F := Main[39] * 2
  let E74 : F := E72 + E73
  let E75 : F := Main[40] * 4
  let E76 : F := E74 + E75
  let E77 : F := Main[41] * 8
  let E78 : F := E76 + E77
  let E79 : F := Main[42] * 16
  let E80 : F := E78 + E79
  let E81 : F := Main[43] * 32
  let E82 : F := E80 + E81
  let E83 : F := Main[25] - E82
  let E84 : F := E83 * ((64 : F)⁻¹)
  let E85 : F := Main[43] * 2
  let E86 : F := E85 * E14
  let E87 : F := Main[42] + E86
  let E88 : F := E87 - 0
  let E89 : F := Main[60] * E88
  let E90 : F := Main[60] - 1
  let E91 : F := Main[60] * E90
  let E92 : F := Main[43] * 2
  let E93 : F := E92 * E14
  let E94 : F := Main[42] + E93
  let E95 : F := E94 - 1
  let E96 : F := Main[61] * E95
  let E97 : F := Main[61] - 1
  let E98 : F := Main[61] * E97
  let E99 : F := Main[43] * 2
  let E100 : F := E99 * E14
  let E101 : F := Main[42] + E100
  let E102 : F := E101 - 2
  let E103 : F := Main[62] * E102
  let E104 : F := Main[62] - 1
  let E105 : F := Main[62] * E104
  let E106 : F := Main[43] * 2
  let E107 : F := E106 * E14
  let E108 : F := Main[42] + E107
  let E109 : F := E108 - 3
  let E110 : F := Main[63] * E109
  let E111 : F := Main[63] - 1
  let E112 : F := Main[63] * E111
  let E113 : F := Main[60] + Main[61]
  let E114 : F := E113 + Main[62]
  let E115 : F := E114 + Main[63]
  let E116 : F := E115 - 1
  let E117 : F := E2 * E116
  let E118 : F := 1 - Main[38]
  let E119 : F := E118 + 1
  let E120 : F := E119 * 2
  let E121 : F := 1 - Main[39]
  let E122 : F := E121 * 3
  let E123 : F := E122 + 1
  let E124 : F := E120 * E123
  let E125 : F := Main[47] - E124
  let E126 : F := 1 - Main[40]
  let E127 : F := E126 * 15
  let E128 : F := E127 + 1
  let E129 : F := Main[47] * E128
  let E130 : F := Main[46] - E129
  let E131 : F := 1 - Main[41]
  let E132 : F := E131 * 255
  let E133 : F := E132 + 1
  let E134 : F := Main[46] * E133
  let E135 : F := Main[45] - E134
  let E136 : F := 16 - E78
  let E137 : F := Main[15] * Main[45]
  let E138 : F := Main[52] * 65536
  let E139 : F := Main[48] * Main[45]
  let E140 : F := E138 + E139
  let E141 : F := E137 - E140
  let E142 : F := 16 - E78
  let E143 : F := Main[16] * Main[45]
  let E144 : F := Main[53] * 65536
  let E145 : F := Main[49] * Main[45]
  let E146 : F := E144 + E145
  let E147 : F := E143 - E146
  let E148 : F := 16 - E78
  let E149 : F := Main[17] * Main[45]
  let E150 : F := E149 * E14
  let E151 : F := Main[54] * 65536
  let E152 : F := Main[50] * Main[45]
  let E153 : F := E151 + E152
  let E154 : F := E150 - E153
  let E155 : F := 16 - E78
  let E156 : F := Main[18] * Main[45]
  let E157 : F := E156 * E14
  let E158 : F := Main[55] * 65536
  let E159 : F := Main[51] * Main[45]
  let E160 : F := E158 + E159
  let E161 : F := E157 - E160
  let E162 : F := Main[49] * Main[45]
  let E163 : F := Main[52] + E162
  let E164 : F := Main[56] - E163
  let E165 : F := Main[50] * Main[45]
  let E166 : F := Main[53] + E165
  let E167 : F := Main[57] - E166
  let E168 : F := Main[51] * Main[45]
  let E169 : F := Main[54] + E168
  let E170 : F := Main[58] - E169
  let E171 : F := Main[59] - Main[55]
  let CS0 : SP1ConstraintList F := U16MSBOperation.constraints Main[18] { msb := Main[36] } Main[65]
  let CS1 : SP1ConstraintList F := U16MSBOperation.constraints Main[16] { msb := Main[36] } Main[67]
  let E172 : F := Main[64] + Main[66]
  let E173 : F := E172 * Main[36]
  let E174 : F := Main[36] * Main[45]
  let E175 : F := Main[44] - E174
  let CS2 : SP1ConstraintList F := U16MSBOperation.constraints Main[33] { msb := Main[37] } E13
  let E176 : F := E13 - 1
  let E177 : F := E176 * Main[37]
  let E178 : F := Main[32] - Main[56]
  let E179 : F := Main[60] * E178
  let E180 : F := E14 * E179
  let E181 : F := Main[33] - Main[57]
  let E182 : F := Main[60] * E181
  let E183 : F := E14 * E182
  let E184 : F := Main[34] - Main[58]
  let E185 : F := Main[60] * E184
  let E186 : F := E14 * E185
  let E187 : F := Main[36] * 65536
  let E188 : F := E187 - Main[44]
  let E189 : F := Main[59] + E188
  let E190 : F := Main[35] - E189
  let E191 : F := Main[60] * E190
  let E192 : F := E14 * E191
  let E193 : F := Main[32] - Main[57]
  let E194 : F := Main[61] * E193
  let E195 : F := E14 * E194
  let E196 : F := Main[33] - Main[58]
  let E197 : F := Main[61] * E196
  let E198 : F := E14 * E197
  let E199 : F := Main[36] * 65536
  let E200 : F := E199 - Main[44]
  let E201 : F := Main[59] + E200
  let E202 : F := Main[34] - E201
  let E203 : F := Main[61] * E202
  let E204 : F := E14 * E203
  let E205 : F := Main[36] * 65535
  let E206 : F := Main[35] - E205
  let E207 : F := Main[61] * E206
  let E208 : F := E14 * E207
  let E209 : F := Main[32] - Main[58]
  let E210 : F := Main[62] * E209
  let E211 : F := E14 * E210
  let E212 : F := Main[36] * 65536
  let E213 : F := E212 - Main[44]
  let E214 : F := Main[59] + E213
  let E215 : F := Main[33] - E214
  let E216 : F := Main[62] * E215
  let E217 : F := E14 * E216
  let E218 : F := Main[36] * 65535
  let E219 : F := Main[34] - E218
  let E220 : F := Main[62] * E219
  let E221 : F := E14 * E220
  let E222 : F := Main[36] * 65535
  let E223 : F := Main[35] - E222
  let E224 : F := Main[62] * E223
  let E225 : F := E14 * E224
  let E226 : F := Main[36] * 65536
  let E227 : F := E226 - Main[44]
  let E228 : F := Main[59] + E227
  let E229 : F := Main[32] - E228
  let E230 : F := Main[63] * E229
  let E231 : F := E14 * E230
  let E232 : F := Main[36] * 65535
  let E233 : F := Main[33] - E232
  let E234 : F := Main[63] * E233
  let E235 : F := E14 * E234
  let E236 : F := Main[36] * 65535
  let E237 : F := Main[34] - E236
  let E238 : F := Main[63] * E237
  let E239 : F := E14 * E238
  let E240 : F := Main[36] * 65535
  let E241 : F := Main[35] - E240
  let E242 : F := Main[63] * E241
  let E243 : F := E14 * E242
  let E244 : F := Main[32] - Main[56]
  let E245 : F := Main[60] * E244
  let E246 : F := E13 * E245
  let E247 : F := Main[36] * 65536
  let E248 : F := E247 - Main[44]
  let E249 : F := Main[57] + E248
  let E250 : F := Main[33] - E249
  let E251 : F := Main[60] * E250
  let E252 : F := E13 * E251
  let E253 : F := Main[36] * 65536
  let E254 : F := E253 - Main[44]
  let E255 : F := Main[57] + E254
  let E256 : F := Main[32] - E255
  let E257 : F := Main[61] * E256
  let E258 : F := E13 * E257
  let E259 : F := Main[36] * 65535
  let E260 : F := Main[33] - E259
  let E261 : F := Main[61] * E260
  let E262 : F := E13 * E261
  let E263 : F := Main[37] * 65535
  let E264 : F := Main[34] - E263
  let E265 : F := E13 * E264
  let E266 : F := Main[37] * 65535
  let E267 : F := Main[35] - E266
  let E268 : F := E13 * E267
  let E269 : F := Main[3] + 4
  let CS3 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E269, Main[4], Main[5]] 8 E2
  let E270 : F := Main[1] * 65536
  let E271 : F := Main[2] + E270
  let CS4 : SP1ConstraintList F := ALUTypeReader.constraints Main[0] E271 #v[Main[3], Main[4], Main[5]] E21 #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E2 E2
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

variable {p : ℕ}

section opcodes

@[simp] def is_real (Main : Vector (ZMod p) 69) : Prop :=
  Main[64] = 1 ∨ Main[65] = 1 ∨ Main[66] = 1 ∨ Main[67] = 1
  deriving Decidable

@[simp] def is_srl (Main : Vector (ZMod p) 69) := Main[64] = 1 ∧ Main[31] = 0
  deriving Decidable
@[simp] def is_sra (Main : Vector (ZMod p) 69) := Main[65] = 1 ∧ Main[31] = 0
  deriving Decidable
@[simp] def is_srlw (Main : Vector (ZMod p) 69) := Main[66] = 1 ∧ Main[31] = 0
  deriving Decidable
@[simp] def is_sraw (Main : Vector (ZMod p) 69) := Main[67] = 1 ∧ Main[31] = 0
  deriving Decidable
@[simp] def is_srli (Main : Vector (ZMod p) 69) := Main[64] = 1 ∧ Main[31] = 1
  deriving Decidable
@[simp] def is_srai (Main : Vector (ZMod p) 69) := Main[65] = 1 ∧ Main[31] = 1
  deriving Decidable
@[simp] def is_srliw (Main : Vector (ZMod p) 69) := Main[66] = 1 ∧ Main[31] = 1
  deriving Decidable
@[simp] def is_sraiw (Main : Vector (ZMod p) 69) := Main[67] = 1 ∧ Main[31] = 1
  deriving Decidable

@[simp] def sp1_op_a (Main : Vector (ZMod p) 69) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val
@[simp] def sp1_op_b (Main : Vector (ZMod p) 69) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val
@[simp] def sp1_op_c (Main : Vector (ZMod p) 69) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val
@[simp] def sp1_op_c_imm (Main : Vector (ZMod p) 69) : BitVec 6 :=
  BitVec.ofNat 6 Main[21].val
@[simp] def sp1_op_c_imm_w (Main : Vector (ZMod p) 69) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val

end opcodes

end ShiftRight
