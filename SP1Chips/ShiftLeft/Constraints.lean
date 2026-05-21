import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace ShiftLeft

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

-- Generated Lean code for chip ShiftLeftChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 65) : SP1ConstraintList F :=
  let E0 : F := Main[62] + Main[63]
  let E1 : F := E0 - 1
  let E2 : F := E0 * E1
  let E3 : F := Main[62] - 1
  let E4 : F := Main[62] * E3
  let E5 : F := Main[63] - 1
  let E6 : F := Main[63] * E5
  let E7 : F := Main[36] - 1
  let E8 : F := Main[36] * E7
  let E9 : F := Main[37] - 1
  let E10 : F := Main[37] * E9
  let E11 : F := Main[38] - 1
  let E12 : F := Main[38] * E11
  let E13 : F := Main[39] - 1
  let E14 : F := Main[39] * E13
  let E15 : F := Main[40] - 1
  let E16 : F := Main[40] * E15
  let E17 : F := Main[41] - 1
  let E18 : F := Main[41] * E17
  let E19 : F := Main[36] * 1
  let E20 : F := 0 + E19
  let E21 : F := Main[37] * 2
  let E22 : F := E20 + E21
  let E23 : F := Main[38] * 4
  let E24 : F := E22 + E23
  let E25 : F := Main[39] * 8
  let E26 : F := E24 + E25
  let E27 : F := Main[40] * 16
  let E28 : F := E26 + E27
  let E29 : F := Main[41] * 32
  let E30 : F := E28 + E29
  let E31 : F := Main[25] - E30
  let E32 : F := E31 * ((64 : F)⁻¹)
  let E33 : F := Main[41] * 2
  let E34 : F := E33 * Main[62]
  let E35 : F := Main[40] + E34
  let E36 : F := E35 - 0
  let E37 : F := Main[45] * E36
  let E38 : F := Main[45] - 1
  let E39 : F := Main[45] * E38
  let E40 : F := Main[41] * 2
  let E41 : F := E40 * Main[62]
  let E42 : F := Main[40] + E41
  let E43 : F := E42 - 1
  let E44 : F := Main[46] * E43
  let E45 : F := Main[46] - 1
  let E46 : F := Main[46] * E45
  let E47 : F := Main[41] * 2
  let E48 : F := E47 * Main[62]
  let E49 : F := Main[40] + E48
  let E50 : F := E49 - 2
  let E51 : F := Main[47] * E50
  let E52 : F := Main[47] - 1
  let E53 : F := Main[47] * E52
  let E54 : F := Main[41] * 2
  let E55 : F := E54 * Main[62]
  let E56 : F := Main[40] + E55
  let E57 : F := E56 - 3
  let E58 : F := Main[48] * E57
  let E59 : F := Main[48] - 1
  let E60 : F := Main[48] * E59
  let E61 : F := Main[45] + Main[46]
  let E62 : F := E61 + Main[47]
  let E63 : F := E62 + Main[48]
  let E64 : F := E63 - 1
  let E65 : F := E0 * E64
  let E66 : F := Main[36] + 1
  let E67 : F := Main[37] * 3
  let E68 : F := E67 + 1
  let E69 : F := E66 * E68
  let E70 : F := Main[42] - E69
  let E71 : F := Main[38] * 15
  let E72 : F := E71 + 1
  let E73 : F := Main[42] * E72
  let E74 : F := Main[43] - E73
  let E75 : F := Main[39] * 255
  let E76 : F := E75 + 1
  let E77 : F := Main[43] * E76
  let E78 : F := Main[44] - E77
  let E79 : F := 16 - E26
  let E80 : F := Main[15] * Main[44]
  let E81 : F := Main[53] * 65536
  let E82 : F := Main[49] * Main[44]
  let E83 : F := E81 + E82
  let E84 : F := E80 - E83
  let E85 : F := 16 - E26
  let E86 : F := Main[16] * Main[44]
  let E87 : F := Main[54] * 65536
  let E88 : F := Main[50] * Main[44]
  let E89 : F := E87 + E88
  let E90 : F := E86 - E89
  let E91 : F := 16 - E26
  let E92 : F := Main[17] * Main[44]
  let E93 : F := Main[55] * 65536
  let E94 : F := Main[51] * Main[44]
  let E95 : F := E93 + E94
  let E96 : F := E92 - E95
  let E97 : F := 16 - E26
  let E98 : F := Main[18] * Main[44]
  let E99 : F := Main[56] * 65536
  let E100 : F := Main[52] * Main[44]
  let E101 : F := E99 + E100
  let E102 : F := E98 - E101
  let E103 : F := Main[49] * Main[44]
  let E104 : F := Main[57] - E103
  let E105 : F := Main[50] * Main[44]
  let E106 : F := E105 + Main[53]
  let E107 : F := Main[58] - E106
  let E108 : F := Main[51] * Main[44]
  let E109 : F := E108 + Main[54]
  let E110 : F := Main[59] - E109
  let E111 : F := Main[52] * Main[44]
  let E112 : F := E111 + Main[55]
  let E113 : F := Main[60] - E112
  let E114 : F := Main[32] - Main[57]
  let E115 : F := Main[45] * E114
  let E116 : F := Main[62] * E115
  let E117 : F := Main[33] - Main[58]
  let E118 : F := Main[45] * E117
  let E119 : F := Main[62] * E118
  let E120 : F := Main[34] - Main[59]
  let E121 : F := Main[45] * E120
  let E122 : F := Main[62] * E121
  let E123 : F := Main[35] - Main[60]
  let E124 : F := Main[45] * E123
  let E125 : F := Main[62] * E124
  let E126 : F := Main[46] * Main[32]
  let E127 : F := Main[62] * E126
  let E128 : F := Main[33] - Main[57]
  let E129 : F := Main[46] * E128
  let E130 : F := Main[62] * E129
  let E131 : F := Main[34] - Main[58]
  let E132 : F := Main[46] * E131
  let E133 : F := Main[62] * E132
  let E134 : F := Main[35] - Main[59]
  let E135 : F := Main[46] * E134
  let E136 : F := Main[62] * E135
  let E137 : F := Main[47] * Main[32]
  let E138 : F := Main[62] * E137
  let E139 : F := Main[47] * Main[33]
  let E140 : F := Main[62] * E139
  let E141 : F := Main[34] - Main[57]
  let E142 : F := Main[47] * E141
  let E143 : F := Main[62] * E142
  let E144 : F := Main[35] - Main[58]
  let E145 : F := Main[47] * E144
  let E146 : F := Main[62] * E145
  let E147 : F := Main[48] * Main[32]
  let E148 : F := Main[62] * E147
  let E149 : F := Main[48] * Main[33]
  let E150 : F := Main[62] * E149
  let E151 : F := Main[48] * Main[34]
  let E152 : F := Main[62] * E151
  let E153 : F := Main[35] - Main[57]
  let E154 : F := Main[48] * E153
  let E155 : F := Main[62] * E154
  let E156 : F := Main[32] - Main[57]
  let E157 : F := Main[45] * E156
  let E158 : F := Main[63] * E157
  let E159 : F := Main[33] - Main[58]
  let E160 : F := Main[45] * E159
  let E161 : F := Main[63] * E160
  let E162 : F := Main[46] * Main[32]
  let E163 : F := Main[63] * E162
  let E164 : F := Main[33] - Main[57]
  let E165 : F := Main[46] * E164
  let E166 : F := Main[63] * E165
  let E167 : F := Main[61] * 65535
  let E168 : F := E167 - Main[34]
  let E169 : F := Main[63] * E168
  let E170 : F := Main[61] * 65535
  let E171 : F := E170 - Main[35]
  let E172 : F := Main[63] * E171
  let CS0 : SP1ConstraintList F := U16MSBOperation.constraints Main[33] { msb := Main[61] } Main[63]
  let E173 : F := Main[62] * 6
  let E174 : F := Main[63] * 21
  let E175 : F := E173 + E174
  let E176 : F := Main[62] * 1
  let E177 : F := Main[63] * 1
  let E178 : F := E176 + E177
  let E179 : F := Main[62] * 0
  let E180 : F := Main[63] * 0
  let E181 : F := E179 + E180
  let E182 : F := Main[62] * 51
  let E183 : F := Main[63] * 59
  let E184 : F := E182 + E183
  let E185 : F := 32 * Main[31]
  let E186 : F := E184 - E185
  let E187 : F := Main[63] * Main[31]
  let E188 : F := Main[64] - E187
  let E189 : F := Main[62] * 8
  let E190 : F := Main[63] * 8
  let E191 : F := E189 + E190
  let E192 : F := 6 * Main[31]
  let E193 : F := 1 * Main[64]
  let E194 : F := E192 + E193
  let E195 : F := E191 - E194
  let E196 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E196, Main[4], Main[5]] 8 E0
  let E197 : F := Main[1] * 65536
  let E198 : F := Main[2] + E197
  let CS2 : SP1ConstraintList F := ALUTypeReader.constraints Main[0] E198 #v[Main[3], Main[4], Main[5]] E175 #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E0 E0
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
    (.assertZero E188),
    (.assertZero Main[13]),
  ]

end constraints

variable {p : ℕ}

section opcodes

@[reducible] def is_sll (Main : Vector (ZMod p) 65) := Main[62] = 1 ∧ Main[31] = 0
  deriving Decidable

@[reducible] def is_sllw (Main : Vector (ZMod p) 65) := Main[63] = 1 ∧ Main[31] = 0
  deriving Decidable

@[reducible] def is_slli (Main : Vector (ZMod p) 65) := Main[62] = 1 ∧ Main[31] = 1
  deriving Decidable

@[reducible] def is_slliw (Main : Vector (ZMod p) 65) := Main[63] = 1 ∧ Main[31] = 1
  deriving Decidable

@[simp] def sp1_op_a (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val
@[simp] def sp1_op_b (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val
@[simp] def sp1_op_c (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val
@[simp] def sp1_op_c_imm (Main : Vector (ZMod p) 65) : BitVec 6 :=
  BitVec.ofNat 6 Main[21].val
@[simp] def sp1_op_c_imm_w (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val

end opcodes

end ShiftLeft
