import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace ShiftLeft

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 65)
def is_real : Prop := Main[62] = 1 ∨ Main[63] = 1

section constraints

-- Generated Lean code for chip ShiftLeftChip
@[irreducible] def constraints (Main : Vector (Fin KB) 65) : SP1ConstraintList :=
  let E0 : Fin KB := Main[62] + Main[63]
  let E1 : Fin KB := E0 - 1
  let E2 : Fin KB := E0 * E1
  let E3 : Fin KB := Main[62] - 1
  let E4 : Fin KB := Main[62] * E3
  let E5 : Fin KB := Main[63] - 1
  let E6 : Fin KB := Main[63] * E5
  let E7 : Fin KB := Main[36] - 1
  let E8 : Fin KB := Main[36] * E7
  let E9 : Fin KB := Main[37] - 1
  let E10 : Fin KB := Main[37] * E9
  let E11 : Fin KB := Main[38] - 1
  let E12 : Fin KB := Main[38] * E11
  let E13 : Fin KB := Main[39] - 1
  let E14 : Fin KB := Main[39] * E13
  let E15 : Fin KB := Main[40] - 1
  let E16 : Fin KB := Main[40] * E15
  let E17 : Fin KB := Main[41] - 1
  let E18 : Fin KB := Main[41] * E17
  let E19 : Fin KB := Main[36] * 1
  let E20 : Fin KB := 0 + E19
  let E21 : Fin KB := Main[37] * 2
  let E22 : Fin KB := E20 + E21
  let E23 : Fin KB := Main[38] * 4
  let E24 : Fin KB := E22 + E23
  let E25 : Fin KB := Main[39] * 8
  let E26 : Fin KB := E24 + E25
  let E27 : Fin KB := Main[40] * 16
  let E28 : Fin KB := E26 + E27
  let E29 : Fin KB := Main[41] * 32
  let E30 : Fin KB := E28 + E29
  let E31 : Fin KB := Main[25] - E30
  let E32 : Fin KB := E31 * 2097414145
  let E33 : Fin KB := Main[41] * 2
  let E34 : Fin KB := E33 * Main[62]
  let E35 : Fin KB := Main[40] + E34
  let E36 : Fin KB := E35 - 0
  let E37 : Fin KB := Main[45] * E36
  let E38 : Fin KB := Main[45] - 1
  let E39 : Fin KB := Main[45] * E38
  let E40 : Fin KB := Main[41] * 2
  let E41 : Fin KB := E40 * Main[62]
  let E42 : Fin KB := Main[40] + E41
  let E43 : Fin KB := E42 - 1
  let E44 : Fin KB := Main[46] * E43
  let E45 : Fin KB := Main[46] - 1
  let E46 : Fin KB := Main[46] * E45
  let E47 : Fin KB := Main[41] * 2
  let E48 : Fin KB := E47 * Main[62]
  let E49 : Fin KB := Main[40] + E48
  let E50 : Fin KB := E49 - 2
  let E51 : Fin KB := Main[47] * E50
  let E52 : Fin KB := Main[47] - 1
  let E53 : Fin KB := Main[47] * E52
  let E54 : Fin KB := Main[41] * 2
  let E55 : Fin KB := E54 * Main[62]
  let E56 : Fin KB := Main[40] + E55
  let E57 : Fin KB := E56 - 3
  let E58 : Fin KB := Main[48] * E57
  let E59 : Fin KB := Main[48] - 1
  let E60 : Fin KB := Main[48] * E59
  let E61 : Fin KB := Main[45] + Main[46]
  let E62 : Fin KB := E61 + Main[47]
  let E63 : Fin KB := E62 + Main[48]
  let E64 : Fin KB := E63 - 1
  let E65 : Fin KB := E0 * E64
  let E66 : Fin KB := Main[36] + 1
  let E67 : Fin KB := Main[37] * 3
  let E68 : Fin KB := E67 + 1
  let E69 : Fin KB := E66 * E68
  let E70 : Fin KB := Main[42] - E69
  let E71 : Fin KB := Main[38] * 15
  let E72 : Fin KB := E71 + 1
  let E73 : Fin KB := Main[42] * E72
  let E74 : Fin KB := Main[43] - E73
  let E75 : Fin KB := Main[39] * 255
  let E76 : Fin KB := E75 + 1
  let E77 : Fin KB := Main[43] * E76
  let E78 : Fin KB := Main[44] - E77
  let E79 : Fin KB := 16 - E26
  let E80 : Fin KB := Main[15] * Main[44]
  let E81 : Fin KB := Main[53] * 65536
  let E82 : Fin KB := Main[49] * Main[44]
  let E83 : Fin KB := E81 + E82
  let E84 : Fin KB := E80 - E83
  let E85 : Fin KB := 16 - E26
  let E86 : Fin KB := Main[16] * Main[44]
  let E87 : Fin KB := Main[54] * 65536
  let E88 : Fin KB := Main[50] * Main[44]
  let E89 : Fin KB := E87 + E88
  let E90 : Fin KB := E86 - E89
  let E91 : Fin KB := 16 - E26
  let E92 : Fin KB := Main[17] * Main[44]
  let E93 : Fin KB := Main[55] * 65536
  let E94 : Fin KB := Main[51] * Main[44]
  let E95 : Fin KB := E93 + E94
  let E96 : Fin KB := E92 - E95
  let E97 : Fin KB := 16 - E26
  let E98 : Fin KB := Main[18] * Main[44]
  let E99 : Fin KB := Main[56] * 65536
  let E100 : Fin KB := Main[52] * Main[44]
  let E101 : Fin KB := E99 + E100
  let E102 : Fin KB := E98 - E101
  let E103 : Fin KB := Main[49] * Main[44]
  let E104 : Fin KB := Main[57] - E103
  let E105 : Fin KB := Main[50] * Main[44]
  let E106 : Fin KB := E105 + Main[53]
  let E107 : Fin KB := Main[58] - E106
  let E108 : Fin KB := Main[51] * Main[44]
  let E109 : Fin KB := E108 + Main[54]
  let E110 : Fin KB := Main[59] - E109
  let E111 : Fin KB := Main[52] * Main[44]
  let E112 : Fin KB := E111 + Main[55]
  let E113 : Fin KB := Main[60] - E112
  let E114 : Fin KB := Main[32] - Main[57]
  let E115 : Fin KB := Main[45] * E114
  let E116 : Fin KB := Main[62] * E115
  let E117 : Fin KB := Main[33] - Main[58]
  let E118 : Fin KB := Main[45] * E117
  let E119 : Fin KB := Main[62] * E118
  let E120 : Fin KB := Main[34] - Main[59]
  let E121 : Fin KB := Main[45] * E120
  let E122 : Fin KB := Main[62] * E121
  let E123 : Fin KB := Main[35] - Main[60]
  let E124 : Fin KB := Main[45] * E123
  let E125 : Fin KB := Main[62] * E124
  let E126 : Fin KB := Main[46] * Main[32]
  let E127 : Fin KB := Main[62] * E126
  let E128 : Fin KB := Main[33] - Main[57]
  let E129 : Fin KB := Main[46] * E128
  let E130 : Fin KB := Main[62] * E129
  let E131 : Fin KB := Main[34] - Main[58]
  let E132 : Fin KB := Main[46] * E131
  let E133 : Fin KB := Main[62] * E132
  let E134 : Fin KB := Main[35] - Main[59]
  let E135 : Fin KB := Main[46] * E134
  let E136 : Fin KB := Main[62] * E135
  let E137 : Fin KB := Main[47] * Main[32]
  let E138 : Fin KB := Main[62] * E137
  let E139 : Fin KB := Main[47] * Main[33]
  let E140 : Fin KB := Main[62] * E139
  let E141 : Fin KB := Main[34] - Main[57]
  let E142 : Fin KB := Main[47] * E141
  let E143 : Fin KB := Main[62] * E142
  let E144 : Fin KB := Main[35] - Main[58]
  let E145 : Fin KB := Main[47] * E144
  let E146 : Fin KB := Main[62] * E145
  let E147 : Fin KB := Main[48] * Main[32]
  let E148 : Fin KB := Main[62] * E147
  let E149 : Fin KB := Main[48] * Main[33]
  let E150 : Fin KB := Main[62] * E149
  let E151 : Fin KB := Main[48] * Main[34]
  let E152 : Fin KB := Main[62] * E151
  let E153 : Fin KB := Main[35] - Main[57]
  let E154 : Fin KB := Main[48] * E153
  let E155 : Fin KB := Main[62] * E154
  let E156 : Fin KB := Main[32] - Main[57]
  let E157 : Fin KB := Main[45] * E156
  let E158 : Fin KB := Main[63] * E157
  let E159 : Fin KB := Main[33] - Main[58]
  let E160 : Fin KB := Main[45] * E159
  let E161 : Fin KB := Main[63] * E160
  let E162 : Fin KB := Main[46] * Main[32]
  let E163 : Fin KB := Main[63] * E162
  let E164 : Fin KB := Main[33] - Main[57]
  let E165 : Fin KB := Main[46] * E164
  let E166 : Fin KB := Main[63] * E165
  let E167 : Fin KB := Main[61] * 65535
  let E168 : Fin KB := E167 - Main[34]
  let E169 : Fin KB := Main[63] * E168
  let E170 : Fin KB := Main[61] * 65535
  let E171 : Fin KB := E170 - Main[35]
  let E172 : Fin KB := Main[63] * E171
  let CS0 : SP1ConstraintList := U16MSBOperation.constraints Main[33] { msb := Main[61] } Main[63]
  let E173 : Fin KB := Main[62] * 6
  let E174 : Fin KB := Main[63] * 21
  let E175 : Fin KB := E173 + E174
  let E176 : Fin KB := Main[62] * 1
  let E177 : Fin KB := Main[63] * 1
  let E178 : Fin KB := E176 + E177
  let E179 : Fin KB := Main[62] * 0
  let E180 : Fin KB := Main[63] * 0
  let E181 : Fin KB := E179 + E180
  let E182 : Fin KB := Main[62] * 51
  let E183 : Fin KB := Main[63] * 59
  let E184 : Fin KB := E182 + E183
  let E185 : Fin KB := 32 * Main[31]
  let E186 : Fin KB := E184 - E185
  let E187 : Fin KB := Main[63] * Main[31]
  let E188 : Fin KB := Main[64] - E187
  let E189 : Fin KB := Main[62] * 8
  let E190 : Fin KB := Main[63] * 8
  let E191 : Fin KB := E189 + E190
  let E192 : Fin KB := 6 * Main[31]
  let E193 : Fin KB := 1 * Main[64]
  let E194 : Fin KB := E192 + E193
  let E195 : Fin KB := E191 - E194
  let E196 : Fin KB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E196, Main[4], Main[5]] 8 E0
  let E197 : Fin KB := Main[1] * 65536
  let E198 : Fin KB := Main[2] + E197
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E198 #v[Main[3], Main[4], Main[5]] E175 #v[E195, E186, E178, E181] #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E0
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

@[simp] def is_sll (Main : Vector (Fin KB) 65) := Main[62] = 1 ∧ Main[31] = 0
@[simp] def is_slli (Main : Vector (Fin KB) 65) := Main[62] = 1 ∧ Main[31] = 1
@[simp] def is_sllw (Main : Vector (Fin KB) 65) := Main[63] = 1 ∧ Main[31] = 0
@[simp] def is_slliw (Main : Vector (Fin KB) 65) := Main[63] = 1 ∧ Main[31] = 1




lemma sll_real (Main : Vector (Fin KB) 65) (h : Main[62] = 1) : is_real Main := by
  simp [is_real, h]
lemma sllw_real (Main : Vector (Fin KB) 65) (h : Main[63] = 1) : is_real Main := by
  simp [is_real, h]

@[simp]
def sp1_op_a {Main : Vector (Fin KB) 65} (_ : (constraints Main).allHold) (_ : is_real Main) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

@[simp]
def sp1_op_b {Main : Vector (Fin KB) 65} (_ : (constraints Main).allHold) (_ : is_real Main) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

@[simp]
def sp1_op_c {Main : Vector (Fin KB) 65} (_ : (constraints Main).allHold) (_ : is_real Main) (_ : Main[31] = 0) : BitVec 5 :=
  BitVec.ofNat 5 Main[21]

@[simp]
def sp1_op_c_imm {Main : Vector (Fin KB) 65} (_ : (constraints Main).allHold) (_ : is_real Main) (_ : Main[31] = 1) : BitVec 6 :=
  BitVec.ofNat 6 Main[21]

@[simp]
def sp1_op_c_imm_w {Main : Vector (Fin KB) 65} (_ : (constraints Main).allHold) (_ : is_real Main) (_ : Main[31] = 1) : BitVec 5 :=
  BitVec.ofNat 5 Main[21]

end ShiftLeft
