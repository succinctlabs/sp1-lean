import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace ShiftLeft

set_option maxHeartbeats 100000000

variable (Main : Vector (Fin BB) 65)
def is_real : Prop := Main[62] = 1 ∨ Main[63] = 1

section constraints

-- Generated Lean code for chip ShiftLeftChip
@[irreducible] def constraints  : SP1ConstraintList :=
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

lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[33] { msb := Main[61] } Main[63]) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[62] + Main[63])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[62] * 6 + Main[63] * 41) #v[Main[64], (Main[62] + Main[63]), 0] #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[62] + Main[63])) ∧
    (Main[62] + Main[63] = 0 ∨ Main[62] + Main[63] = 1) ∧
    (Main[62] = 0 ∨ Main[62] = 1) ∧
    (Main[63] = 0 ∨ Main[63] = 1) ∧
    (Main[36] = 0 ∨ Main[36] = 1) ∧
    (Main[37] = 0 ∨ Main[37] = 1) ∧
    (Main[38] = 0 ∨ Main[38] = 1) ∧
    (Main[39] = 0 ∨ Main[39] = 1) ∧
    (Main[40] = 0 ∨ Main[40] = 1) ∧
    (Main[41] = 0 ∨ Main[41] = 1) ∧
    (¬Main[62] + Main[63] = 0 → ((Main[25] - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16 + Main[41] * 32)) * 1981808641).val < 1024) ∧
    (Main[45] = 0 ∨ Main[40] + Main[41] * 2 * Main[62] = 0) ∧
    (Main[45] = 0 ∨ Main[45] = 1) ∧
    (Main[46] = 0 ∨ Main[40] + Main[41] * 2 * Main[62] = 1) ∧
    (Main[46] = 0 ∨ Main[46] = 1) ∧
    (Main[47] = 0 ∨ Main[40] + Main[41] * 2 * Main[62] = 2) ∧
    (Main[47] = 0 ∨ Main[47] = 1) ∧
    (Main[48] = 0 ∨ Main[40] + Main[41] * 2 * Main[62] = 3) ∧
    (Main[48] = 0 ∨ Main[48] = 1) ∧
    (Main[62] + Main[63] = 0 ∨ Main[45] + Main[46] + Main[47] + Main[48] = 1) ∧
    (Main[42] = (Main[36] + 1) * (Main[37] * 3 + 1)) ∧
    (Main[43] = Main[42] * (Main[38] * 15 + 1)) ∧
    (Main[44] = Main[43] * (Main[39] * 255 + 1)) ∧
    (¬Main[62] + Main[63] = 0 → Main[49].val < 2 ^ ((16 : Fin BB) - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val) ∧
    (¬Main[62] + Main[63] = 0 → Main[53].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val) ∧
    (Main[15] * Main[44] = Main[53] * 65536 + Main[49] * Main[44]) ∧
    (¬Main[62] + Main[63] = 0 → Main[50].val < 2 ^ ((16 : Fin BB) - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val) ∧
    (¬Main[62] + Main[63] = 0 → Main[54].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val) ∧
    (Main[16] * Main[44] = Main[54] * 65536 + Main[50] * Main[44]) ∧
    (¬Main[62] + Main[63] = 0 → Main[51].val < 2 ^ ((16 : Fin BB) - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val) ∧
    (¬Main[62] + Main[63] = 0 → Main[55].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val) ∧
    (Main[17] * Main[44] = Main[55] * 65536 + Main[51] * Main[44]) ∧
    (¬Main[62] + Main[63] = 0 → Main[52].val < 2 ^ ((16 : Fin BB) - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val) ∧
    (¬Main[62] + Main[63] = 0 → Main[56].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val) ∧
    (Main[18] * Main[44] = Main[56] * 65536 + Main[52] * Main[44]) ∧
    (Main[57] = Main[49] * Main[44]) ∧
    (Main[58] = Main[50] * Main[44] + Main[53]) ∧
    (Main[59] = Main[51] * Main[44] + Main[54]) ∧
    (Main[60] = Main[52] * Main[44] + Main[55]) ∧
    (Main[62] = 0 ∨ Main[45] = 0 ∨ Main[32] = Main[57]) ∧
    (Main[62] = 0 ∨ Main[45] = 0 ∨ Main[33] = Main[58]) ∧
    (Main[62] = 0 ∨ Main[45] = 0 ∨ Main[34] = Main[59]) ∧
    (Main[62] = 0 ∨ Main[45] = 0 ∨ Main[35] = Main[60]) ∧
    (Main[62] = 0 ∨ Main[46] = 0 ∨ Main[32] = 0) ∧
    (Main[62] = 0 ∨ Main[46] = 0 ∨ Main[33] = Main[57]) ∧
    (Main[62] = 0 ∨ Main[46] = 0 ∨ Main[34] = Main[58]) ∧
    (Main[62] = 0 ∨ Main[46] = 0 ∨ Main[35] = Main[59]) ∧
    (Main[62] = 0 ∨ Main[47] = 0 ∨ Main[32] = 0) ∧
    (Main[62] = 0 ∨ Main[47] = 0 ∨ Main[33] = 0) ∧
    (Main[62] = 0 ∨ Main[47] = 0 ∨ Main[34] = Main[57]) ∧
    (Main[62] = 0 ∨ Main[47] = 0 ∨ Main[35] = Main[58]) ∧
    (Main[62] = 0 ∨ Main[48] = 0 ∨ Main[32] = 0) ∧
    (Main[62] = 0 ∨ Main[48] = 0 ∨ Main[33] = 0) ∧
    (Main[62] = 0 ∨ Main[48] = 0 ∨ Main[34] = 0) ∧
    (Main[62] = 0 ∨ Main[48] = 0 ∨ Main[35] = Main[57]) ∧
    (Main[63] = 0 ∨ Main[45] = 0 ∨ Main[32] = Main[57]) ∧
    (Main[63] = 0 ∨ Main[45] = 0 ∨ Main[33] = Main[58]) ∧
    (Main[63] = 0 ∨ Main[46] = 0 ∨ Main[32] = 0) ∧
    (Main[63] = 0 ∨ Main[46] = 0 ∨ Main[33] = Main[57]) ∧
    (Main[63] = 0 ∨ Main[61] * 65535 = Main[34]) ∧
    (Main[63] = 0 ∨ Main[61] * 65535 = Main[35]) ∧
    (Main[62] + Main[63] = 0 ∨ Main[64] = Main[31] * (Main[62] * 19 + Main[63] * 27) + (1 - Main[31]) * (Main[62] * 51 + Main[63] * 59))
   := by
  simp [constraints, sub_eq_zero]

end constraints

section field_arithmetic

lemma cancel_mul_65536 { a b c x : Fin BB } (h_dvd : (x : ℕ) ∣ 65536) : a * x = b * 65536 + c * x → a = b * ((65536 : ℕ) / (x : ℕ)) + c
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

@[simp] def is_sll := Main[62] = 1 ∧ Main[31] = 0
@[simp] def is_sllw := Main[63] = 1 ∧ Main[31] = 0
@[simp] def is_slli := Main[62] = 1 ∧ Main[31] = 1
@[simp] def is_slliw := Main[63] = 1 ∧ Main[31] = 1

lemma single_op : List.Forall SP1Constraint.toProp (constraints Main) →
  (Main[62] = 1 → Main[63] = 0) ∧
  (Main[63] = 1 → Main[62] = 0)
   := by

  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_msb, cpu, alu, one_of_ops, b_sll, b_sllw, rest ⟩ := cstrs
  clear *- b_sll b_sllw one_of_ops
  aesop

end opcodes

section is_real

lemma sll_real : Main[62] = 1 → is_real Main := by simp [is_real]; aesop
lemma sllw_real : Main[63] = 1 → is_real Main := by simp [is_real]; aesop

end is_real

section bounds

lemma bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let imm := Main[31]
  Main[6] < 32 ∧ Main[14] < 32 ∧ (imm = 0 → Main[21] < 32) ∧ Main[3] < 65536 ∧
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] ∧
  (imm = 1 →
    (Main[21] = Main[25] ∧ Main[26] = 0 ∧ Main[27] = 0 ∧ Main[28] = 0 ∧
      ((Main[62] = 1 → Main[25] < 64) ∧
       (Main[63] = 1 → Main[25] < 32)))) ∧
  (Main[6] = 0 → Main[32] = 0 ∧ Main[33] = 0 ∧ Main[34] = 0 ∧ Main[35] = 0)
  := by
  intro cstrs real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨ h_msb, cpu, alu, one_of_ops, b_sll, b_sllw, rest ⟩ := cstrs
  clear h_msb cpu rest
  simp [is_real] at real
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  . obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19 ⟩ := alu; simp_all
    by_cases sll : Main[62] = 0
    . by_cases sllw : Main[63] = 0
      . clear *- real sll sllw; aesop
      . have : Main[62] = 0 := by
          clear *- real b_sll b_sllw sll sllw one_of_ops
          aesop
        simp_all [Opcode.ofNat, Nat.beq, Nat.ble]
        split_ands
        . rcases b_imm <;> simp_all
        . rcases b_imm <;> simp_all
          apply Word.isU64_of_cases <;> simp; omega
        . aesop
    . have : Main[63] = 0 := by
        clear *- real b_sll b_sllw sll one_of_ops
        aesop
      simp_all [Opcode.ofNat, Nat.beq, Nat.ble]
      split_ands
      . rcases b_imm <;> simp_all
      . rcases b_imm <;> simp_all
        apply Word.isU64_of_cases <;> simp; omega
      . aesop
  . clear alu; aesop

end bounds

section operands

@[simp]
def sp1_op_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[6] ?_
  show Main[6] < 32
  have := bounds Main cstrs real
  tauto

@[simp]
def sp1_op_b : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[14] ?_
  show Main[14] < 32
  have := bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 0 → BitVec 5 := by
  intro cstrs real imm
  refine BitVec.ofNatLT Main[21] ?_
  show Main[21] < 32
  have := bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c_imm : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[62] = 1 → BitVec 6 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have ⟨ _, _, _, _, _, _, h_imm, _ ⟩ := bounds Main cstrs real
  simp_all
  have ⟨ _, _, _, _, _ ⟩ := h_imm
  tauto

@[simp]
def sp1_op_c_imm_w : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[63] = 1 → BitVec 5 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have ⟨ _, _, _, _, _, _, h_imm, _ ⟩ := bounds Main cstrs real
  simp_all
  have ⟨ _, _, _, _, _ ⟩ := h_imm
  tauto

end operands

section sll

lemma spec.sll (h : is_sll Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLL
  := by
    intro cstrs
    obtain ⟨ eq_sll, eq_imm ⟩ := h
    have ⟨ h0, h1, h2, hpc, is_U64_b, is_U64_c, h3, h4 ⟩ := bounds Main cstrs (sll_real Main eq_sll)
    clear h0 h1 h2 h3 h4
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨ sop_1, sop_2 ⟩ := single_op Main cstrs

    rw [allHold_constraints_iff] at cstrs

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
    set cb0 := Main[36]
    set cb1 := Main[37]
    set cb2 := Main[38]
    set cb3 := Main[39]
    set cb4 := Main[40]
    set cb5 := Main[41]
    set v01 := Main[42]
    set v012 := Main[43]
    set v0123 := Main[44]
    set su160 := Main[45]
    set su161 := Main[46]
    set su162 := Main[47]
    set su163 := Main[48]
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
    set msb := Main[61]
    set sll := Main[62]
    set sllw := Main[63]

    obtain ⟨ h_msb_a1, cpu, alu, one_of_ops,
             b_sll, b_sllw,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
             lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05,
             eq_m64 ⟩ := cstrs
    clear h_msb_a1 cpu alu

    simp_all

    rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

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

    rw [this]; clear this
    rw [Word.toBitVec64_toNat (w := #v[b0, b1, b2, b3]) (by apply Word.isU64_of_cases <;> simp <;> assumption)]
    simp [Word.toNat]

    -- 64-way case split
    rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
    rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
    simp_all <;>
    (try apply cancel_mul_65536 (by simp) at h_b0_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b1_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b2_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b3_dec) <;>
    simp_all

    all_goals {
      rw [Word.toBitVec64_toNat]
      . simp [Word.toNat]
        try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
        repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
        omega
      . apply Word.isU64_of_cases <;> simp [Fin.val_add, Fin.val_mul] <;>
        (repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]) <;>
        omega
    }

end sll

section slli

lemma spec.slli (h : is_slli Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLL
  := by
    intro cstrs
    obtain ⟨ eq_sll, eq_imm ⟩ := h
    have ⟨ h0, h1, h2, hpc, is_U64_b, is_U64_c, imm_zeros, h3 ⟩ := bounds Main cstrs (sll_real Main eq_sll)
    clear h0 h1 h2 h3
    rw [eq_imm] at imm_zeros; simp_all
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3, lt_c0, h0 ⟩ := imm_zeros
    obtain ⟨ sop_1, sop_2 ⟩ := single_op Main cstrs

    rw [allHold_constraints_iff] at cstrs

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
    set cb0 := Main[36]
    set cb1 := Main[37]
    set cb2 := Main[38]
    set cb3 := Main[39]
    set cb4 := Main[40]
    set cb5 := Main[41]
    set v01 := Main[42]
    set v012 := Main[43]
    set v0123 := Main[44]
    set su160 := Main[45]
    set su161 := Main[46]
    set su162 := Main[47]
    set su163 := Main[48]
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
    set msb := Main[61]
    set sll := Main[62]
    set sllw := Main[63]

    obtain ⟨ h_msb_a1, cpu, alu, one_of_ops,
             b_sll, b_sllw,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
             lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05,
             eq_m64 ⟩ := cstrs
    clear h_msb_a1 cpu alu

    simp_all

    rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

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
    rw [Word.toBitVec64_toNat (w := #v[b0, b1, b2, b3]) (by apply Word.isU64_of_cases <;> simp <;> assumption)]
    simp [Word.toNat]

    -- 64-way case split
    rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
    rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
    simp_all <;>
    (try apply cancel_mul_65536 (by simp) at h_b0_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b1_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b2_dec) <;>
    (try apply cancel_mul_65536 (by simp) at h_b3_dec) <;>
    simp_all

    all_goals {
      rw [Word.toBitVec64_toNat]
      . simp [Word.toNat]
        try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
        repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
        omega
      . apply Word.isU64_of_cases <;> simp [Fin.val_add, Fin.val_mul] <;>
        (repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]) <;>
        omega
    }

end slli

section sllw

lemma spec.sllw (h : is_sllw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLLW
  := by
    intro cstrs
    obtain ⟨ eq_sllw, eq_imm ⟩ := h
    have ⟨ h0, h1, h2, hpc, is_U64_b, is_U64_c, h3, h4 ⟩ := bounds Main cstrs (sllw_real Main eq_sllw)
    clear h0 h1 h2 h3 h4
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ c0_16, c1_16, c2_16, c3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨ sop_1, sop_2 ⟩ := single_op Main cstrs

    rw [allHold_constraints_iff] at cstrs

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
    set cb0 := Main[36]
    set cb1 := Main[37]
    set cb2 := Main[38]
    set cb3 := Main[39]
    set cb4 := Main[40]
    set cb5 := Main[41]
    set v01 := Main[42]
    set v012 := Main[43]
    set v0123 := Main[44]
    set su160 := Main[45]
    set su161 := Main[46]
    set su162 := Main[47]
    set su163 := Main[48]
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
    set msb := Main[61]
    set sll := Main[62]
    set sllw := Main[63]

    obtain ⟨ h_msb_a1, cpu, alu, one_of_ops,
             b_sll, b_sllw,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
             lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05,
             eq_m64 ⟩ := cstrs
    clear cpu alu

    simp_all

    have is_U32_b : HWord.isU32 #v[ b0, b1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_c : HWord.isU32 #v[ c0, c1 ] := by apply HWord.isU32_of_cases <;> assumption

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

    have h_isU32_a : HWord.isU32 #v[ a0, a1 ] := by
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
      rcases b_cb3 <;> rcases b_cb4 <;> simp_all <;>
      apply HWord.isU32_of_cases <;> simp_all [Fin.val_add, Fin.val_mul] <;>
      (repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]) <;>
      omega

    have ⟨ _, _ ⟩ := HWord.lt_cases_of_isU32 h_isU32_a

    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      rw [← w_04] at *
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      . unfold HWord.isNegative; split_ifs <;> simp_all; omega
      . congr; rw [HWord.isNegative_msb h_isU32_a]

    . suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = (HWord.toBitVec32 #v[b0, b1] <<< (c0.val % 32))
      . rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      . rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        rw [HWord.toBitVec32_toNat h_isU32_a, HWord.toBitVec32_toNat is_U32_b]
        rw [this]; clear this h_a3

        cases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
        rcases b_cb3 <;> rcases b_cb4 <;> simp_all

        all_goals {
          (try apply cancel_mul_65536 (by simp) at h_b0_dec)
          (try apply cancel_mul_65536 (by simp) at h_b1_dec)
          (try apply cancel_mul_65536 (by simp) at h_b2_dec)
          (try apply cancel_mul_65536 (by simp) at h_b3_dec)
          simp_all [HWord.toNat]
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          omega
        }

end sllw

section slliw

lemma spec.slliw (h : is_slliw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLLW
  := by
    intro cstrs
    obtain ⟨ eq_sllw, eq_imm ⟩ := h
    have ⟨ h0, h1, h2, hpc, is_U64_b, is_U64_c, imm_zeros, h3 ⟩ := bounds Main cstrs (sllw_real Main eq_sllw)
    clear h0 h1 h2 h3
    rw [eq_imm] at imm_zeros; simp_all
    obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3, lt_c0, h0 ⟩ := imm_zeros
    obtain ⟨ sop_1, sop_2 ⟩ := single_op Main cstrs

    rw [allHold_constraints_iff] at cstrs

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
    set cb0 := Main[36]
    set cb1 := Main[37]
    set cb2 := Main[38]
    set cb3 := Main[39]
    set cb4 := Main[40]
    set cb5 := Main[41]
    set v01 := Main[42]
    set v012 := Main[43]
    set v0123 := Main[44]
    set su160 := Main[45]
    set su161 := Main[46]
    set su162 := Main[47]
    set su163 := Main[48]
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
    set msb := Main[61]
    set sll := Main[62]
    set sllw := Main[63]

    obtain ⟨ h_msb_a1, cpu, alu, one_of_ops,
             b_sll, b_sllw,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
             lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05,
             eq_m64 ⟩ := cstrs
    clear cpu alu

    simp_all

    have is_U32_b : HWord.isU32 #v[ b0, b1 ] := by apply HWord.isU32_of_cases <;> assumption
    have is_U32_c : HWord.isU32 #v[ c0, 0 ] := by apply HWord.isU32_of_cases <;> simp; omega

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

    have h_isU32_a : HWord.isU32 #v[ a0, a1 ] := by
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
      rcases b_cb3 <;> rcases b_cb4 <;> simp_all <;>
      apply HWord.isU32_of_cases <;> simp_all [Fin.val_add, Fin.val_mul] <;>
      (repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]) <;>
      omega

    have ⟨ _, _ ⟩ := HWord.lt_cases_of_isU32 h_isU32_a

    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      rw [← w_04] at *
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      . unfold HWord.isNegative; split_ifs <;> simp_all; omega
      . congr; rw [HWord.isNegative_msb h_isU32_a]

    . suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = (HWord.toBitVec32 #v[b0, b1] <<< (c0.val % 32))
      . rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      . rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        rw [HWord.toBitVec32_toNat h_isU32_a, HWord.toBitVec32_toNat is_U32_b]
        rw [this]; clear this h_a3

        cases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
        rcases b_cb3 <;> rcases b_cb4 <;> simp_all

        all_goals {
          (try apply cancel_mul_65536 (by simp) at h_b0_dec)
          (try apply cancel_mul_65536 (by simp) at h_b1_dec)
          (try apply cancel_mul_65536 (by simp) at h_b2_dec)
          (try apply cancel_mul_65536 (by simp) at h_b3_dec)
          simp_all [HWord.toNat]
          try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          omega
        }

end slliw

end ShiftLeft
