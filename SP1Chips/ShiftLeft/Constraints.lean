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
  let CS2 : SP1ConstraintList F := ALUTypeReader.constraints Main[0] E198 #v[Main[3], Main[4], Main[5]] E175 #v[E195, E186, E178, E181] #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E0
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

lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[33] { msb := Main[61] } Main[63]) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[62] + Main[63])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[62] * 6 + Main[63] * 21) (
      #v[Main[62] * 8 + Main[63] * 8 - (6 * Main[31] + Main[64]), Main[62] * 51 + Main[63] * 59 - 32 * Main[31],
          Main[62] + Main[63], 0]
    ) #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[62] + Main[63])) ∧
    (Main[62] + Main[63] = 0 ∨ Main[62] + Main[63] = 1) ∧
    (Main[62] = 0 ∨ Main[62] = 1) ∧
    (Main[63] = 0 ∨ Main[63] = 1) ∧
    (Main[36] = 0 ∨ Main[36] = 1) ∧
    (Main[37] = 0 ∨ Main[37] = 1) ∧
    (Main[38] = 0 ∨ Main[38] = 1) ∧
    (Main[39] = 0 ∨ Main[39] = 1) ∧
    (Main[40] = 0 ∨ Main[40] = 1) ∧
    (Main[41] = 0 ∨ Main[41] = 1) ∧
    (¬Main[62] + Main[63] = 0 → ((Main[25] - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8 + Main[40] * 16 + Main[41] * 32)) * ((64 : Fin KB)⁻¹)).val < 1024) ∧
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
    (¬Main[62] + Main[63] = 0 → Main[49].val < 2 ^ ((16 : Fin KB) - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val) ∧
    (¬Main[62] + Main[63] = 0 → Main[53].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val) ∧
    (Main[15] * Main[44] = Main[53] * 65536 + Main[49] * Main[44]) ∧
    (¬Main[62] + Main[63] = 0 → Main[50].val < 2 ^ ((16 : Fin KB) - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val) ∧
    (¬Main[62] + Main[63] = 0 → Main[54].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val) ∧
    (Main[16] * Main[44] = Main[54] * 65536 + Main[50] * Main[44]) ∧
    (¬Main[62] + Main[63] = 0 → Main[51].val < 2 ^ ((16 : Fin KB) - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val) ∧
    (¬Main[62] + Main[63] = 0 → Main[55].val < 2 ^ (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8).val) ∧
    (Main[17] * Main[44] = Main[55] * 65536 + Main[51] * Main[44]) ∧
    (¬Main[62] + Main[63] = 0 → Main[52].val < 2 ^ ((16 : Fin KB) - (Main[36] + Main[37] * 2 + Main[38] * 4 + Main[39] * 8)).val) ∧
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
    Main[64] = Main[63] * Main[31] ∧
    Main[13] = 0
   := by
  simp [constraints, sub_eq_zero]

section field_arithmetic

lemma cancel_mul_65536 {a b c x : Fin KB} (h_dvd : (x : ℕ) ∣ 65536) : a * x = b * 65536 + c * x → a = b * ((65536 : ℕ) / (x : ℕ)) + c
  := by
  obtain ⟨z, h_eq⟩ := h_dvd; rw [h_eq]
  have x_pos : 0 < (x : ℕ) := by nlinarith
  have xz_BB : (x : ℕ) * z < 2130706433 := by nlinarith
  have z_BB : z < 2130706433 := by nlinarith
  have h_eq_BB : 65536 = x * z := by
    apply Fin.ext
    simp [Fin.mul_def, Nat.mod_eq_of_lt z_BB, Nat.mod_eq_of_lt xz_BB]
    have hz : ((z : Fin 2130706433) : ℕ) = z := Nat.mod_eq_of_lt z_BB
    rw [hz, Nat.mod_eq_of_lt xz_BB]
    exact h_eq
  rw [h_eq_BB]
  rw [mul_comm x z, ← mul_assoc, ← right_distrib]
  intro eq; apply mul_right_cancel₀ (by omega) at eq; rw [eq]
  congr
  rw [Fin.ext_iff]
  change z % 2130706433 = (↑x * z % 2130706433 / (x.val % 2130706433))
  rw [Nat.mod_eq_of_lt z_BB, Nat.mod_eq_of_lt xz_BB, Nat.mod_eq_of_lt x.isLt,
    Nat.mul_div_cancel_left _ x_pos]

lemma is_mod_64 {c0 m : Fin KB} : m < 64 → c0 < 65536 → ((c0 - m) * 2097414145).val < 1024 → c0.val % 64 = m := by
  simp [Fin.sub_def, Fin.mul_def, Fin.lt_def]; ring_nf
  intro hm hc hdiff
  suffices : (BitVec.ofNat 64 c0.val) % 64#64 = BitVec.ofNat 64 m.val
  · simp [BitVec.toNat_eq] at this
    repeat rw [Nat.mod_eq_of_lt (b := 18446744073709551616) (by omega)] at this
    assumption
  · suffices : ((2130706433 - BitVec.ofNat 64 ↑m) * BitVec.ofNat 64 2097414145 + BitVec.ofNat 64 ↑c0 * 2097414145#64) % 2130706433#64 < 1024#64
    · clear hdiff
      have : BitVec.ofNat 64 c0.val < 65536 := by simp; omega
      have : BitVec.ofNat 64 m.val < 64 := by simp; omega
      clear hm
      trans (BitVec.ofNat 64 ↑c0) &&& 63#64
      · bv_decide
      · bv_decide
    · rw [← BitVec.ult_iff_lt]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul]
      simp [-BitVec.toNat_sub]
      rw [BitVec.toNat_sub_of_le] <;> simp
      · repeat rw [Nat.mod_eq_of_lt (b := 18446744073709551616) (by omega)]
        assumption
      · omega

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
  obtain ⟨h_msb, cpu, alu, one_of_ops, b_sll, b_sllw, rest⟩ := cstrs
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
  obtain ⟨h_msb, cpu, alu, one_of_ops, b_sll, b_sllw, rest⟩ := cstrs
  clear h_msb cpu rest
  simp [is_real] at real
  rw [ALUTypeReader.allHold_constraints_iff_is_real] at alu
  · obtain ⟨h1, h2, h3, _, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := alu; simp_all
    by_cases sll : Main[62] = 0
    · by_cases sllw : Main[63] = 0
      · clear *- real sll sllw; aesop
      · have : Main[62] = 0 := by
          clear *- real b_sll b_sllw sll sllw one_of_ops
          aesop
        simp_all [Opcode.ofNat, Nat.beq, Nat.ble]
        split_ands
        · rcases b_imm <;> simp_all
        · rcases b_imm <;> simp_all
          apply Word.isU64_of_cases <;> simp; omega
        · aesop
        · intro h6; exact h18.1 (by have := h5.mpr h6; omega)
    · have : Main[63] = 0 := by
        clear *- real b_sll b_sllw sll one_of_ops
        aesop
      simp_all [Opcode.ofNat, Nat.beq, Nat.ble]
      split_ands
      · rcases b_imm <;> simp_all
      · rcases b_imm <;> simp_all
        apply Word.isU64_of_cases <;> simp; omega
      · aesop
      · intro h6; exact h18.1 (by have := h5.mpr h6; omega)
  · clear alu; aesop

end bounds

section operands

@[simp]
def sp1_op_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[6] ?_
  change Main[6] < 32
  have := bounds Main cstrs real
  tauto

@[simp]
def sp1_op_b : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[14] ?_
  change Main[14] < 32
  have := bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 0 → BitVec 5 := by
  intro cstrs real imm
  refine BitVec.ofNatLT Main[21] ?_
  change Main[21] < 32
  have := bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c_imm : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[62] = 1 → BitVec 6 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have ⟨_, _, _, _, _, _, h_imm, _⟩ := bounds Main cstrs real
  simp_all
  have ⟨_, _, _, _, _⟩ := h_imm
  tauto

@[simp]
def sp1_op_c_imm_w : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[63] = 1 → BitVec 5 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have ⟨_, _, _, _, _, _, h_imm, _⟩ := bounds Main cstrs real
  simp_all
  have ⟨_, _, _, _, _⟩ := h_imm
  tauto

end operands

section sll

lemma spec.sll (h : is_sll Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLL
  := by
    have _ := h
    intro cstrs
    obtain ⟨eq_sll, eq_imm⟩ := h
    have ⟨h0, h1, h2, hpc, is_U64_b, is_U64_c, h3, h4⟩ := bounds Main cstrs (sll_real Main eq_sll)
    clear h0 h1 h2 h3 h4
    obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨c0_16, c1_16, c2_16, c3_16⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨sop_1, sop_2⟩ := single_op Main cstrs
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
    obtain ⟨h_msb_a1, cpu, alu, one_of_ops,
             b_sll, b_sllw,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
             lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05,
             eq_m64, h13⟩ := cstrs
    clear h_msb_a1 cpu alu
    simp_all
    rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have : ((Word.toBitVec64 #v[c0, c1, c2, c3]).toNat % 64) = c0.val % 64 := by
      rw [Word.toBitVec64_toNat is_U64_c]; simp [Word.toNat]
      omega
    rw [this]; clear this
    have : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · omega
      · exact diff
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
      · simp [Word.toNat]
        try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
        repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
        omega
      · apply Word.isU64_of_cases <;> simp [Fin.val_add, Fin.val_mul] <;>
        (repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]) <;>
        omega
    }

end sll

section slli

lemma spec.slli (h : is_slli Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLL
  := by
    have _ := h
    intro cstrs
    obtain ⟨eq_sll, eq_imm⟩ := h
    have ⟨h0, h1, h2, hpc, is_U64_b, is_U64_c, imm_zeros, h3⟩ := bounds Main cstrs (sll_real Main eq_sll)
    clear h0 h1 h2 h3
    rw [eq_imm] at imm_zeros; simp_all
    obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨eq_c0, eq_c1, eq_c2, eq_c3, lt_c0, h0⟩ := imm_zeros
    obtain ⟨sop_1, sop_2⟩ := single_op Main cstrs
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
    obtain ⟨h_msb_a1, cpu, alu, one_of_ops,
             b_sll, b_sllw,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
             lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05,
             eq_m64⟩ := cstrs
    clear h_msb_a1 cpu alu
    simp_all
    rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have : ((Word.toBitVec64 #v[c0, 0, 0, 0]).toNat % 64) = c0.val % 64 := by
      rw [Word.toBitVec64_toNat is_U64_c]; simp [Word.toNat]
    rw [this]; clear this
    have : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · omega
      · exact diff
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
      · simp [Word.toNat]
        try simp [Fin.val_add, Fin.val_mul] at b0_16 b1_16 b2_16 b3_16 ⊢
        repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
        omega
      · apply Word.isU64_of_cases <;> simp [Fin.val_add, Fin.val_mul] <;>
        (repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]) <;>
        omega
    }

end slli

section sllw

lemma spec.sllw (h : is_sllw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLLW
  := by
    have _ := h
    intro cstrs
    obtain ⟨eq_sllw, eq_imm⟩ := h
    have ⟨h0, h1, h2, hpc, is_U64_b, is_U64_c, h3, h4⟩ := bounds Main cstrs (sllw_real Main eq_sllw)
    clear h0 h1 h2 h3 h4
    obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨c0_16, c1_16, c2_16, c3_16⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨sop_1, sop_2⟩ := single_op Main cstrs
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
    obtain ⟨h_msb_a1, cpu, alu, one_of_ops,
             b_sll, b_sllw,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
             lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05,
             eq_m64⟩ := cstrs
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
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · omega
      · exact diff
    clear diff
    have : c0.val % 32 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
      trans (c0.val % 64) % 32
      · omega
      · rw [c0_mod_64]
        clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
    clear c0_mod_64
    have h_isU32_a : HWord.isU32 #v[ a0, a1 ] := by
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
      rcases b_cb3 <;> rcases b_cb4 <;> simp_all <;>
      apply HWord.isU32_of_cases <;> simp_all [Fin.val_add, Fin.val_mul] <;>
      (repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]) <;>
      omega
    have ⟨_, _⟩ := HWord.lt_cases_of_isU32 h_isU32_a
    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      rw [← w_04] at *
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      · unfold HWord.isNegative; split_ifs <;> simp_all; omega
      · congr; rw [HWord.isNegative_msb h_isU32_a]
    · suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = (HWord.toBitVec32 #v[b0, b1] <<< (c0.val % 32))
      · rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      · rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
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
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          omega
        }

end sllw

section slliw

lemma spec.slliw (h : is_slliw Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPEW_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SLLW
  := by
    have _ := h
    intro cstrs
    obtain ⟨eq_sllw, eq_imm⟩ := h
    have ⟨h0, h1, h2, hpc, is_U64_b, is_U64_c, imm_zeros, h3⟩ := bounds Main cstrs (sllw_real Main eq_sllw)
    clear h0 h1 h2 h3
    rw [eq_imm] at imm_zeros; simp_all
    obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨eq_c0, eq_c1, eq_c2, eq_c3, lt_c0, h0⟩ := imm_zeros
    obtain ⟨sop_1, sop_2⟩ := single_op Main cstrs
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
    obtain ⟨h_msb_a1, cpu, alu, one_of_ops,
             b_sll, b_sllw,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
             lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05,
             eq_m64⟩ := cstrs
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
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · omega
      · exact diff
    clear diff
    have : c0.val % 32 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
      trans (c0.val % 64) % 32
      · omega
      · rw [c0_mod_64]
        clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
    clear c0_mod_64
    have h_isU32_a : HWord.isU32 #v[ a0, a1 ] := by
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
      rcases b_cb3 <;> rcases b_cb4 <;> simp_all <;>
      apply HWord.isU32_of_cases <;> simp_all [Fin.val_add, Fin.val_mul] <;>
      (repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]) <;>
      omega
    have ⟨_, _⟩ := HWord.lt_cases_of_isU32 h_isU32_a
    have h_a3 : a3 = if (HWord.toBitVec32 #v[a0, a1]).msb = true then 65535 else 0 := by
      simp_all
      rw [← w_04] at *
      have h_msb := U16MSBOperation.spec (by assumption) h_msb_a1
      simp at h_msb; rw [h_msb]
      trans (if HWord.isNegative #v[a0, a1] then 65535 else 0)
      · unfold HWord.isNegative; split_ifs <;> simp_all; omega
      · congr; rw [HWord.isNegative_msb h_isU32_a]
    · suffices hw_shift : HWord.toBitVec32 #v[ a0, a1 ] = (HWord.toBitVec32 #v[b0, b1] <<< (c0.val % 32))
      · rw [← hw_shift]
        rw [HWord.sign_extend_32_to_64_msb]
        simp_all; congr
      · rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
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
          repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
          omega
        }

end slliw

section poly_helpers

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

@[simp] def is_real_poly (Main : Vector (ZMod p) 65) : Prop := Main[62] = 1 ∨ Main[63] = 1

@[simp] def is_sll_poly (Main : Vector (ZMod p) 65) := Main[62] = 1 ∧ Main[31] = 0
@[simp] def is_sllw_poly (Main : Vector (ZMod p) 65) := Main[63] = 1 ∧ Main[31] = 0
@[simp] def is_slli_poly (Main : Vector (ZMod p) 65) := Main[62] = 1 ∧ Main[31] = 1
@[simp] def is_slliw_poly (Main : Vector (ZMod p) 65) := Main[63] = 1 ∧ Main[31] = 1

omit [Fact (2 ^ 17 < p)] in
lemma sll_real_poly (Main : Vector (ZMod p) 65) : Main[62] = 1 → is_real_poly Main := by
  intro h; exact Or.inl h

omit [Fact (2 ^ 17 < p)] in
lemma sllw_real_poly (Main : Vector (ZMod p) 65) : Main[63] = 1 → is_real_poly Main := by
  intro h; exact Or.inr h

-- Polymorphic counterpart of `cancel_mul_65536`. Same algebraic content
-- (cancel `(k : ZMod p)` from both sides given `0 < k ∣ 65536`), but stays
-- in `ZMod p` arithmetic via `mul_right_cancel₀` rather than the concrete
-- version's `Fin.ext`/`Fin.mul_def` Nat reasoning. `(k : ZMod p) ≠ 0` holds
-- because `k ≤ 65536 < 2^17 < p`.
lemma cancel_mul_65536_poly {a b c : ZMod p} {k : ℕ}
    (h_dvd : k ∣ 65536) (h_pos : 0 < k) :
    a * (k : ZMod p) = b * 65536 + c * (k : ZMod p) →
    a = b * ((65536 / k : ℕ) : ZMod p) + c := by
  intro h
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 65536 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have hk_le : k ≤ 65536 := Nat.le_of_dvd (by omega) h_dvd
  have hk_lt_p : k < p := by omega
  obtain ⟨z, hz_eq⟩ := h_dvd
  have hk_ne_zero : (k : ZMod p) ≠ 0 := by
    intro h0
    have hv : (k : ZMod p).val = 0 := by rw [h0]; exact ZMod.val_zero
    rw [ZMod.val_natCast_of_lt hk_lt_p] at hv; omega
  have hkz_eq_zmod : (k : ZMod p) * (z : ZMod p) = (65536 : ZMod p) := by
    have hcast : ((k * z : ℕ) : ZMod p) = ((65536 : ℕ) : ZMod p) :=
      congrArg ((↑) : ℕ → ZMod p) hz_eq.symm
    push_cast at hcast; exact hcast
  have hdiv : 65536 / k = z := by rw [hz_eq]; exact Nat.mul_div_cancel_left z h_pos
  rw [hdiv]
  have h2 : a * (k : ZMod p) = (b * (z : ZMod p) + c) * (k : ZMod p) := by
    rw [add_mul, mul_assoc, mul_comm ((z : ZMod p)) ((k : ZMod p)), hkz_eq_zmod, h]
  exact mul_right_cancel₀ hk_ne_zero h2

set_option maxHeartbeats 1600000 in
-- Polymorphic counterpart of `single_op`. Two-way mutual exclusion of the
-- sll/sllw flags. The `Main[62]=Main[63]=1` case is ruled out by the
-- `Main[62]+Main[63] ∈ {0,1}` binarity constraint together with
-- `(2 : ZMod p) ∉ {0,1}` (which holds under `[Fact (2^17 < p)]`).
lemma single_op_poly (Main : Vector (ZMod p) 65)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main)) :
    (Main[62] = 1 → Main[63] = 0) ∧ (Main[63] = 1 → Main[62] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h2_ne : ((2 : ℕ) : ZMod p) ≠ 0 ∧ ((2 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((2 : ℕ) : ZMod p).val = 2 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  have h2_ne_zero : (1 + 1 : ZMod p) ≠ 0 := fun h => h2_ne.1 (by push_cast; linear_combination h)
  have h2_ne_one  : (1 + 1 : ZMod p) ≠ 1 := fun h => h2_ne.2 (by push_cast; linear_combination h)
  simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly] at cstrs
  obtain ⟨_h_msb, _cpu, _alu, one_of_ops, b_sll, b_sllw, _rest⟩ := cstrs
  refine ⟨?_, ?_⟩ <;> intro h <;>
    rcases b_sll with h_sll | h_sll <;> rcases b_sllw with h_sllw | h_sllw <;>
    simp_all [h2_ne_zero, h2_ne_one]

-- Polymorphic counterpart of `is_mod_64`. Same conclusion (`c0.val % 64 = m.val`),
-- with the lookup-side bound `((c0 - m) * (64 : ZMod p)⁻¹).val < 1024` replacing
-- the `Fin KB` form. Proof: derive `c0 = 64 * q + m` in `ZMod p`, lift to ℕ
-- using the size budget `64 * 1023 + 63 < 2^17 < p`, then take mod 64.
-- (Doesn't need `c0.val < 65536` — the size budget on `q` and `m` suffices.)
lemma is_mod_64_poly {c0 m : ZMod p} (hm : m.val < 64)
    (hdiff : ((c0 - m) * (64 : ZMod p)⁻¹).val < 1024) :
    c0.val % 64 = m.val := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h64_val : (64 : ZMod p).val = 64 :=
    ZMod.val_natCast_of_lt (show (64 : ℕ) < p from by omega)
  have h64_ne : (64 : ZMod p) ≠ 0 := by
    intro h0
    have := congrArg ZMod.val h0
    rw [h64_val, ZMod.val_zero] at this; omega
  set q := (c0 - m) * (64 : ZMod p)⁻¹ with hq_def
  have h_q_lt : q.val < 1024 := hdiff
  have h_eq : (64 : ZMod p) * q = c0 - m := by
    rw [hq_def, show (64 : ZMod p) * ((c0 - m) * (64 : ZMod p)⁻¹) =
      (c0 - m) * ((64 : ZMod p) * (64 : ZMod p)⁻¹) from by ring,
      mul_inv_cancel₀ h64_ne, mul_one]
  have h_c0 : c0 = 64 * q + m := by linear_combination -h_eq
  have h_64q_val : (64 * q : ZMod p).val = 64 * q.val := by
    rw [ZMod.val_mul, h64_val, Nat.mod_eq_of_lt]; omega
  have h_sum_val : (64 * q + m : ZMod p).val = 64 * q.val + m.val := by
    rw [ZMod.val_add, h_64q_val, Nat.mod_eq_of_lt]; omega
  have hc0_eq : c0.val = 64 * q.val + m.val := by rw [h_c0, h_sum_val]
  omega

set_option maxHeartbeats 4000000 in
-- Polymorphic counterpart of the `bounds` lemma's most-load-bearing exits:
-- `Main[3].val < 65536` (PC low limb), `Word.isU64_poly` for both op_b and
-- op_c reads. Mirrors Mul's `ops_U64_b_c_poly` design — minimum extraction
-- from `cstrs` to support the spec lemmas; finer-grained register bounds
-- (`Main[6] < 32` etc.) and I-type immediate consequences are derived
-- inline at use sites.
lemma bounds_poly (Main : Vector (ZMod p) 65)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main))
    (real : is_real_poly Main) :
    Main[3].val < 65536 ∧
    Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64_poly #v[Main[25], Main[26], Main[27], Main[28]] := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  obtain ⟨single_62, single_63⟩ := single_op_poly Main cstrs
  have h_is_real_eq_one : Main[62] + Main[63] = 1 := by
    rcases real with h62 | h63
    · rw [h62, single_62 h62]; ring
    · rw [h63, single_63 h63]; ring
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append,
    List.Forall, SP1Constraint.toProp_poly_assertZero, sub_eq_zero] at cstrs
  obtain ⟨⟨⟨_h_msb, _cpu⟩, alu⟩, _rest⟩ := cstrs
  rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at alu
  -- Destructure ALU iff RHS (19 conjuncts; we only need PC bound, U64_b,
  -- and the imm_c=0 → U64_c block).
  obtain ⟨_trusted_instr_prop, _h_op_a_lt, _h_op_b_lt, h_c_bnds,
          _h_a0_bool, _h_a0_iff,
          b_imm_c, _pc_mod, h3_lt, _h4_lt, _h5_lt,
          _h12_lt, _h20_lt, _h_clk_b, _h_clk_a,
          _is_U64_a, is_U64_b,
          h_imm_c_zero_block, _h_op_a_0_zero, h_imm_c_one_block⟩ := alu
  have h65536 : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h3_lt_nat : Main[3].val < 65536 := by
    have : Main[3].val < (65536 : ZMod p).val := h3_lt
    rwa [h65536] at this
  refine ⟨h3_lt_nat, is_U64_b, ?_⟩
  -- Word.isU64_poly #v[Main[25..28]]:
  -- - imm_c = 0 (R-type): comes from `h_imm_c_zero_block` (U64 conjunct of
  --   the imm_c=0 → block — op_c_memory.prev_value is loaded normally).
  -- - imm_c = 1 (I-type-shift): `h_imm_c_one_block` says Main[25..28] copies
  --   op_c[0..3], which are bounded by `h_c_bnds : op_c[i] < 65536`. Combine
  --   via `Word.isU64_of_cases_poly`.
  rcases b_imm_c with h_imm_zero | h_imm_one
  · exact (h_imm_c_zero_block h_imm_zero).2.2
  · obtain ⟨h25, h26, h27, h28⟩ :=
      h_imm_c_one_block (by rw [h_imm_one]; exact one_ne_zero)
    obtain ⟨h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt⟩ := h_c_bnds
    apply Word.isU64_of_cases_poly
    · rw [h25, show (2 : ℕ) ^ 16 = 65536 from rfl]
      have : Main[21].val < (65536 : ZMod p).val := h_c0_lt
      rwa [h65536] at this
    · rw [h26, show (2 : ℕ) ^ 16 = 65536 from rfl]
      have : Main[22].val < (65536 : ZMod p).val := h_c1_lt
      rwa [h65536] at this
    · rw [h27, show (2 : ℕ) ^ 16 = 65536 from rfl]
      have : Main[23].val < (65536 : ZMod p).val := h_c2_lt
      rwa [h65536] at this
    · rw [h28, show (2 : ℕ) ^ 16 = 65536 from rfl]
      have : Main[24].val < (65536 : ZMod p).val := h_c3_lt
      rwa [h65536] at this

@[simp] def sp1_op_a_poly (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val
@[simp] def sp1_op_b_poly (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val
@[simp] def sp1_op_c_poly (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val
@[simp] def sp1_op_c_imm_poly (Main : Vector (ZMod p) 65) : BitVec 6 :=
  BitVec.ofNat 6 Main[21].val
@[simp] def sp1_op_c_imm_w_poly (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val

-- Polymorphic counterpart of `spec.sll`. Mirrors the Fin KB version's
-- structure: extract `bounds_poly` + `single_op_poly`, destructure `cstrs`
-- directly via `simp [constraints, ..., toProp_poly]` (no master iff lemma —
-- intractable for this chip per commit 4a60d33), reduce both sides to Nat
-- via `Word.toBitVec64_poly_toNat_poly` + `BitVec.toNat_shiftLeft`, take the
-- `c0.val % 64` shift amount through `is_mod_64_poly`, then 64-way case
-- split on `cb_i ∈ {0,1}`.
--
-- Per-leaf close: see `_spec_sll_poly_shift0_omega_test` below for the
-- arithmetic-core close pattern, which omega closes once the per-case
-- bridges (`Word.isU64_poly` for the result word; `a_i.val` from the active
-- `nw_*`; `c0.val % 64` from `is_mod_64_poly diff` with the concrete cb-sum)
-- are in scope. Filling those bridges per case is the remaining work.
set_option maxHeartbeats 64000000 in
-- Heavy: 65-element row + 70-clause constraints destructure + 64-way `rcases`
-- on cb0..cb5 + `simp only` distinctness lemmas at all hypotheses.
lemma spec.sll_poly (Main : Vector (ZMod p) 65) (h : is_sll_poly Main) :
    SP1ConstraintList.allHold_poly (constraints Main) →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w_poly
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]]
          .SLL := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  intro cstrs
  obtain ⟨eq_sll, eq_imm⟩ := h
  have ⟨hpc, is_U64_b, is_U64_c⟩ := bounds_poly Main cstrs (sll_real_poly Main eq_sll)
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨c0_16, c1_16, c2_16, c3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  obtain ⟨sop_1, sop_2⟩ := single_op_poly Main cstrs
  have h_63_zero : Main[63] = 0 := sop_1 eq_sll
  -- Destructure cstrs without the (intractable) master iff lemma.
  simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly] at cstrs
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
  obtain ⟨h_msb_a1, cpu, alu, _one_of_ops,
           _b_sll, _b_sllw,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
           h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
           eq_v01, eq_v012, eq_v0123,
           lt_ll0, lt_lh0, h_b0_dec, lt_ll1, lt_lh1, h_b1_dec,
           lt_ll2, lt_lh2, h_b2_dec, lt_ll3, lt_lh3, h_b3_dec,
           eq_lr0, eq_lr1, eq_lr2, eq_lr3,
           nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
           _w_00, _w_01, _w_02, _w_03, _w_04, _w_05,
           _eq_m64, _h13⟩ := cstrs
  clear h_msb_a1 cpu alu
  -- Convert `2 ^ ZMod.val 10` (= 1024) so `is_mod_64_poly` can consume `diff`.
  have h10_val : ((10 : ℕ) : ZMod p).val = 10 := ZMod.val_natCast_of_lt (by omega)
  have h10_cast : (10 : ZMod p) = ((10 : ℕ) : ZMod p) := by push_cast; rfl
  rw [h10_cast, h10_val] at diff
  norm_num at diff
  -- Distinctness facts for small ZMod literals (used to collapse the
  -- `K = K'` second disjuncts in the `h_su16*` hypotheses).
  have h_zmod_lit_ne : ∀ K K' : ℕ, K < 65536 → K' < 65536 → K ≠ K' →
      ((K : ZMod p) ≠ (K' : ZMod p)) := by
    intros K K' hK hK' hne heq
    have := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
    exact hne this
  have h_2_ne_0 : (2 : ZMod p) ≠ 0 := by
    have := h_zmod_lit_ne 2 0 (by omega) (by omega) (by omega); push_cast at this; exact this
  have h_2_ne_1 : (2 : ZMod p) ≠ 1 := by
    have := h_zmod_lit_ne 2 1 (by omega) (by omega) (by omega); push_cast at this; exact this
  have h_2_ne_3 : (2 : ZMod p) ≠ 3 := by
    have := h_zmod_lit_ne 2 3 (by omega) (by omega) (by omega); push_cast at this; exact this
  have h_1_ne_0 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h_0_ne_1 : (0 : ZMod p) ≠ 1 := h_1_ne_0.symm
  have h_1_ne_2 : (1 : ZMod p) ≠ 2 := h_2_ne_1.symm
  have h_1_ne_3 : (1 : ZMod p) ≠ 3 := by
    have := h_zmod_lit_ne 1 3 (by omega) (by omega) (by omega); push_cast at this; exact this
  have h_3_ne_0 : (3 : ZMod p) ≠ 0 := by
    have := h_zmod_lit_ne 3 0 (by omega) (by omega) (by omega); push_cast at this; exact this
  have h_3_ne_1 : (3 : ZMod p) ≠ 1 := h_1_ne_3.symm
  have h_3_ne_2 : (3 : ZMod p) ≠ 2 := h_2_ne_3.symm
  have h_0_ne_2 : (0 : ZMod p) ≠ 2 := h_2_ne_0.symm
  have h_0_ne_3 : (0 : ZMod p) ≠ 3 := h_3_ne_0.symm
  -- `is_real` discharges the `¬sll+sllw=0 →` prefix on `lt_lh*` and `lt_ll*`.
  have h_real_ne : ¬(sll + sllw = 0) := by
    rw [eq_sll, h_63_zero]; norm_num
  have h_sll_ne_zero : sll ≠ 0 := by rw [eq_sll]; exact h_1_ne_0
  -- Bridge RHS to nat upfront (does not depend on per-case info).
  rw [← BitVec.toNat_inj]
  simp only [execute_RTYPE_pure_w_poly]
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Word.toBitVec64_poly_toNat_poly is_U64_b, Word.toNat_poly_def]
  have h_setWidth :
      (BitVec.setWidth 6
        (Word.toBitVec64_poly (#v[Main[25], Main[26], Main[27], Main[28]]
                                  : Word (ZMod p)))).toNat
      = Main[25].val % 64 := by
    rw [BitVec.toNat_setWidth, Word.toBitVec64_poly_toNat_poly is_U64_c,
        Word.toNat_poly_def]
    have ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64_poly is_U64_c
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
               List.getElem_cons_succ] at *
    -- 2^6 = 64; higher limbs are multiples of 2^16 hence of 64.
    change (c0.val + c1.val * 2 ^ 16 + c2.val * 2 ^ 32 + c3.val * 2 ^ 48) % 64 = c0.val % 64
    omega
  rw [h_setWidth]
  -- 64-way case split on cb0..cb5 ∈ {0,1}; `simp only` substitutes concrete
  -- cb values, collapses the `2 = 0` etc. disjuncts in `h_su16*`, and reduces
  -- `eq_v0123`, `lt_ll*`, `lt_lh*`, `h_b*_dec`, `eq_lr*`, `nw_*` to concrete
  -- forms. After this, each leaf is the per-case arithmetic that closes via
  -- the `_spec_sll_poly_shift0_omega_test` pattern below (filling in the per-
  -- case `Word.isU64_poly`, `a_i.val`, and `c0.val % 64` bridges).
  set_option maxRecDepth 8192 in
  rcases b_cb0 with h_cb0 | h_cb0 <;> rcases b_cb1 with h_cb1 | h_cb1 <;>
  rcases b_cb2 with h_cb2 | h_cb2 <;> rcases b_cb3 with h_cb3 | h_cb3 <;>
  rcases b_cb4 with h_cb4 | h_cb4 <;> rcases b_cb5 with h_cb5 | h_cb5 <;>
  simp only [h_cb0, h_cb1, h_cb2, h_cb3, h_cb4, h_cb5,
             zero_mul, mul_zero, zero_add, add_zero, mul_one, one_mul,
             h_2_ne_0, h_2_ne_1, h_2_ne_3, h_1_ne_0, h_0_ne_1, h_1_ne_2, h_1_ne_3,
             h_3_ne_0, h_3_ne_1, h_3_ne_2, h_0_ne_2, h_0_ne_3,
             or_false, false_or, or_true, true_or] at *
  -- case 0/64 (shift = 0, su160 active): explicitly closed.
  · -- Discharge the `¬sll+sllw=0 →` prefix on lt_lh*, lt_ll*.
    have lt_lh0' := lt_lh0 h_real_ne
    have lt_lh1' := lt_lh1 h_real_ne
    have lt_lh2' := lt_lh2 h_real_ne
    have lt_lh3' := lt_lh3 h_real_ne
    have lt_ll0' := lt_ll0 h_real_ne
    have lt_ll1' := lt_ll1 h_real_ne
    have lt_ll2' := lt_ll2 h_real_ne
    have lt_ll3' := lt_ll3 h_real_ne
    have diff'  := diff h_real_ne
    -- Reduce `2 ^ ZMod.val 0 = 1` and `(16 - 0 : ZMod p).val = 16`.
    have hZ0 : (0 : ZMod p).val = 0 := ZMod.val_zero
    have h16 : ((16 : ZMod p) - 0).val = 16 := by
      rw [show ((16 : ZMod p) - 0) = ((16 : ℕ) : ZMod p) by push_cast; ring,
          ZMod.val_natCast_of_lt (by omega)]
    rw [hZ0] at lt_lh0' lt_lh1' lt_lh2' lt_lh3'
    rw [h16] at lt_ll0' lt_ll1' lt_ll2' lt_ll3'
    simp only [Nat.pow_zero, Nat.lt_one_iff] at lt_lh0' lt_lh1' lt_lh2' lt_lh3'
    -- hl_i = 0.
    have hl0_eq : hl0 = 0 := (ZMod.val_eq_zero hl0).mp lt_lh0'
    have hl1_eq : hl1 = 0 := (ZMod.val_eq_zero hl1).mp lt_lh1'
    have hl2_eq : hl2 = 0 := (ZMod.val_eq_zero hl2).mp lt_lh2'
    have hl3_eq : hl3 = 0 := (ZMod.val_eq_zero hl3).mp lt_lh3'
    -- Active su16 flag. After distinctness simp, h_su16{1,2,3} : su16i = 0.
    -- Substitute into one_of_su16s, dispatch the False disjunct.
    rw [h_su161, h_su162, h_su163] at one_of_su16s
    have h_su160_one : su160 = 1 := by
      have h := one_of_su16s.resolve_left h_real_ne
      linear_combination h
    have h_su160_ne : su160 ≠ 0 := by rw [h_su160_one]; exact h_1_ne_0
    -- v0123 = 1 (chain v0123 = v012 = v01 = 1 after cb's = 0).
    have h_v0123_one : v0123 = 1 := by
      have h := eq_v0123; rw [eq_v012, eq_v01] at h; exact h
    -- Substitute v0123 = 1 everywhere needed.
    rw [h_v0123_one] at h_b0_dec h_b1_dec h_b2_dec h_b3_dec eq_lr0 eq_lr1 eq_lr2 eq_lr3
    -- b_i = ll_i (from h_b_i_dec, hl_i = 0).
    have h_b0 : b0 = ll0 := by
      have h := h_b0_dec
      rw [hl0_eq] at h; linear_combination h
    have h_b1 : b1 = ll1 := by
      have h := h_b1_dec
      rw [hl1_eq] at h; linear_combination h
    have h_b2 : b2 = ll2 := by
      have h := h_b2_dec
      rw [hl2_eq] at h; linear_combination h
    have h_b3 : b3 = ll3 := by
      have h := h_b3_dec
      rw [hl3_eq] at h; linear_combination h
    -- lr_i values (now lr0 = ll0 * 1 = ll0; lr1 = ll1 + hl0; etc.)
    simp only [mul_one] at eq_lr0 eq_lr1 eq_lr2 eq_lr3
    rw [hl0_eq] at eq_lr1
    rw [hl1_eq] at eq_lr2
    rw [hl2_eq] at eq_lr3
    simp only [zero_add, add_zero] at eq_lr1 eq_lr2 eq_lr3
    -- a_i values via active nw_* (3-way disjunction: `sll = 0 ∨ su160 = 0 ∨ ...`).
    have h_a0_eq : a0 = lr0 :=
      (nw_00.resolve_left h_sll_ne_zero).resolve_left h_su160_ne
    have h_a1_eq : a1 = lr1 :=
      (nw_01.resolve_left h_sll_ne_zero).resolve_left h_su160_ne
    have h_a2_eq : a2 = lr2 :=
      (nw_02.resolve_left h_sll_ne_zero).resolve_left h_su160_ne
    have h_a3_eq : a3 = lr3 :=
      (nw_03.resolve_left h_sll_ne_zero).resolve_left h_su160_ne
    -- After the simp above, eq_lr0..eq_lr3 are now `lr_i = ll_i`.
    -- Chain a_i = lr_i = ll_i = b_i.
    have h_a0_val : a0.val = b0.val := by rw [h_a0_eq, eq_lr0, ← h_b0]
    have h_a1_val : a1.val = b1.val := by rw [h_a1_eq, eq_lr1, ← h_b1]
    have h_a2_val : a2.val = b2.val := by rw [h_a2_eq, eq_lr2, ← h_b2]
    have h_a3_val : a3.val = b3.val := by rw [h_a3_eq, eq_lr3, ← h_b3]
    -- Word.isU64_poly #v[a0..a3].
    have h_a_isU64 : Word.isU64_poly (#v[a0, a1, a2, a3] : Word (ZMod p)) := by
      apply Word.isU64_of_cases_poly
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
        rw [h_a0_val]
        have := b0_16
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at this
        exact this
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                   List.getElem_cons_succ]
        rw [h_a1_val]
        have := b1_16
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                   List.getElem_cons_succ] at this
        exact this
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                   List.getElem_cons_succ]
        rw [h_a2_val]
        have := b2_16
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                   List.getElem_cons_succ] at this
        exact this
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                   List.getElem_cons_succ]
        rw [h_a3_val]
        have := b3_16
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                   List.getElem_cons_succ] at this
        exact this
    -- c0.val % 64 = 0 from is_mod_64_poly (m = 0, since cb sum = 0 here).
    have h_c_mod : c0.val % 64 = 0 := by
      have hm : ((0 : ZMod p)).val < 64 := by rw [hZ0]; omega
      have hdiff' : ((c0 - 0) * (64 : ZMod p)⁻¹).val < 1024 := by
        simpa using diff'
      have := is_mod_64_poly hm hdiff'
      rw [hZ0] at this; exact this
    -- omega close.
    rw [Word.toBitVec64_poly_toNat_poly h_a_isU64, Word.toNat_poly_def]
    rw [h_c_mod]
    simp only [Nat.pow_zero, Nat.mul_one, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ, Nat.reduceAdd]
         at b0_16 b1_16 b2_16 b3_16 ⊢
    omega
  -- Remaining 63 cases: same structure (different active su16 / shift / a_i
  -- expressions). TODO: fill following the case-0 template above.
  all_goals sorry

set_option maxHeartbeats 16000000 in
-- Witness that omega closes the arithmetic core of each `spec.sll_poly` leaf
-- once the per-case bridge facts (Word.isU64_poly, `a_i.val = ...`,
-- `c0.val % 64 = ...`) are in scope. This is the shift = 0 case (cb_i = 0
-- for all i); other cases follow the same close pattern with different
-- a-side expressions and shift values.
private lemma _spec_sll_poly_shift0_omega_test
    (Main : Vector (ZMod p) 65) (h : is_sll_poly Main)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main))
    (_h_cb_all_zero : Main[36] = 0 ∧ Main[37] = 0 ∧ Main[38] = 0 ∧ Main[39] = 0 ∧
                      Main[40] = 0 ∧ Main[41] = 0) :
    Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
      execute_RTYPE_pure_w_poly
        #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[25], Main[26], Main[27], Main[28]]
        .SLL := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_sll, _eq_imm⟩ := h
  have ⟨_hpc, is_U64_b, is_U64_c⟩ := bounds_poly Main cstrs (sll_real_poly Main eq_sll)
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨_c0_16, _c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  -- The bridges (each `sorry` is per-case derivable from `cstrs`):
  have h_a_isU64 : Word.isU64_poly (#v[Main[32], Main[33], Main[34], Main[35]]
                                      : Word (ZMod p)) := sorry
  have h_a0_val : Main[32].val = Main[15].val := sorry
  have h_a1_val : Main[33].val = Main[16].val := sorry
  have h_a2_val : Main[34].val = Main[17].val := sorry
  have h_a3_val : Main[35].val = Main[18].val := sorry
  have h_c_mod : Main[25].val % 64 = 0 := sorry
  -- Bridge LHS to nat.
  rw [← BitVec.toNat_inj]
  rw [Word.toBitVec64_poly_toNat_poly h_a_isU64, Word.toNat_poly_def]
  -- Bridge RHS: execute_RTYPE_pure_w_poly .SLL = op1 <<< setWidth 6 op2.
  simp only [execute_RTYPE_pure_w_poly]
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Word.toBitVec64_poly_toNat_poly is_U64_b, Word.toNat_poly_def]
  -- Reduce setWidth shift count to c.val % 64.
  have h_setWidth :
      (BitVec.setWidth 6
        (Word.toBitVec64_poly (#v[Main[25], Main[26], Main[27], Main[28]]
                                  : Word (ZMod p)))).toNat
      = Main[25].val % 64 := by
    rw [BitVec.toNat_setWidth, Word.toBitVec64_poly_toNat_poly is_U64_c]
    rw [Word.toNat_poly_def]
    simp; omega
  rw [h_setWidth, h_c_mod]
  -- Now goal should be a pure Nat equation in Main[i].val terms. omega.
  simp only [Nat.pow_zero, Nat.mul_one, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ, Nat.reduceAdd]
       at b0_16 b1_16 b2_16 b3_16 ⊢
  omega

end poly_helpers

end ShiftLeft
