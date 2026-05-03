import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadX0

section constraints

-- Generated Lean code for chip LoadX0Chip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 48) : SP1ConstraintList F :=
  let E0 : F := Main[1] * 65536
  let E1 : F := Main[2] + E0
  let E2 : F := 29 * Main[41]
  let E3 : F := 32 * Main[42]
  let E4 : F := E2 + E3
  let E5 : F := 30 * Main[43]
  let E6 : F := E4 + E5
  let E7 : F := 33 * Main[44]
  let E8 : F := E6 + E7
  let E9 : F := 31 * Main[45]
  let E10 : F := E8 + E9
  let E11 : F := 34 * Main[46]
  let E12 : F := E10 + E11
  let E13 : F := 35 * Main[47]
  let E14 : F := E12 + E13
  let E15 : F := Main[41] * 0
  let E16 : F := Main[42] * 4
  let E17 : F := E15 + E16
  let E18 : F := Main[43] * 1
  let E19 : F := E17 + E18
  let E20 : F := Main[44] * 5
  let E21 : F := E19 + E20
  let E22 : F := Main[45] * 2
  let E23 : F := E21 + E22
  let E24 : F := Main[46] * 6
  let E25 : F := E23 + E24
  let E26 : F := Main[47] * 3
  let E27 : F := E25 + E26
  let E28 : F := Main[41] * 0
  let E29 : F := Main[42] * 0
  let E30 : F := E28 + E29
  let E31 : F := Main[43] * 0
  let E32 : F := E30 + E31
  let E33 : F := Main[44] * 0
  let E34 : F := E32 + E33
  let E35 : F := Main[45] * 0
  let E36 : F := E34 + E35
  let E37 : F := Main[46] * 0
  let E38 : F := E36 + E37
  let E39 : F := Main[47] * 0
  let E40 : F := E38 + E39
  let E41 : F := Main[41] * 3
  let E42 : F := Main[42] * 3
  let E43 : F := E41 + E42
  let E44 : F := Main[43] * 3
  let E45 : F := E43 + E44
  let E46 : F := Main[44] * 3
  let E47 : F := E45 + E46
  let E48 : F := Main[45] * 3
  let E49 : F := E47 + E48
  let E50 : F := Main[46] * 3
  let E51 : F := E49 + E50
  let E52 : F := Main[47] * 3
  let E53 : F := E51 + E52
  let E54 : F := Main[41] * 4
  let E55 : F := Main[42] * 4
  let E56 : F := E54 + E55
  let E57 : F := Main[43] * 4
  let E58 : F := E56 + E57
  let E59 : F := Main[44] * 4
  let E60 : F := E58 + E59
  let E61 : F := Main[45] * 4
  let E62 : F := E60 + E61
  let E63 : F := Main[46] * 4
  let E64 : F := E62 + E63
  let E65 : F := Main[47] * 4
  let E66 : F := E64 + E65
  let E67 : F := Main[41] + Main[42]
  let E68 : F := E67 + Main[43]
  let E69 : F := E68 + Main[44]
  let E70 : F := E69 + Main[45]
  let E71 : F := E70 + Main[46]
  let E72 : F := E71 + Main[47]
  let E73 : F := Main[41] - 1
  let E74 : F := Main[41] * E73
  let E75 : F := Main[42] - 1
  let E76 : F := Main[42] * E75
  let E77 : F := Main[43] - 1
  let E78 : F := Main[43] * E77
  let E79 : F := Main[44] - 1
  let E80 : F := Main[44] * E79
  let E81 : F := Main[45] - 1
  let E82 : F := Main[45] * E81
  let E83 : F := Main[46] - 1
  let E84 : F := Main[46] * E83
  let E85 : F := Main[47] - 1
  let E86 : F := Main[47] * E85
  let E87 : F := E72 - 1
  let E88 : F := E72 * E87
  let ⟨⟨⟨[E89, E90, E91]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] Main[38] Main[39] Main[40] E72 { addr_operation := { value := #v[Main[25], Main[26], Main[27]] }, top_two_limb_inv := Main[28] }
  let E92 : F := Main[47] * Main[40]
  let E93 : F := Main[45] + Main[46]
  let E94 : F := E93 + Main[47]
  let E95 : F := E94 * Main[39]
  let E96 : F := Main[43] + Main[44]
  let E97 : F := E96 + Main[45]
  let E98 : F := E97 + Main[46]
  let E99 : F := E98 + Main[47]
  let E100 : F := E99 * Main[38]
  let E101 : F := E1 + 1
  let E102 : F := E72 - 1
  let E103 : F := E72 * E102
  let E104 : F := Main[35] - 1
  let E105 : F := Main[35] * E104
  let E106 : F := E72 * E105
  let E107 : F := Main[0] - Main[33]
  let E108 : F := Main[35] * E107
  let E109 : F := E72 * E108
  let E110 : F := Main[35] * Main[34]
  let E111 : F := 1 - Main[35]
  let E112 : F := E111 * Main[33]
  let E113 : F := E110 + E112
  let E114 : F := Main[35] * E101
  let E115 : F := 1 - Main[35]
  let E116 : F := E115 * Main[0]
  let E117 : F := E114 + E116
  let E118 : F := E117 - E113
  let E119 : F := E118 - 1
  let E120 : F := Main[37] * 65536
  let E121 : F := Main[36] + E120
  let E122 : F := E119 - E121
  let E123 : F := E72 * E122
  let E124 : F := Main[13] - 1
  let E125 : F := E72 * E124
  let E126 : F := E72 - 1
  let E127 : F := E126 * Main[13]
  let E128 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E128, Main[4], Main[5]] 8 E72
  let CS2 : SP1ConstraintList F := ITypeReaderImmutable.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E14 #v[E66, E53, E27, E40] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E72
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E74),
    (.assertZero E76),
    (.assertZero E78),
    (.assertZero E80),
    (.assertZero E82),
    (.assertZero E84),
    (.assertZero E86),
    (.assertZero E88),
    (.assertZero E92),
    (.assertZero E95),
    (.assertZero E100),
    (.assertZero E103),
    (.assertZero E106),
    (.assertZero E109),
    (.assertZero E123),
    (.send (.byte (ByteOpcode.ofNat 6) Main[36] 16 0) E72),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[37] 0) E72),
    (.send (.memory Main[33] Main[34] E89 E90 E91 Main[29] Main[30] Main[31] Main[32]) E72),
    (.receive (.memory Main[0] E101 E89 E90 E91 Main[29] Main[30] Main[31] Main[32]) E72),
    (.assertZero E125),
    (.assertZero E127),
  ]

end constraints

section poly_helpers

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

/-- Umbrella "is real" gate for LoadX0. The chip covers all 7 load
sub-opcodes (LB/LBU/LH/LHU/LW/LWU/LD when `op_a = x0`); each is selected
by exactly one of `Main[41..47]` being 1, and the sum is the chip-wide
"is real" flag. -/
@[simp] def is_loadX0_poly (Main : Vector (ZMod p) 48) : Prop :=
  Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] = 1

/-- `Main[47] = 1` selects the LD (load-doubleword) sub-opcode. -/
@[simp] def is_loadX0_ld_poly (Main : Vector (ZMod p) 48) : Prop := Main[47] = 1

end poly_helpers

end LoadX0

end Load
