import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadX0

section constraints

-- Generated Lean code for chip LoadX0Chip
@[irreducible] def constraints (Main : Vector (Fin KB) 48) : SP1ConstraintList (Fin KB) :=
  let E0 : Fin KB := Main[1] * 65536
  let E1 : Fin KB := Main[2] + E0
  let E2 : Fin KB := 29 * Main[41]
  let E3 : Fin KB := 32 * Main[42]
  let E4 : Fin KB := E2 + E3
  let E5 : Fin KB := 30 * Main[43]
  let E6 : Fin KB := E4 + E5
  let E7 : Fin KB := 33 * Main[44]
  let E8 : Fin KB := E6 + E7
  let E9 : Fin KB := 31 * Main[45]
  let E10 : Fin KB := E8 + E9
  let E11 : Fin KB := 34 * Main[46]
  let E12 : Fin KB := E10 + E11
  let E13 : Fin KB := 35 * Main[47]
  let E14 : Fin KB := E12 + E13
  let E15 : Fin KB := Main[41] * 0
  let E16 : Fin KB := Main[42] * 4
  let E17 : Fin KB := E15 + E16
  let E18 : Fin KB := Main[43] * 1
  let E19 : Fin KB := E17 + E18
  let E20 : Fin KB := Main[44] * 5
  let E21 : Fin KB := E19 + E20
  let E22 : Fin KB := Main[45] * 2
  let E23 : Fin KB := E21 + E22
  let E24 : Fin KB := Main[46] * 6
  let E25 : Fin KB := E23 + E24
  let E26 : Fin KB := Main[47] * 3
  let E27 : Fin KB := E25 + E26
  let E28 : Fin KB := Main[41] * 0
  let E29 : Fin KB := Main[42] * 0
  let E30 : Fin KB := E28 + E29
  let E31 : Fin KB := Main[43] * 0
  let E32 : Fin KB := E30 + E31
  let E33 : Fin KB := Main[44] * 0
  let E34 : Fin KB := E32 + E33
  let E35 : Fin KB := Main[45] * 0
  let E36 : Fin KB := E34 + E35
  let E37 : Fin KB := Main[46] * 0
  let E38 : Fin KB := E36 + E37
  let E39 : Fin KB := Main[47] * 0
  let E40 : Fin KB := E38 + E39
  let E41 : Fin KB := Main[41] * 3
  let E42 : Fin KB := Main[42] * 3
  let E43 : Fin KB := E41 + E42
  let E44 : Fin KB := Main[43] * 3
  let E45 : Fin KB := E43 + E44
  let E46 : Fin KB := Main[44] * 3
  let E47 : Fin KB := E45 + E46
  let E48 : Fin KB := Main[45] * 3
  let E49 : Fin KB := E47 + E48
  let E50 : Fin KB := Main[46] * 3
  let E51 : Fin KB := E49 + E50
  let E52 : Fin KB := Main[47] * 3
  let E53 : Fin KB := E51 + E52
  let E54 : Fin KB := Main[41] * 4
  let E55 : Fin KB := Main[42] * 4
  let E56 : Fin KB := E54 + E55
  let E57 : Fin KB := Main[43] * 4
  let E58 : Fin KB := E56 + E57
  let E59 : Fin KB := Main[44] * 4
  let E60 : Fin KB := E58 + E59
  let E61 : Fin KB := Main[45] * 4
  let E62 : Fin KB := E60 + E61
  let E63 : Fin KB := Main[46] * 4
  let E64 : Fin KB := E62 + E63
  let E65 : Fin KB := Main[47] * 4
  let E66 : Fin KB := E64 + E65
  let E67 : Fin KB := Main[41] + Main[42]
  let E68 : Fin KB := E67 + Main[43]
  let E69 : Fin KB := E68 + Main[44]
  let E70 : Fin KB := E69 + Main[45]
  let E71 : Fin KB := E70 + Main[46]
  let E72 : Fin KB := E71 + Main[47]
  let E73 : Fin KB := Main[41] - 1
  let E74 : Fin KB := Main[41] * E73
  let E75 : Fin KB := Main[42] - 1
  let E76 : Fin KB := Main[42] * E75
  let E77 : Fin KB := Main[43] - 1
  let E78 : Fin KB := Main[43] * E77
  let E79 : Fin KB := Main[44] - 1
  let E80 : Fin KB := Main[44] * E79
  let E81 : Fin KB := Main[45] - 1
  let E82 : Fin KB := Main[45] * E81
  let E83 : Fin KB := Main[46] - 1
  let E84 : Fin KB := Main[46] * E83
  let E85 : Fin KB := Main[47] - 1
  let E86 : Fin KB := Main[47] * E85
  let E87 : Fin KB := E72 - 1
  let E88 : Fin KB := E72 * E87
  let ⟨⟨⟨[E89, E90, E91]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] Main[38] Main[39] Main[40] E72 { addr_operation := { value := #v[Main[25], Main[26], Main[27]] }, top_two_limb_inv := Main[28] }
  let E92 : Fin KB := Main[47] * Main[40]
  let E93 : Fin KB := Main[45] + Main[46]
  let E94 : Fin KB := E93 + Main[47]
  let E95 : Fin KB := E94 * Main[39]
  let E96 : Fin KB := Main[43] + Main[44]
  let E97 : Fin KB := E96 + Main[45]
  let E98 : Fin KB := E97 + Main[46]
  let E99 : Fin KB := E98 + Main[47]
  let E100 : Fin KB := E99 * Main[38]
  let E101 : Fin KB := E1 + 1
  let E102 : Fin KB := E72 - 1
  let E103 : Fin KB := E72 * E102
  let E104 : Fin KB := Main[35] - 1
  let E105 : Fin KB := Main[35] * E104
  let E106 : Fin KB := E72 * E105
  let E107 : Fin KB := Main[0] - Main[33]
  let E108 : Fin KB := Main[35] * E107
  let E109 : Fin KB := E72 * E108
  let E110 : Fin KB := Main[35] * Main[34]
  let E111 : Fin KB := 1 - Main[35]
  let E112 : Fin KB := E111 * Main[33]
  let E113 : Fin KB := E110 + E112
  let E114 : Fin KB := Main[35] * E101
  let E115 : Fin KB := 1 - Main[35]
  let E116 : Fin KB := E115 * Main[0]
  let E117 : Fin KB := E114 + E116
  let E118 : Fin KB := E117 - E113
  let E119 : Fin KB := E118 - 1
  let E120 : Fin KB := Main[37] * 65536
  let E121 : Fin KB := Main[36] + E120
  let E122 : Fin KB := E119 - E121
  let E123 : Fin KB := E72 * E122
  let E124 : Fin KB := Main[13] - 1
  let E125 : Fin KB := E72 * E124
  let E126 : Fin KB := E72 - 1
  let E127 : Fin KB := E126 * Main[13]
  let E128 : Fin KB := Main[3] + 4
  let CS1 : SP1ConstraintList (Fin KB) := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E128, Main[4], Main[5]] 8 E72
  let CS2 : SP1ConstraintList (Fin KB) := ITypeReaderImmutable.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E14 #v[E66, E53, E27, E40] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E72
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

end LoadX0

end Load
