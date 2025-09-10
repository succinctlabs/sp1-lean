import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadX0

section constraints

-- Generated Lean code for chip LoadX0Chip
def constraints (Main : Vector (Fin BB) 50) : SP1ConstraintList :=
  let E0 : Fin BB := Main[1] * 65536
  let E1 : Fin BB := Main[2] + E0
  let E2 : Fin BB := 19 * Main[42]
  let E3 : Fin BB := 22 * Main[43]
  let E4 : Fin BB := E2 + E3
  let E5 : Fin BB := 20 * Main[44]
  let E6 : Fin BB := E4 + E5
  let E7 : Fin BB := 23 * Main[45]
  let E8 : Fin BB := E6 + E7
  let E9 : Fin BB := 21 * Main[46]
  let E10 : Fin BB := E8 + E9
  let E11 : Fin BB := 44 * Main[47]
  let E12 : Fin BB := E10 + E11
  let E13 : Fin BB := 45 * Main[48]
  let E14 : Fin BB := E12 + E13
  let E15 : Fin BB := Main[42] * 0
  let E16 : Fin BB := Main[43] * 4
  let E17 : Fin BB := E15 + E16
  let E18 : Fin BB := Main[44] * 1
  let E19 : Fin BB := E17 + E18
  let E20 : Fin BB := Main[45] * 5
  let E21 : Fin BB := E19 + E20
  let E22 : Fin BB := Main[46] * 2
  let E23 : Fin BB := E21 + E22
  let E24 : Fin BB := Main[47] * 6
  let E25 : Fin BB := E23 + E24
  let E26 : Fin BB := Main[48] * 3
  let E27 : Fin BB := E25 + E26
  let E28 : Fin BB := Main[42] * 0
  let E29 : Fin BB := Main[43] * 0
  let E30 : Fin BB := E28 + E29
  let E31 : Fin BB := Main[44] * 0
  let E32 : Fin BB := E30 + E31
  let E33 : Fin BB := Main[45] * 0
  let E34 : Fin BB := E32 + E33
  let E35 : Fin BB := Main[46] * 0
  let E36 : Fin BB := E34 + E35
  let E37 : Fin BB := Main[47] * 0
  let E38 : Fin BB := E36 + E37
  let E39 : Fin BB := Main[48] * 0
  let E40 : Fin BB := E38 + E39
  let E41 : Fin BB := Main[42] * 3
  let E42 : Fin BB := Main[43] * 3
  let E43 : Fin BB := E41 + E42
  let E44 : Fin BB := Main[44] * 3
  let E45 : Fin BB := E43 + E44
  let E46 : Fin BB := Main[45] * 3
  let E47 : Fin BB := E45 + E46
  let E48 : Fin BB := Main[46] * 3
  let E49 : Fin BB := E47 + E48
  let E50 : Fin BB := Main[47] * 3
  let E51 : Fin BB := E49 + E50
  let E52 : Fin BB := Main[48] * 3
  let E53 : Fin BB := E51 + E52
  let E54 : Fin BB := Main[42] * 4
  let E55 : Fin BB := Main[43] * 4
  let E56 : Fin BB := E54 + E55
  let E57 : Fin BB := Main[44] * 4
  let E58 : Fin BB := E56 + E57
  let E59 : Fin BB := Main[45] * 4
  let E60 : Fin BB := E58 + E59
  let E61 : Fin BB := Main[46] * 4
  let E62 : Fin BB := E60 + E61
  let E63 : Fin BB := Main[47] * 4
  let E64 : Fin BB := E62 + E63
  let E65 : Fin BB := Main[48] * 4
  let E66 : Fin BB := E64 + E65
  let E67 : Fin BB := Main[42] + Main[43]
  let E68 : Fin BB := E67 + Main[44]
  let E69 : Fin BB := E68 + Main[45]
  let E70 : Fin BB := E69 + Main[46]
  let E71 : Fin BB := E70 + Main[47]
  let E72 : Fin BB := E71 + Main[48]
  let E73 : Fin BB := Main[42] - 1
  let E74 : Fin BB := Main[42] * E73
  let E75 : Fin BB := Main[43] - 1
  let E76 : Fin BB := Main[43] * E75
  let E77 : Fin BB := Main[44] - 1
  let E78 : Fin BB := Main[44] * E77
  let E79 : Fin BB := Main[45] - 1
  let E80 : Fin BB := Main[45] * E79
  let E81 : Fin BB := Main[46] - 1
  let E82 : Fin BB := Main[46] * E81
  let E83 : Fin BB := Main[47] - 1
  let E84 : Fin BB := Main[47] * E83
  let E85 : Fin BB := Main[48] - 1
  let E86 : Fin BB := Main[48] * E85
  let E87 : Fin BB := E72 - 1
  let E88 : Fin BB := E72 * E87
  let ⟨⟨⟨[E89, E90, E91]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] Main[39] Main[40] Main[41] E72 { addr_operation := { value := #v[Main[26], Main[27], Main[28]] }, top_two_limb_inv := Main[29] }
  let E92 : Fin BB := Main[48] * Main[41]
  let E93 : Fin BB := Main[46] + Main[47]
  let E94 : Fin BB := E93 + Main[48]
  let E95 : Fin BB := E94 * Main[40]
  let E96 : Fin BB := Main[44] + Main[45]
  let E97 : Fin BB := E96 + Main[46]
  let E98 : Fin BB := E97 + Main[47]
  let E99 : Fin BB := E98 + Main[48]
  let E100 : Fin BB := E99 * Main[39]
  let E101 : Fin BB := E1 + 1
  let E102 : Fin BB := E72 - 1
  let E103 : Fin BB := E72 * E102
  let E104 : Fin BB := Main[36] - 1
  let E105 : Fin BB := Main[36] * E104
  let E106 : Fin BB := E72 * E105
  let E107 : Fin BB := Main[0] - Main[34]
  let E108 : Fin BB := Main[36] * E107
  let E109 : Fin BB := E72 * E108
  let E110 : Fin BB := Main[36] * Main[35]
  let E111 : Fin BB := 1 - Main[36]
  let E112 : Fin BB := E111 * Main[34]
  let E113 : Fin BB := E110 + E112
  let E114 : Fin BB := Main[36] * E101
  let E115 : Fin BB := 1 - Main[36]
  let E116 : Fin BB := E115 * Main[0]
  let E117 : Fin BB := E114 + E116
  let E118 : Fin BB := E117 - E113
  let E119 : Fin BB := E118 - 1
  let E120 : Fin BB := Main[38] * 65536
  let E121 : Fin BB := Main[37] + E120
  let E122 : Fin BB := E119 - E121
  let E123 : Fin BB := E72 * E122
  let E124 : Fin BB := Public Arg [151] * E72
  let E125 : Fin BB := Main[49] - E124
  let E126 : Fin BB := E1 + 1
  let E127 : Fin BB := Main[13] - 1
  let E128 : Fin BB := E72 * E127
  let E129 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E129, Main[4], Main[5]] 8 E72
  let CS2 : SP1ConstraintList := ITypeReaderImmutable.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E14 #v[E66, E53, E27, E40] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } E72
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
    (.send (.byte (ByteOpcode.ofNat 6) Main[37] 16 0) E72),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[38] 0) E72),
    (.send (.memory Main[34] Main[35] E89 E90 E91 Main[30] Main[31] Main[32] Main[33]) E72),
    (.receive (.memory Main[0] E101 E89 E90 E91 Main[30] Main[31] Main[32] Main[33]) E72),
    (.assertZero E125),
    (.assertZero E128),
  ]

end constraints

end LoadX0

end Load
