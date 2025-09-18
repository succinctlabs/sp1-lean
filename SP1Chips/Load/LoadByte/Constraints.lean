import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadByte

section constraints

-- Generated Lean code for chip LoadByteChip
@[irreducible] def constraints (Main : Vector (Fin BB) 49) : SP1ConstraintList :=
  let E0 : Fin BB := Main[1] * 65536
  let E1 : Fin BB := Main[2] + E0
  let E2 : Fin BB := 19 * Main[46]
  let E3 : Fin BB := 22 * Main[47]
  let E4 : Fin BB := E2 + E3
  let E5 : Fin BB := Main[46] * 0
  let E6 : Fin BB := Main[47] * 4
  let E7 : Fin BB := E5 + E6
  let E8 : Fin BB := Main[46] * 0
  let E9 : Fin BB := Main[47] * 0
  let E10 : Fin BB := E8 + E9
  let E11 : Fin BB := Main[46] * 3
  let E12 : Fin BB := Main[47] * 3
  let E13 : Fin BB := E11 + E12
  let E14 : Fin BB := Main[46] * 4
  let E15 : Fin BB := Main[47] * 4
  let E16 : Fin BB := E14 + E15
  let E17 : Fin BB := Main[46] + Main[47]
  let E18 : Fin BB := Main[46] - 1
  let E19 : Fin BB := Main[46] * E18
  let E20 : Fin BB := Main[47] - 1
  let E21 : Fin BB := Main[47] * E20
  let E22 : Fin BB := E17 - 1
  let E23 : Fin BB := E17 * E22
  let ⟨⟨⟨[E24, E25, E26]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] Main[39] Main[40] Main[41] E17 { addr_operation := { value := #v[Main[26], Main[27], Main[28]] }, top_two_limb_inv := Main[29] }
  let E27 : Fin BB := E1 + 1
  let E28 : Fin BB := E17 - 1
  let E29 : Fin BB := E17 * E28
  let E30 : Fin BB := Main[36] - 1
  let E31 : Fin BB := Main[36] * E30
  let E32 : Fin BB := E17 * E31
  let E33 : Fin BB := Main[0] - Main[34]
  let E34 : Fin BB := Main[36] * E33
  let E35 : Fin BB := E17 * E34
  let E36 : Fin BB := Main[36] * Main[35]
  let E37 : Fin BB := 1 - Main[36]
  let E38 : Fin BB := E37 * Main[34]
  let E39 : Fin BB := E36 + E38
  let E40 : Fin BB := Main[36] * E27
  let E41 : Fin BB := 1 - Main[36]
  let E42 : Fin BB := E41 * Main[0]
  let E43 : Fin BB := E40 + E42
  let E44 : Fin BB := E43 - E39
  let E45 : Fin BB := E44 - 1
  let E46 : Fin BB := Main[38] * 65536
  let E47 : Fin BB := Main[37] + E46
  let E48 : Fin BB := E45 - E47
  let E49 : Fin BB := E17 * E48
  let E50 : Fin BB := mprotect_enabled () * E17
  let E51 : Fin BB := Main[48] - E50
  let E52 : Fin BB := E1 + 1
  let E53 : Fin BB := Main[40] - 1
  let E54 : Fin BB := Main[41] - 1
  let E55 : Fin BB := Main[42] - Main[30]
  let E56 : Fin BB := E54 * E55
  let E57 : Fin BB := E53 * E56
  let E58 : Fin BB := Main[41] - 1
  let E59 : Fin BB := Main[42] - Main[31]
  let E60 : Fin BB := E58 * E59
  let E61 : Fin BB := Main[40] * E60
  let E62 : Fin BB := Main[40] - 1
  let E63 : Fin BB := Main[42] - Main[32]
  let E64 : Fin BB := Main[41] * E63
  let E65 : Fin BB := E62 * E64
  let E66 : Fin BB := Main[42] - Main[33]
  let E67 : Fin BB := Main[41] * E66
  let E68 : Fin BB := Main[40] * E67
  let E69 : Fin BB := Main[42] - Main[43]
  let E70 : Fin BB := E69 * 2122383361
  let E71 : Fin BB := Main[39] * E70
  let E72 : Fin BB := 1 - Main[39]
  let E73 : Fin BB := E72 * Main[43]
  let E74 : Fin BB := E71 + E73
  let E75 : Fin BB := Main[44] - E74
  let E76 : Fin BB := Main[47] * Main[45]
  let E77 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E77, Main[4], Main[5]] 8 E17
  let E78 : Fin BB := 65280 * Main[45]
  let E79 : Fin BB := Main[44] + E78
  let E80 : Fin BB := 65535 * Main[45]
  let E81 : Fin BB := 65535 * Main[45]
  let E82 : Fin BB := 65535 * Main[45]
  let CS2 : SP1ConstraintList := ITypeReader.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E4 #v[E16, E13, E7, E10] #v[E79, E80, E81, E82] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } E17
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E19),
    (.assertZero E21),
    (.assertZero E23),
    (.assertZero E29),
    (.assertZero E32),
    (.assertZero E35),
    (.assertZero E49),
    (.send (.byte (ByteOpcode.ofNat 6) Main[37] 16 0) E17),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[38] 0) E17),
    (.send (.memory Main[34] Main[35] E24 E25 E26 Main[30] Main[31] Main[32] Main[33]) E17),
    (.receive (.memory Main[0] E27 E24 E25 E26 Main[30] Main[31] Main[32] Main[33]) E17),
    (.assertZero E51),
    (.assertZero Main[13]),
    (.assertZero E57),
    (.assertZero E61),
    (.assertZero E65),
    (.assertZero E68),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[43] E70) E17),
    (.assertZero E75),
    (.assertZero E76),
    (.send (.byte (ByteOpcode.ofNat 5) Main[45] Main[44] 0) Main[46]),
  ]

end constraints

end LoadByte

end Load
