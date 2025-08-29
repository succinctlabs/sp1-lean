import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadByte

section constraints

-- Generated Lean code for chip LoadByteChip
@[irreducible] def constraints (Main : Vector (Fin BB) 47) : SP1ConstraintList :=
  let E0 : Fin BB := Main[1] * 65536
  let E1 : Fin BB := Main[2] + E0
  let E2 : Fin BB := 19 * Main[45]
  let E3 : Fin BB := 22 * Main[46]
  let E4 : Fin BB := E2 + E3
  let E5 : Fin BB := Main[45] * 0
  let E6 : Fin BB := Main[46] * 4
  let E7 : Fin BB := E5 + E6
  let E8 : Fin BB := Main[45] * 0
  let E9 : Fin BB := Main[46] * 0
  let E10 : Fin BB := E8 + E9
  let E11 : Fin BB := Main[45] * 3
  let E12 : Fin BB := Main[46] * 3
  let E13 : Fin BB := E11 + E12
  let E14 : Fin BB := Main[45] + Main[46]
  let E15 : Fin BB := Main[45] - 1
  let E16 : Fin BB := Main[45] * E15
  let E17 : Fin BB := Main[46] - 1
  let E18 : Fin BB := Main[46] * E17
  let E19 : Fin BB := E14 - 1
  let E20 : Fin BB := E14 * E19
  let ⟨⟨⟨[E21, E22, E23]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] Main[38] Main[39] Main[40] E14 { addr_operation := { value := #v[Main[25], Main[26], Main[27]] }, top_two_limb_inv := Main[28] }
  let E24 : Fin BB := E14 - 1
  let E25 : Fin BB := E14 * E24
  let E26 : Fin BB := Main[35] - 1
  let E27 : Fin BB := Main[35] * E26
  let E28 : Fin BB := E14 * E27
  let E29 : Fin BB := Main[0] - Main[33]
  let E30 : Fin BB := Main[35] * E29
  let E31 : Fin BB := E14 * E30
  let E32 : Fin BB := Main[35] * Main[34]
  let E33 : Fin BB := 1 - Main[35]
  let E34 : Fin BB := E33 * Main[33]
  let E35 : Fin BB := E32 + E34
  let E36 : Fin BB := Main[35] * E1
  let E37 : Fin BB := 1 - Main[35]
  let E38 : Fin BB := E37 * Main[0]
  let E39 : Fin BB := E36 + E38
  let E40 : Fin BB := E39 - E35
  let E41 : Fin BB := E40 - 1
  let E42 : Fin BB := Main[37] * 65536
  let E43 : Fin BB := Main[36] + E42
  let E44 : Fin BB := E41 - E43
  let E45 : Fin BB := E14 * E44
  let E46 : Fin BB := Main[39] - 1
  let E47 : Fin BB := Main[40] - 1
  let E48 : Fin BB := Main[41] - Main[29]
  let E49 : Fin BB := E47 * E48
  let E50 : Fin BB := E46 * E49
  let E51 : Fin BB := Main[40] - 1
  let E52 : Fin BB := Main[41] - Main[30]
  let E53 : Fin BB := E51 * E52
  let E54 : Fin BB := Main[39] * E53
  let E55 : Fin BB := Main[39] - 1
  let E56 : Fin BB := Main[41] - Main[31]
  let E57 : Fin BB := Main[40] * E56
  let E58 : Fin BB := E55 * E57
  let E59 : Fin BB := Main[41] - Main[32]
  let E60 : Fin BB := Main[40] * E59
  let E61 : Fin BB := Main[39] * E60
  let E62 : Fin BB := Main[41] - Main[42]
  let E63 : Fin BB := E62 * 2005401601
  let E64 : Fin BB := Main[38] * E63
  let E65 : Fin BB := 1 - Main[38]
  let E66 : Fin BB := E65 * Main[42]
  let E67 : Fin BB := E64 + E66
  let E68 : Fin BB := Main[43] - E67
  let E69 : Fin BB := Main[46] * Main[44]
  let E70 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E70, Main[4], Main[5]] 8 E14
  let E71 : Fin BB := 65280 * Main[44]
  let E72 : Fin BB := Main[43] + E71
  let E73 : Fin BB := 65535 * Main[44]
  let E74 : Fin BB := 65535 * Main[44]
  let E75 : Fin BB := 65535 * Main[44]
  let CS2 : SP1ConstraintList := ITypeReader.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E4 #v[E13, E7, E10] #v[E72, E73, E74, E75] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E14
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E16),
    (.assertZero E18),
    (.assertZero E20),
    (.assertZero E25),
    (.assertZero E28),
    (.assertZero E31),
    (.assertZero E45),
    (.send (.byte (ByteOpcode.ofNat 6) Main[36] 16 0) E14),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[37] 0) E14),
    (.send (.memory Main[33] Main[34] E21 E22 E23 Main[29] Main[30] Main[31] Main[32]) E14),
    (.receive (.memory Main[0] E1 E21 E22 E23 Main[29] Main[30] Main[31] Main[32]) E14),
    (.assertZero Main[13]),
    (.assertZero E50),
    (.assertZero E54),
    (.assertZero E58),
    (.assertZero E61),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[42] E63) E14),
    (.assertZero E68),
    (.assertZero E69),
    (.send (.byte (ByteOpcode.ofNat 5) Main[44] Main[43] 0) Main[45]),
  ]

end constraints

end LoadByte

end Load
