import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Store

namespace StoreByte

section constraints

-- Generated Lean code for chip StoreByteChip
def constraints (Main : Vector (Fin BB) 50) : SP1ConstraintList :=
  let E0 : Fin BB := Main[1] * 65536
  let E1 : Fin BB := Main[2] + E0
  let E2 : Fin BB := Main[49] - 1
  let E3 : Fin BB := Main[49] * E2
  let ⟨⟨⟨[E4, E5, E6]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] Main[38] Main[39] Main[40] Main[49] { addr_word_operation := { value := #v[Main[25], Main[26], Main[27]] }, top_two_limb_inv := Main[28] }
  let E7 : Fin BB := Main[49] - 1
  let E8 : Fin BB := Main[49] * E7
  let E9 : Fin BB := Main[35] - 1
  let E10 : Fin BB := Main[35] * E9
  let E11 : Fin BB := Main[49] * E10
  let E12 : Fin BB := Main[0] - Main[33]
  let E13 : Fin BB := Main[35] * E12
  let E14 : Fin BB := Main[49] * E13
  let E15 : Fin BB := Main[35] * Main[34]
  let E16 : Fin BB := 1 - Main[35]
  let E17 : Fin BB := E16 * Main[33]
  let E18 : Fin BB := E15 + E17
  let E19 : Fin BB := Main[35] * E1
  let E20 : Fin BB := 1 - Main[35]
  let E21 : Fin BB := E20 * Main[0]
  let E22 : Fin BB := E19 + E21
  let E23 : Fin BB := E22 - E18
  let E24 : Fin BB := E23 - 1
  let E25 : Fin BB := Main[37] * 65536
  let E26 : Fin BB := Main[36] + E25
  let E27 : Fin BB := E24 - E26
  let E28 : Fin BB := Main[49] * E27
  let E29 : Fin BB := Main[39] - 1
  let E30 : Fin BB := Main[40] - 1
  let E31 : Fin BB := Main[41] - Main[29]
  let E32 : Fin BB := E30 * E31
  let E33 : Fin BB := E29 * E32
  let E34 : Fin BB := Main[40] - 1
  let E35 : Fin BB := Main[41] - Main[30]
  let E36 : Fin BB := E34 * E35
  let E37 : Fin BB := Main[39] * E36
  let E38 : Fin BB := Main[39] - 1
  let E39 : Fin BB := Main[41] - Main[31]
  let E40 : Fin BB := Main[40] * E39
  let E41 : Fin BB := E38 * E40
  let E42 : Fin BB := Main[41] - Main[32]
  let E43 : Fin BB := Main[40] * E42
  let E44 : Fin BB := Main[39] * E43
  let E45 : Fin BB := Main[7] - Main[43]
  let E46 : Fin BB := E45 * 2005401601
  let E47 : Fin BB := Main[41] - Main[42]
  let E48 : Fin BB := E47 * 2005401601
  let E49 : Fin BB := Main[43] - Main[42]
  let E50 : Fin BB := 1 - Main[38]
  let E51 : Fin BB := E49 * E50
  let E52 : Fin BB := Main[43] - E48
  let E53 : Fin BB := 256 * E52
  let E54 : Fin BB := E53 * Main[38]
  let E55 : Fin BB := E51 + E54
  let E56 : Fin BB := Main[44] - E55
  let E57 : Fin BB := 1 - Main[39]
  let E58 : Fin BB := Main[44] * E57
  let E59 : Fin BB := 1 - Main[40]
  let E60 : Fin BB := E58 * E59
  let E61 : Fin BB := E60 + Main[29]
  let E62 : Fin BB := Main[45] - E61
  let E63 : Fin BB := Main[44] * Main[39]
  let E64 : Fin BB := 1 - Main[40]
  let E65 : Fin BB := E63 * E64
  let E66 : Fin BB := E65 + Main[30]
  let E67 : Fin BB := Main[46] - E66
  let E68 : Fin BB := 1 - Main[39]
  let E69 : Fin BB := Main[44] * E68
  let E70 : Fin BB := E69 * Main[40]
  let E71 : Fin BB := E70 + Main[31]
  let E72 : Fin BB := Main[47] - E71
  let E73 : Fin BB := Main[44] * Main[39]
  let E74 : Fin BB := E73 * Main[40]
  let E75 : Fin BB := E74 + Main[32]
  let E76 : Fin BB := Main[48] - E75
  let E77 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E77, Main[4], Main[5]] 8 Main[49]
  let CS2 : SP1ConstraintList := ITypeReaderImmutable.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] 24 #v[35, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } Main[49]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E8),
    (.assertZero E11),
    (.assertZero E14),
    (.assertZero E28),
    (.send (.byte (ByteOpcode.ofNat 6) Main[36] 16 0) Main[49]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[37] 0) Main[49]),
    (.send (.memory Main[33] Main[34] E4 E5 E6 Main[29] Main[30] Main[31] Main[32]) Main[49]),
    (.receive (.memory Main[0] E1 E4 E5 E6 Main[45] Main[46] Main[47] Main[48]) Main[49]),
    (.assertZero E33),
    (.assertZero E37),
    (.assertZero E41),
    (.assertZero E44),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[43] E46) Main[49]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[42] E48) Main[49]),
    (.assertZero E56),
    (.assertZero E62),
    (.assertZero E67),
    (.assertZero E72),
    (.assertZero E76),
  ]

end constraints

end StoreByte

end Store
