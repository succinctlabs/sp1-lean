import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Store

namespace StoreByte 

section constraints

-- Generated Lean code for chip StoreByteChip
def constraints (Main : Vector (Fin BB) 52) : SP1ConstraintList :=
  let E0 : Fin BB := Main[1] * 65536
  let E1 : Fin BB := Main[2] + E0
  let E2 : Fin BB := Main[50] - 1
  let E3 : Fin BB := Main[50] * E2
  let ⟨⟨⟨[E4, E5, E6]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] Main[39] Main[40] Main[41] Main[50] { addr_operation := { value := #v[Main[26], Main[27], Main[28]] }, top_two_limb_inv := Main[29] }
  let E7 : Fin BB := E1 + 1
  let E8 : Fin BB := Main[50] - 1
  let E9 : Fin BB := Main[50] * E8
  let E10 : Fin BB := Main[36] - 1
  let E11 : Fin BB := Main[36] * E10
  let E12 : Fin BB := Main[50] * E11
  let E13 : Fin BB := Main[0] - Main[34]
  let E14 : Fin BB := Main[36] * E13
  let E15 : Fin BB := Main[50] * E14
  let E16 : Fin BB := Main[36] * Main[35]
  let E17 : Fin BB := 1 - Main[36]
  let E18 : Fin BB := E17 * Main[34]
  let E19 : Fin BB := E16 + E18
  let E20 : Fin BB := Main[36] * E7
  let E21 : Fin BB := 1 - Main[36]
  let E22 : Fin BB := E21 * Main[0]
  let E23 : Fin BB := E20 + E22
  let E24 : Fin BB := E23 - E19
  let E25 : Fin BB := E24 - 1
  let E26 : Fin BB := Main[38] * 65536
  let E27 : Fin BB := Main[37] + E26
  let E28 : Fin BB := E25 - E27
  let E29 : Fin BB := Main[50] * E28
  let E30 : Fin BB := Public Arg [151] * Main[50]
  let E31 : Fin BB := Main[51] - E30
  let E32 : Fin BB := E1 + 1
  let E33 : Fin BB := Main[40] - 1
  let E34 : Fin BB := Main[41] - 1
  let E35 : Fin BB := Main[42] - Main[30]
  let E36 : Fin BB := E34 * E35
  let E37 : Fin BB := E33 * E36
  let E38 : Fin BB := Main[41] - 1
  let E39 : Fin BB := Main[42] - Main[31]
  let E40 : Fin BB := E38 * E39
  let E41 : Fin BB := Main[40] * E40
  let E42 : Fin BB := Main[40] - 1
  let E43 : Fin BB := Main[42] - Main[32]
  let E44 : Fin BB := Main[41] * E43
  let E45 : Fin BB := E42 * E44
  let E46 : Fin BB := Main[42] - Main[33]
  let E47 : Fin BB := Main[41] * E46
  let E48 : Fin BB := Main[40] * E47
  let E49 : Fin BB := Main[7] - Main[44]
  let E50 : Fin BB := E49 * 2122383361
  let E51 : Fin BB := Main[42] - Main[43]
  let E52 : Fin BB := E51 * 2122383361
  let E53 : Fin BB := Main[44] - Main[43]
  let E54 : Fin BB := 1 - Main[39]
  let E55 : Fin BB := E53 * E54
  let E56 : Fin BB := Main[44] - E52
  let E57 : Fin BB := 256 * E56
  let E58 : Fin BB := E57 * Main[39]
  let E59 : Fin BB := E55 + E58
  let E60 : Fin BB := Main[45] - E59
  let E61 : Fin BB := 1 - Main[40]
  let E62 : Fin BB := Main[45] * E61
  let E63 : Fin BB := 1 - Main[41]
  let E64 : Fin BB := E62 * E63
  let E65 : Fin BB := E64 + Main[30]
  let E66 : Fin BB := Main[46] - E65
  let E67 : Fin BB := Main[45] * Main[40]
  let E68 : Fin BB := 1 - Main[41]
  let E69 : Fin BB := E67 * E68
  let E70 : Fin BB := E69 + Main[31]
  let E71 : Fin BB := Main[47] - E70
  let E72 : Fin BB := 1 - Main[40]
  let E73 : Fin BB := Main[45] * E72
  let E74 : Fin BB := E73 * Main[41]
  let E75 : Fin BB := E74 + Main[32]
  let E76 : Fin BB := Main[48] - E75
  let E77 : Fin BB := Main[45] * Main[40]
  let E78 : Fin BB := E77 * Main[41]
  let E79 : Fin BB := E78 + Main[33]
  let E80 : Fin BB := Main[49] - E79
  let E81 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E81, Main[4], Main[5]] 8 Main[50]
  let CS2 : SP1ConstraintList := ITypeReaderImmutable.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] 24 #v[64, 35, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } Main[50]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E9),
    (.assertZero E12),
    (.assertZero E15),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 6) Main[37] 16 0) Main[50]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[38] 0) Main[50]),
    (.send (.memory Main[34] Main[35] E4 E5 E6 Main[30] Main[31] Main[32] Main[33]) Main[50]),
    (.receive (.memory Main[0] E7 E4 E5 E6 Main[46] Main[47] Main[48] Main[49]) Main[50]),
    (.assertZero E31),
    (.assertZero E37),
    (.assertZero E41),
    (.assertZero E45),
    (.assertZero E48),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[44] E50) Main[50]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[43] E52) Main[50]),
    (.assertZero E60),
    (.assertZero E66),
    (.assertZero E71),
    (.assertZero E76),
    (.assertZero E80),
  ]

end constraints

end StoreByte

end Store
