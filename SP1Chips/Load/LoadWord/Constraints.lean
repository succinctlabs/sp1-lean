import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Operation.U16MSBOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadWord

section constraints

-- Generated Lean code for chip LoadWordChip
@[irreducible] def constraints (Main : Vector (Fin BB) 46) : SP1ConstraintList :=
  let E0 : Fin BB := Main[1] * 65536
  let E1 : Fin BB := Main[2] + E0
  let E2 : Fin BB := Main[43] * 21
  let E3 : Fin BB := Main[44] * 44
  let E4 : Fin BB := E2 + E3
  let E5 : Fin BB := Main[43] * 2
  let E6 : Fin BB := Main[44] * 6
  let E7 : Fin BB := E5 + E6
  let E8 : Fin BB := Main[43] * 0
  let E9 : Fin BB := Main[44] * 0
  let E10 : Fin BB := E8 + E9
  let E11 : Fin BB := Main[43] * 3
  let E12 : Fin BB := Main[44] * 3
  let E13 : Fin BB := E11 + E12
  let E14 : Fin BB := Main[43] * 4
  let E15 : Fin BB := Main[44] * 4
  let E16 : Fin BB := E14 + E15
  let E17 : Fin BB := Main[43] + Main[44]
  let E18 : Fin BB := Main[43] - 1
  let E19 : Fin BB := Main[43] * E18
  let E20 : Fin BB := Main[44] - 1
  let E21 : Fin BB := Main[44] * E20
  let E22 : Fin BB := E17 - 1
  let E23 : Fin BB := E17 * E22
  let ⟨⟨⟨[E24, E25, E26]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] 0 0 Main[39] E17 { addr_operation := { value := #v[Main[26], Main[27], Main[28]] }, top_two_limb_inv := Main[29] }
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
  let E51 : Fin BB := Main[45] - E50
  let E52 : Fin BB := E1 + 1
  let E53 : Fin BB := Main[39] - 1
  let E54 : Fin BB := Main[40] - Main[30]
  let E55 : Fin BB := E53 * E54
  let E56 : Fin BB := Main[39] - 1
  let E57 : Fin BB := Main[41] - Main[31]
  let E58 : Fin BB := E56 * E57
  let E59 : Fin BB := Main[40] - Main[32]
  let E60 : Fin BB := Main[39] * E59
  let E61 : Fin BB := Main[41] - Main[33]
  let E62 : Fin BB := Main[39] * E61
  let CS1 : SP1ConstraintList := U16MSBOperation.constraints Main[41] { msb := Main[42] } Main[43]
  let E63 : Fin BB := Main[43] - 1
  let E64 : Fin BB := E63 * Main[42]
  let E65 : Fin BB := Main[3] + 4
  let CS2 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E65, Main[4], Main[5]] 8 E17
  let E66 : Fin BB := 65535 * Main[42]
  let E67 : Fin BB := 65535 * Main[42]
  let CS3 : SP1ConstraintList := ITypeReader.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E4 #v[E16, E13, E7, E10] #v[Main[40], Main[41], E66, E67] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } E17
  CS0 ++ CS1 ++ CS2 ++ CS3 ++ [
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
    (.assertZero E55),
    (.assertZero E58),
    (.assertZero E60),
    (.assertZero E62),
    (.assertZero E64),
  ]

end constraints

end LoadWord

end Load
