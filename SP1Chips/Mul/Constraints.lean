import SP1Operations

namespace Mul

section constraints

-- Generated Lean code for chip MulChip
def constraints (Main : Vector (Fin BB) 87) : SP1ConstraintList :=
  let E0 : Fin BB := Main[81] + Main[82]
  let E1 : Fin BB := E0 + Main[83]
  let E2 : Fin BB := E1 + Main[84]
  let E3 : Fin BB := E2 + Main[85]
  let CS0 : SP1ConstraintList := MulOperation.constraints #v[Main[32], Main[33], Main[34], Main[35]] #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { carry := #v[Main[36], Main[37], Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47], Main[48], Main[49], Main[50], Main[51]], product := #v[Main[52], Main[53], Main[54], Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61], Main[62], Main[63], Main[64], Main[65], Main[66], Main[67]], b_lower_byte := { low_bytes := #v[Main[68], Main[69], Main[70], Main[71]] }, c_lower_byte := { low_bytes := #v[Main[72], Main[73], Main[74], Main[75]] }, b_msb := Main[76], c_msb := Main[77], product_msb := { msb := Main[78] }, b_sign_extend := Main[79], c_sign_extend := Main[80] } E3 Main[81] Main[82] Main[85] Main[83] Main[84]
  let E4 : Fin BB := Main[81] - 1
  let E5 : Fin BB := Main[81] * E4
  let E6 : Fin BB := Main[82] - 1
  let E7 : Fin BB := Main[82] * E6
  let E8 : Fin BB := Main[83] - 1
  let E9 : Fin BB := Main[83] * E8
  let E10 : Fin BB := Main[85] - 1
  let E11 : Fin BB := Main[85] * E10
  let E12 : Fin BB := Main[84] - 1
  let E13 : Fin BB := Main[84] * E12
  let E14 : Fin BB := E3 - 1
  let E15 : Fin BB := E3 * E14
  let E16 : Fin BB := Main[81] * 11
  let E17 : Fin BB := Main[82] * 12
  let E18 : Fin BB := E16 + E17
  let E19 : Fin BB := Main[83] * 13
  let E20 : Fin BB := E18 + E19
  let E21 : Fin BB := Main[84] * 14
  let E22 : Fin BB := E20 + E21
  let E23 : Fin BB := Main[85] * 47
  let E24 : Fin BB := E22 + E23
  let E25 : Fin BB := Main[81] * 0
  let E26 : Fin BB := Main[82] * 1
  let E27 : Fin BB := E25 + E26
  let E28 : Fin BB := Main[83] * 3
  let E29 : Fin BB := E27 + E28
  let E30 : Fin BB := Main[84] * 2
  let E31 : Fin BB := E29 + E30
  let E32 : Fin BB := Main[85] * 0
  let E33 : Fin BB := E31 + E32
  let E34 : Fin BB := Main[81] * 1
  let E35 : Fin BB := Main[82] * 1
  let E36 : Fin BB := E34 + E35
  let E37 : Fin BB := Main[83] * 1
  let E38 : Fin BB := E36 + E37
  let E39 : Fin BB := Main[84] * 1
  let E40 : Fin BB := E38 + E39
  let E41 : Fin BB := Main[85] * 1
  let E42 : Fin BB := E40 + E41
  let E43 : Fin BB := Main[85] * 27
  let E44 : Fin BB := Main[81] * 51
  let E45 : Fin BB := Main[82] * 51
  let E46 : Fin BB := E44 + E45
  let E47 : Fin BB := Main[83] * 51
  let E48 : Fin BB := E46 + E47
  let E49 : Fin BB := Main[84] * 51
  let E50 : Fin BB := E48 + E49
  let E51 : Fin BB := Main[85] * 59
  let E52 : Fin BB := E50 + E51
  let E53 : Fin BB := Main[31] * E43
  let E54 : Fin BB := 1 - Main[31]
  let E55 : Fin BB := E54 * E52
  let E56 : Fin BB := E53 + E55
  let E57 : Fin BB := Main[86] - E56
  let E58 : Fin BB := E3 * E57
  let E59 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E59, Main[4], Main[5]] 8 E3
  let E60 : Fin BB := Main[1] * 65536
  let E61 : Fin BB := Main[2] + E60
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E61 #v[Main[3], Main[4], Main[5]] E24 #v[Main[86], E33, E42] #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E3
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E11),
    (.assertZero E13),
    (.assertZero E15),
    (.assertZero E58),
  ]

end constraints

end Mul
