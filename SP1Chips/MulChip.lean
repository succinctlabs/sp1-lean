import SP1Operations

namespace MulChip

def constraints (Main : Vector (Fin BB) 88) : SP1ConstraintList :=
  let CS0 : SP1ConstraintList := MulOperation.constraints #v[Main[32], Main[33], Main[34], Main[35]] #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { carry := #v[Main[36], Main[37], Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47], Main[48], Main[49], Main[50], Main[51]], product := #v[Main[52], Main[53], Main[54], Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61], Main[62], Main[63], Main[64], Main[65], Main[66], Main[67]], b_lower_byte := { low_bytes := #v[Main[68], Main[69], Main[70], Main[71]] }, c_lower_byte := { low_bytes := #v[Main[72], Main[73], Main[74], Main[75]] }, b_msb := Main[76], c_msb := Main[77], product_msb := { msb := Main[78] }, b_sign_extend := Main[79], c_sign_extend := Main[80], is_mulw := Main[81] } Main[82] Main[83] Main[84] Main[87] Main[85] Main[86]
  let E0 : Fin BB := Main[83] + Main[84]
  let E1 : Fin BB := E0 + Main[85]
  let E2 : Fin BB := E1 + Main[86]
  let E3 : Fin BB := E2 + Main[87]
  let E4 : Fin BB := Main[82] - E3
  let E5 : Fin BB := Main[83] - 1
  let E6 : Fin BB := Main[83] * E5
  let E7 : Fin BB := Main[84] - 1
  let E8 : Fin BB := Main[84] * E7
  let E9 : Fin BB := Main[85] - 1
  let E10 : Fin BB := Main[85] * E9
  let E11 : Fin BB := Main[87] - 1
  let E12 : Fin BB := Main[87] * E11
  let E13 : Fin BB := Main[86] - 1
  let E14 : Fin BB := Main[86] * E13
  let E15 : Fin BB := Main[82] - 1
  let E16 : Fin BB := Main[82] * E15
  let E17 : Fin BB := Main[83] * 11
  let E18 : Fin BB := Main[84] * 12
  let E19 : Fin BB := E17 + E18
  let E20 : Fin BB := Main[85] * 13
  let E21 : Fin BB := E19 + E20
  let E22 : Fin BB := Main[86] * 14
  let E23 : Fin BB := E21 + E22
  let E24 : Fin BB := Main[87] * 47
  let E25 : Fin BB := E23 + E24
  let E26 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E26, Main[4], Main[5]] 8 Main[82]
  let E27 : Fin BB := Main[1] * 65536
  let E28 : Fin BB := Main[2] + E27
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E28 #v[Main[3], Main[4], Main[5]] E25 #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } Main[82]
  [
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.assertZero E12),
    (.assertZero E14),
    (.assertZero E16),
  ] ++ CS0 ++ CS1 ++ CS2

end MulChip
