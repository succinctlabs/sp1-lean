import SP1Operations

namespace LtChip

def constraints (Main : Vector (Fin BB) 44) : SP1ConstraintList :=
  let E0 : Fin BB := Main[32] + Main[33]
  let E1 : Fin BB := Main[32] - 1
  let E2 : Fin BB := Main[32] * E1
  let E3 : Fin BB := Main[33] - 1
  let E4 : Fin BB := Main[33] * E3
  let E5 : Fin BB := E0 - 1
  let E6 : Fin BB := E0 * E5
  let CS0 : SP1ConstraintList := LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] E0
  let E7 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E7, Main[4], Main[5]] 8 E0
  let E8 : Fin BB := Main[32] * 9
  let E9 : Fin BB := Main[33] * 10
  let E10 : Fin BB := E8 + E9
  let E11 : Fin BB := Main[1] * 65536
  let E12 : Fin BB := Main[2] + E11
  let E13 : Fin BB := 0 + Main[34]
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E12 #v[Main[3], Main[4], Main[5]] E10 #v[51, 0, 0] #v[E13, 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E0
  [
    (.assertZero E2),
    (.assertZero E4),
    (.assertZero E6),
  ] ++ CS0 ++ CS1 ++ CS2

end LtChip
