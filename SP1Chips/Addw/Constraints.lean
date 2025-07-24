import SP1Operations

namespace Addw

section constraints

-- Generated Lean code for chip AddwChip
def constraints (Main : Vector (Fin BB) 37) : SP1ConstraintList :=
  let E0 : Fin BB := Main[35] - 1
  let E1 : Fin BB := Main[35] * E0
  let E2 : Fin BB := Main[31] * 27
  let E3 : Fin BB := 1 - Main[31]
  let E4 : Fin BB := E3 * 59
  let E5 : Fin BB := E2 + E4
  let E6 : Fin BB := Main[36] - E5
  let E7 : Fin BB := Main[35] * E6
  let CS0 : SP1ConstraintList := AddwOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { value := #v[Main[32], Main[33]], msb := { msb := Main[34] } } Main[35]
  let E8 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E8, Main[4], Main[5]] 8 Main[35]
  let E9 : Fin BB := Main[34] * 65535
  let E10 : Fin BB := Main[34] * 65535
  let E11 : Fin BB := Main[1] * 65536
  let E12 : Fin BB := Main[2] + E11
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E12 #v[Main[3], Main[4], Main[5]] 39 #v[Main[36], 0, 0] #v[Main[32], Main[33], E9, E10] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } Main[35]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
    (.assertZero E7),
  ]

end constraints

end Addw
