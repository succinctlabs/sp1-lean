import SP1Operations.Reader.CPUState
import SP1Operations.Reader.JTypeReader
import SP1Operations.Operation.AddOperation

namespace UType

section constraints

-- Generated Lean code for chip UTypeChip
def constraints (Main : Vector (Fin BB) 31) : SP1ConstraintList :=
  let E0 : Fin BB := Main[30] - 1
  let E1 : Fin BB := Main[30] * E0
  let E2 : Fin BB := Main[29] - 1
  let E3 : Fin BB := Main[29] * E2
  let E4 : Fin BB := Main[29] * 35
  let E5 : Fin BB := 1 - Main[29]
  let E6 : Fin BB := E5 * 36
  let E7 : Fin BB := E4 + E6
  let E8 : Fin BB := 1 - Main[29]
  let E9 : Fin BB := Main[29] * 0
  let E10 : Fin BB := E8 * 0
  let E11 : Fin BB := E9 + E10
  let E12 : Fin BB := Main[29] * 0
  let E13 : Fin BB := E8 * 0
  let E14 : Fin BB := E12 + E13
  let E15 : Fin BB := Main[29] * 23
  let E16 : Fin BB := E8 * 55
  let E17 : Fin BB := E15 + E16
  let E18 : Fin BB := Main[3] + 4
  let CS0 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E18, Main[4], Main[5]] 8 Main[30]
  let E19 : Fin BB := Main[29] * Main[3]
  let E20 : Fin BB := 1 - Main[29]
  let E21 : Fin BB := E20 * 0
  let E22 : Fin BB := E19 + E21
  let E23 : Fin BB := Main[29] * Main[4]
  let E24 : Fin BB := 1 - Main[29]
  let E25 : Fin BB := E24 * 0
  let E26 : Fin BB := E23 + E25
  let E27 : Fin BB := Main[29] * Main[5]
  let E28 : Fin BB := 1 - Main[29]
  let E29 : Fin BB := E28 * 0
  let E30 : Fin BB := E27 + E29
  let E31 : Fin BB := Main[29] * 0
  let E32 : Fin BB := 1 - Main[29]
  let E33 : Fin BB := E32 * 0
  let E34 : Fin BB := E31 + E33
  let E35 : Fin BB := Main[22] - E22
  let E36 : Fin BB := Main[23] - E26
  let E37 : Fin BB := Main[24] - E30
  let E38 : Fin BB := 0 - E34
  let E39 : Fin BB := Main[30] - 1
  let E40 : Fin BB := E39 * Main[13]
  let E41 : Fin BB := Main[30] - Main[13]
  let CS1 : SP1ConstraintList := AddOperation.constraints #v[Main[22], Main[23], Main[24], 0] #v[Main[14], Main[15], Main[16], Main[17]] { value := #v[Main[25], Main[26], Main[27], Main[28]] } E41
  let E42 : Fin BB := Main[1] * 65536
  let E43 : Fin BB := Main[2] + E42
  let CS2 : SP1ConstraintList := JTypeReader.constraints Main[0] E43 #v[Main[3], Main[4], Main[5]] E7 #v[E17, E11, E14] #v[Main[25], Main[26], Main[27], Main[28]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]], op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] } Main[30]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
    (.assertZero E3),
    (.assertZero E35),
    (.assertZero E36),
    (.assertZero E37),
    (.assertZero E38),
    (.assertZero E40),
  ]

end constraints

end UType
