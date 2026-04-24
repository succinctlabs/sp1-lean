import SP1Operations.Reader.CPUState
import SP1Operations.Reader.JTypeReader
import SP1Operations.Operation.AddOperation

namespace UType

section constraints

-- Generated Lean code for chip UTypeChip
@[irreducible] def constraints (Main : Vector (Fin KB) 31) : SP1ConstraintList :=
  let E0 : Fin KB := Main[30] - 1
  let E1 : Fin KB := Main[30] * E0
  let E2 : Fin KB := Main[29] - 1
  let E3 : Fin KB := Main[29] * E2
  let E4 : Fin KB := Main[29] * 48
  let E5 : Fin KB := 1 - Main[29]
  let E6 : Fin KB := E5 * 49
  let E7 : Fin KB := E4 + E6
  let E8 : Fin KB := 1 - Main[29]
  let E9 : Fin KB := Main[29] * 0
  let E10 : Fin KB := E8 * 0
  let E11 : Fin KB := E9 + E10
  let E12 : Fin KB := Main[29] * 0
  let E13 : Fin KB := E8 * 0
  let E14 : Fin KB := E12 + E13
  let E15 : Fin KB := Main[29] * 23
  let E16 : Fin KB := E8 * 55
  let E17 : Fin KB := E15 + E16
  let E18 : Fin KB := Main[29] * 128
  let E19 : Fin KB := E8 * 128
  let E20 : Fin KB := E18 + E19
  let E21 : Fin KB := Main[3] + 4
  let CS0 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E21, Main[4], Main[5]] 8 Main[30]
  let E22 : Fin KB := Main[29] * Main[3]
  let E23 : Fin KB := 1 - Main[29]
  let E24 : Fin KB := E23 * 0
  let E25 : Fin KB := E22 + E24
  let E26 : Fin KB := Main[29] * Main[4]
  let E27 : Fin KB := 1 - Main[29]
  let E28 : Fin KB := E27 * 0
  let E29 : Fin KB := E26 + E28
  let E30 : Fin KB := Main[29] * Main[5]
  let E31 : Fin KB := 1 - Main[29]
  let E32 : Fin KB := E31 * 0
  let E33 : Fin KB := E30 + E32
  let E34 : Fin KB := Main[29] * 0
  let E35 : Fin KB := 1 - Main[29]
  let E36 : Fin KB := E35 * 0
  let E37 : Fin KB := E34 + E36
  let E38 : Fin KB := Main[22] - E25
  let E39 : Fin KB := Main[23] - E29
  let E40 : Fin KB := Main[24] - E33
  let E41 : Fin KB := 0 - E37
  let E42 : Fin KB := Main[30] - 1
  let E43 : Fin KB := E42 * Main[13]
  let E44 : Fin KB := Main[30] - Main[13]
  let CS1 : SP1ConstraintList := AddOperation.constraints #v[Main[22], Main[23], Main[24], 0] #v[Main[14], Main[15], Main[16], Main[17]] { value := #v[Main[25], Main[26], Main[27], Main[28]] } E44
  let E45 : Fin KB := Main[1] * 65536
  let E46 : Fin KB := Main[2] + E45
  let CS2 : SP1ConstraintList := JTypeReader.constraints Main[0] E46 #v[Main[3], Main[4], Main[5]] E7 #v[E20, E17, E11, E14] #v[Main[25], Main[26], Main[27], Main[28]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]], op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] } Main[30]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
    (.assertZero E3),
    (.assertZero E38),
    (.assertZero E39),
    (.assertZero E40),
    (.assertZero E41),
    (.assertZero E43),
  ]

end constraints

end UType
