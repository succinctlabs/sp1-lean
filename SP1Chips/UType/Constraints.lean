import SP1Operations.Reader.CPUState
import SP1Operations.Reader.JTypeReader
import SP1Operations.Operation.AddOperation

namespace UType

section constraints

-- Generated Lean code for chip UTypeChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 31) : SP1ConstraintList F :=
  let E0 : F := Main[30] - 1
  let E1 : F := Main[30] * E0
  let E2 : F := Main[29] - 1
  let E3 : F := Main[29] * E2
  let E4 : F := Main[29] * 48
  let E5 : F := 1 - Main[29]
  let E6 : F := E5 * 49
  let E7 : F := E4 + E6
  let E8 : F := 1 - Main[29]
  let E9 : F := Main[29] * 0
  let E10 : F := E8 * 0
  let E11 : F := E9 + E10
  let E12 : F := Main[29] * 0
  let E13 : F := E8 * 0
  let E14 : F := E12 + E13
  let E15 : F := Main[29] * 23
  let E16 : F := E8 * 55
  let E17 : F := E15 + E16
  let E18 : F := Main[29] * 128
  let E19 : F := E8 * 128
  let E20 : F := E18 + E19
  let E21 : F := Main[3] + 4
  let CS0 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E21, Main[4], Main[5]] 8 Main[30]
  let E22 : F := Main[29] * Main[3]
  let E23 : F := 1 - Main[29]
  let E24 : F := E23 * 0
  let E25 : F := E22 + E24
  let E26 : F := Main[29] * Main[4]
  let E27 : F := 1 - Main[29]
  let E28 : F := E27 * 0
  let E29 : F := E26 + E28
  let E30 : F := Main[29] * Main[5]
  let E31 : F := 1 - Main[29]
  let E32 : F := E31 * 0
  let E33 : F := E30 + E32
  let E34 : F := Main[29] * 0
  let E35 : F := 1 - Main[29]
  let E36 : F := E35 * 0
  let E37 : F := E34 + E36
  let E38 : F := Main[22] - E25
  let E39 : F := Main[23] - E29
  let E40 : F := Main[24] - E33
  let E41 : F := 0 - E37
  let E42 : F := Main[30] - 1
  let E43 : F := E42 * Main[13]
  let E44 : F := Main[30] - Main[13]
  let CS1 : SP1ConstraintList F := AddOperation.constraints #v[Main[22], Main[23], Main[24], 0] #v[Main[14], Main[15], Main[16], Main[17]] { value := #v[Main[25], Main[26], Main[27], Main[28]] } E44
  let E45 : F := Main[1] * 65536
  let E46 : F := Main[2] + E45
  let CS2 : SP1ConstraintList F := JTypeReader.constraints Main[0] E46 #v[Main[3], Main[4], Main[5]] E7 #v[E20, E17, E11, E14] #v[Main[25], Main[26], Main[27], Main[28]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]], op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] } Main[30]
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
