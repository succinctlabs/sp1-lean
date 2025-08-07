import SP1Operations.Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace Bitwise

section constraints

-- Generated Lean code for chip BitwiseChip
def constraints (Main : Vector (Fin BB) 52) : SP1ConstraintList :=
  let E0 : Fin BB := Main[48] + Main[49]
  let E1 : Fin BB := E0 + Main[50]
  let E2 : Fin BB := Main[48] - 1
  let E3 : Fin BB := Main[48] * E2
  let E4 : Fin BB := Main[49] - 1
  let E5 : Fin BB := Main[49] * E4
  let E6 : Fin BB := Main[50] - 1
  let E7 : Fin BB := Main[50] * E6
  let E8 : Fin BB := E1 - 1
  let E9 : Fin BB := E1 * E8
  let E10 : Fin BB := Main[48] * 2
  let E11 : Fin BB := Main[49] * 1
  let E12 : Fin BB := E10 + E11
  let E13 : Fin BB := Main[50] * 0
  let E14 : Fin BB := E12 + E13
  let E15 : Fin BB := Main[48] * 3
  let E16 : Fin BB := Main[49] * 4
  let E17 : Fin BB := E15 + E16
  let E18 : Fin BB := Main[50] * 5
  let E19 : Fin BB := E17 + E18
  let E20 : Fin BB := Main[48] * 4
  let E21 : Fin BB := Main[49] * 6
  let E22 : Fin BB := E20 + E21
  let E23 : Fin BB := Main[50] * 7
  let E24 : Fin BB := E22 + E23
  let E25 : Fin BB := Main[48] * 0
  let E26 : Fin BB := Main[49] * 0
  let E27 : Fin BB := E25 + E26
  let E28 : Fin BB := Main[50] * 0
  let E29 : Fin BB := E27 + E28
  let E30 : Fin BB := Main[48] * 19
  let E31 : Fin BB := Main[49] * 19
  let E32 : Fin BB := E30 + E31
  let E33 : Fin BB := Main[50] * 19
  let E34 : Fin BB := E32 + E33
  let E35 : Fin BB := Main[48] * 51
  let E36 : Fin BB := Main[49] * 51
  let E37 : Fin BB := E35 + E36
  let E38 : Fin BB := Main[50] * 51
  let E39 : Fin BB := E37 + E38
  let E40 : Fin BB := Main[31] * E34
  let E41 : Fin BB := 1 - Main[31]
  let E42 : Fin BB := E41 * E39
  let E43 : Fin BB := E40 + E42
  let E44 : Fin BB := Main[51] - E43
  let E45 : Fin BB := E1 * E44
  let ⟨⟨⟨[E46, E47, E48, E49]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } E14 E1
  let E50 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E50, Main[4], Main[5]] 8 E1
  let E51 : Fin BB := Main[1] * 65536
  let E52 : Fin BB := Main[2] + E51
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E52 #v[Main[3], Main[4], Main[5]] E19 #v[Main[51], E24, E29] #v[E46, E47, E48, E49] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E1
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E45),
  ]

end constraints

end Bitwise
