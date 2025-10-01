import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader

namespace Add

section constraints

-- Generated Lean code for chip AddChip
@[irreducible] def constraints (Main : Vector (Fin KB) 34) : SP1ConstraintList :=
  let E0 : Fin KB := Main[33] - 1
  let E1 : Fin KB := Main[33] * E0
  let CS0 : SP1ConstraintList := AddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[22], Main[23], Main[24], Main[25]] { value := #v[Main[29], Main[30], Main[31], Main[32]] } Main[33]
  let E2 : Fin KB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E2, Main[4], Main[5]] 8 Main[33]
  let E3 : Fin KB := Main[1] * 65536
  let E4 : Fin KB := Main[2] + E3
  let CS2 : SP1ConstraintList := RTypeReader.constraints Main[0] E4 #v[Main[3], Main[4], Main[5]] 0 #v[8, 51, 0, 0] #v[Main[29], Main[30], Main[31], Main[32]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } }, is_trusted := Main[28] } Main[33]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
  ]

end constraints
