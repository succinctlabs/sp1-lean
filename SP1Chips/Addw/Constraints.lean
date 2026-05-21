import SP1Operations.Operation.AddwOperation.AddwOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader

namespace Addw

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

-- Generated Lean code for chip AddwChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 36) : SP1ConstraintList F :=
  let E0 : F := Main[35] - 1
  let E1 : F := Main[35] * E0
  let E2 : F := 4 * Main[31]
  let E3 : F := 8 - E2
  let E4 : F := 32 * Main[31]
  let E5 : F := 59 - E4
  let CS0 : SP1ConstraintList F := AddwOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { value := #v[Main[32], Main[33]], msb := { msb := Main[34] } } Main[35]
  let E6 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E6, Main[4], Main[5]] 8 Main[35]
  let E7 : F := Main[34] * 65535
  let E8 : F := Main[34] * 65535
  let E9 : F := Main[1] * 65536
  let E10 : F := Main[2] + E9
  let CS2 : SP1ConstraintList F := ALUTypeReader.constraints Main[0] E10 #v[Main[3], Main[4], Main[5]] 19 #v[Main[32], Main[33], E7, E8] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } Main[35] Main[35]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
    (.assertZero Main[13]),
  ]

end constraints

end Addw
