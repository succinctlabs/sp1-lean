import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader

namespace Add

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

-- Generated Lean code for chip AddChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 33) : SP1ConstraintList F :=
  let E0 : F := Main[32] - 1
  let E1 : F := Main[32] * E0
  let CS0 : SP1ConstraintList F := AddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[22], Main[23], Main[24], Main[25]] { value := #v[Main[28], Main[29], Main[30], Main[31]] } Main[32]
  let E2 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E2, Main[4], Main[5]] 8 Main[32]
  let E3 : F := Main[1] * 65536
  let E4 : F := Main[2] + E3
  let CS2 : SP1ConstraintList F := RTypeReader.constraints Main[0] E4 #v[Main[3], Main[4], Main[5]] 0 #v[Main[28], Main[29], Main[30], Main[31]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } } Main[32] Main[32]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
    (.assertZero Main[13]),
  ]

end constraints

end Add
