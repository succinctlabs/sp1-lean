import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader

namespace Lt

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

-- Generated Lean code for chip LtChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 44) : SP1ConstraintList F :=
  let E0 : F := Main[32] + Main[33]
  let E1 : F := Main[32] - 1
  let E2 : F := Main[32] * E1
  let E3 : F := Main[33] - 1
  let E4 : F := Main[33] * E3
  let E5 : F := E0 - 1
  let E6 : F := E0 * E5
  let CS0 : SP1ConstraintList F := LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] E0
  let E7 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E7, Main[4], Main[5]] 8 E0
  let E8 : F := Main[32] * 9
  let E9 : F := Main[33] * 10
  let E10 : F := E8 + E9
  let E11 : F := Main[32] * 2
  let E12 : F := Main[33] * 3
  let E13 : F := E11 + E12
  let E14 : F := Main[32] * 0
  let E15 : F := Main[33] * 0
  let E16 : F := E14 + E15
  let E17 : F := Main[32] * 51
  let E18 : F := Main[33] * 51
  let E19 : F := E17 + E18
  let E20 : F := 32 * Main[31]
  let E21 : F := E19 - E20
  let E22 : F := Main[32] * 8
  let E23 : F := Main[33] * 8
  let E24 : F := E22 + E23
  let E25 : F := 4 * Main[31]
  let E26 : F := E24 - E25
  let E27 : F := Main[1] * 65536
  let E28 : F := Main[2] + E27
  let E29 : F := 0 + Main[34]
  let CS2 : SP1ConstraintList F := ALUTypeReader.constraints Main[0] E28 #v[Main[3], Main[4], Main[5]] E10 #v[E29, 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E0 E0
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E2),
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero Main[13]),
  ]

end constraints

variable {p : ℕ}

section opcodes

@[simp] def is_slt (Main : Vector (ZMod p) 44) := Main[32] = 1 ∧ Main[31] = 0
  deriving Decidable
@[simp] def is_sltu (Main : Vector (ZMod p) 44) := Main[33] = 1 ∧ Main[31] = 0
  deriving Decidable
@[simp] def is_slti (Main : Vector (ZMod p) 44) := Main[32] = 1 ∧ Main[31] = 1
  deriving Decidable
@[simp] def is_sltiu (Main : Vector (ZMod p) 44) := Main[33] = 1 ∧ Main[31] = 1
  deriving Decidable

end opcodes

end Lt
