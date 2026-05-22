import SP1Operations.Operation.BitwiseU16Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader

namespace Bitwise

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

-- Generated Lean code for chip BitwiseChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 51) : SP1ConstraintList F :=
  let E0 : F := Main[48] + Main[49]
  let E1 : F := E0 + Main[50]
  let E2 : F := Main[48] - 1
  let E3 : F := Main[48] * E2
  let E4 : F := Main[49] - 1
  let E5 : F := Main[49] * E4
  let E6 : F := Main[50] - 1
  let E7 : F := Main[50] * E6
  let E8 : F := E1 - 1
  let E9 : F := E1 * E8
  let E10 : F := Main[48] * 2
  let E11 : F := Main[49] * 1
  let E12 : F := E10 + E11
  let E13 : F := Main[50] * 0
  let E14 : F := E12 + E13
  let E15 : F := Main[48] * 3
  let E16 : F := Main[49] * 4
  let E17 : F := E15 + E16
  let E18 : F := Main[50] * 5
  let E19 : F := E17 + E18
  let E20 : F := Main[48] * 4
  let E21 : F := Main[49] * 6
  let E22 : F := E20 + E21
  let E23 : F := Main[50] * 7
  let E24 : F := E22 + E23
  let E25 : F := Main[48] * 0
  let E26 : F := Main[49] * 0
  let E27 : F := E25 + E26
  let E28 : F := Main[50] * 0
  let E29 : F := E27 + E28
  let E30 : F := Main[48] * 51
  let E31 : F := Main[49] * 51
  let E32 : F := E30 + E31
  let E33 : F := Main[50] * 51
  let E34 : F := E32 + E33
  let E35 : F := 32 * Main[31]
  let E36 : F := E34 - E35
  let E37 : F := Main[48] * 8
  let E38 : F := Main[49] * 8
  let E39 : F := E37 + E38
  let E40 : F := Main[50] * 8
  let E41 : F := E39 + E40
  let E42 : F := 4 * Main[31]
  let E43 : F := E41 - E42
  let ⟨⟨⟨[E44, E45, E46, E47]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } E14 E1
  let E48 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E48, Main[4], Main[5]] 8 E1
  let E49 : F := Main[1] * 65536
  let E50 : F := Main[2] + E49
  let CS2 : SP1ConstraintList F := ALUTypeReader.constraints Main[0] E50 #v[Main[3], Main[4], Main[5]] E19 #v[E44, E45, E46, E47] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E1 E1
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero Main[13]),
  ]

end constraints

variable {p : ℕ}

section opcodes

@[simp] def is_real (Main : Vector (ZMod p) 51) : Prop :=
  Main[48] = 1 ∨ Main[49] = 1 ∨ Main[50] = 1
  deriving Decidable

@[simp] def is_xor (Main : Vector (ZMod p) 51) := Main[48] = 1 ∧ Main[31] = 0
  deriving Decidable
@[simp] def is_xori (Main : Vector (ZMod p) 51) := Main[48] = 1 ∧ Main[31] = 1
  deriving Decidable
@[simp] def is_or (Main : Vector (ZMod p) 51) := Main[49] = 1 ∧ Main[31] = 0
  deriving Decidable
@[simp] def is_ori (Main : Vector (ZMod p) 51) := Main[49] = 1 ∧ Main[31] = 1
  deriving Decidable
@[simp] def is_and (Main : Vector (ZMod p) 51) := Main[50] = 1 ∧ Main[31] = 0
  deriving Decidable
@[simp] def is_andi (Main : Vector (ZMod p) 51) := Main[50] = 1 ∧ Main[31] = 1
  deriving Decidable

end opcodes

end Bitwise
