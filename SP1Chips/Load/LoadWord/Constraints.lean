import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Operation.U16MSBOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace Load

namespace LoadWord


section constraints

-- Generated Lean code for chip LoadWordChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 44) : SP1ConstraintList F :=
  let E0 : F := Main[1] * 65536
  let E1 : F := Main[2] + E0
  let E2 : F := Main[42] * 31
  let E3 : F := Main[43] * 34
  let E4 : F := E2 + E3
  let E5 : F := Main[42] * 2
  let E6 : F := Main[43] * 6
  let E7 : F := E5 + E6
  let E8 : F := Main[42] * 0
  let E9 : F := Main[43] * 0
  let E10 : F := E8 + E9
  let E11 : F := Main[42] * 3
  let E12 : F := Main[43] * 3
  let E13 : F := E11 + E12
  let E14 : F := Main[42] * 4
  let E15 : F := Main[43] * 4
  let E16 : F := E14 + E15
  let E17 : F := Main[42] + Main[43]
  let E18 : F := Main[42] - 1
  let E19 : F := Main[42] * E18
  let E20 : F := Main[43] - 1
  let E21 : F := Main[43] * E20
  let E22 : F := E17 - 1
  let E23 : F := E17 * E22
  let ⟨⟨⟨[E24, E25, E26]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] 0 0 Main[38] E17 { addr_operation := { value := #v[Main[25], Main[26], Main[27]] }, top_two_limb_inv := Main[28] }
  let E27 : F := E1 + 1
  let E28 : F := E17 - 1
  let E29 : F := E17 * E28
  let E30 : F := Main[35] - 1
  let E31 : F := Main[35] * E30
  let E32 : F := E17 * E31
  let E33 : F := Main[0] - Main[33]
  let E34 : F := Main[35] * E33
  let E35 : F := E17 * E34
  let E36 : F := Main[35] * Main[34]
  let E37 : F := 1 - Main[35]
  let E38 : F := E37 * Main[33]
  let E39 : F := E36 + E38
  let E40 : F := Main[35] * E27
  let E41 : F := 1 - Main[35]
  let E42 : F := E41 * Main[0]
  let E43 : F := E40 + E42
  let E44 : F := E43 - E39
  let E45 : F := E44 - 1
  let E46 : F := Main[37] * 65536
  let E47 : F := Main[36] + E46
  let E48 : F := E45 - E47
  let E49 : F := E17 * E48
  let E50 : F := Main[38] - 1
  let E51 : F := Main[39] - Main[29]
  let E52 : F := E50 * E51
  let E53 : F := Main[38] - 1
  let E54 : F := Main[40] - Main[30]
  let E55 : F := E53 * E54
  let E56 : F := Main[39] - Main[31]
  let E57 : F := Main[38] * E56
  let E58 : F := Main[40] - Main[32]
  let E59 : F := Main[38] * E58
  let CS1 : SP1ConstraintList F := U16MSBOperation.constraints Main[40] { msb := Main[41] } Main[42]
  let E60 : F := Main[42] - 1
  let E61 : F := E60 * Main[41]
  let E62 : F := Main[3] + 4
  let CS2 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E62, Main[4], Main[5]] 8 E17
  let E63 : F := 65535 * Main[41]
  let E64 : F := 65535 * Main[41]
  let CS3 : SP1ConstraintList F := ITypeReader.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E4 #v[Main[39], Main[40], E63, E64] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E17 E17
  CS0 ++ CS1 ++ CS2 ++ CS3 ++ [
    (.assertZero E19),
    (.assertZero E21),
    (.assertZero E23),
    (.assertZero E29),
    (.assertZero E32),
    (.assertZero E35),
    (.assertZero E49),
    (.send (.byte (ByteOpcode.ofNat 6) Main[36] 16 0) E17),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[37] 0) E17),
    (.send (.memory Main[33] Main[34] E24 E25 E26 Main[29] Main[30] Main[31] Main[32]) E17),
    (.receive (.memory Main[0] E27 E24 E25 E26 Main[29] Main[30] Main[31] Main[32]) E17),
    (.assertZero Main[13]),
    (.assertZero E52),
    (.assertZero E55),
    (.assertZero E57),
    (.assertZero E59),
    (.assertZero E61),
  ]

end constraints

variable {p : ℕ}

section opcodes

@[simp] def is_lw (Main : Vector (ZMod p) 44) : Prop := Main[42] = 1
  deriving Decidable
@[simp] def is_lwu (Main : Vector (ZMod p) 44) : Prop := Main[43] = 1
  deriving Decidable

end opcodes

end LoadWord

end Load
