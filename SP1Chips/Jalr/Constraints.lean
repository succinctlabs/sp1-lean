import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ITypeReader.ITypeReader

namespace Jalr

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

-- Generated Lean code for chip JalrChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 35) : SP1ConstraintList F :=
  let E0 : F := Main[25] - 1
  let E1 : F := Main[25] * E0
  let CS0 : SP1ConstraintList F := AddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[26], Main[27], Main[28], Main[29]] } Main[25]
  let E2 : F := Main[34] - 1
  let E3 : F := Main[34] * E2
  let E4 : F := Main[26] - Main[34]
  let E5 : F := E4 * ((4 : F)⁻¹)
  let E6 : F := Main[26] - Main[34]
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E6, Main[27], Main[28]] 8 Main[25]
  let E7 : F := Main[1] * 65536
  let E8 : F := Main[2] + E7
  let CS2 : SP1ConstraintList F := ITypeReader.constraints Main[0] E8 #v[Main[3], Main[4], Main[5]] 47 #v[Main[30], Main[31], Main[32], Main[33]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } Main[25] Main[25]
  let E9 : F := Main[25] - 1
  let E10 : F := E9 * Main[13]
  let E11 : F := Main[25] - Main[13]
  let CS3 : SP1ConstraintList F := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0] { value := #v[Main[30], Main[31], Main[32], Main[33]] } E11
  let E12 : F := Main[13] * Main[30]
  let E13 : F := Main[13] * Main[31]
  let E14 : F := Main[13] * Main[32]
  CS0 ++ CS1 ++ CS2 ++ CS3 ++ [
    (.assertZero E1),
    (.assertZero Main[29]),
    (.assertZero E3),
    (.send (.byte (ByteOpcode.ofNat 6) E5 14 0) Main[25]),
    (.assertZero E10),
    (.assertZero Main[33]),
    (.assertZero E12),
    (.assertZero E13),
    (.assertZero E14),
  ]

end constraints

section opcodes

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

@[simp] def is_real (Main : Vector (ZMod p) 35) : Prop := Main[25] = 1
  deriving Decidable

end opcodes

end Jalr
