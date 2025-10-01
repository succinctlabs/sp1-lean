import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader

namespace Jalr

section constraints

-- Generated Lean code for chip JalrChip
@[irreducible] def constraints (Main : Vector (Fin KB) 39) : SP1ConstraintList :=
  let E0 : Fin KB := Main[30] - 1
  let E1 : Fin KB := Main[30] * E0
  let CS0 : SP1ConstraintList := AddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[31], Main[32], Main[33], Main[34]] } Main[30]
  let E2 : Fin KB := Main[31] * 1598029825
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[31], Main[32], Main[33]] 8 Main[30]
  let E3 : Fin KB := Main[1] * 65536
  let E4 : Fin KB := Main[2] + E3
  let CS2 : SP1ConstraintList := ITypeReader.constraints Main[0] E4 #v[Main[3], Main[4], Main[5]] 34 #v[4, 103, 0, 0] #v[Main[35], Main[36], Main[37], Main[38]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } Main[30]
  let E5 : Fin KB := Main[30] - 1
  let E6 : Fin KB := E5 * Main[13]
  let E7 : Fin KB := Main[30] - Main[13]
  let CS3 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0] { value := #v[Main[35], Main[36], Main[37], Main[38]] } E7
  let E8 : Fin KB := Main[13] * Main[35]
  let E9 : Fin KB := Main[13] * Main[36]
  let E10 : Fin KB := Main[13] * Main[37]
  CS0 ++ CS1 ++ CS2 ++ CS3 ++ [
    (.assertZero E1),
    (.assertZero Main[34]),
    (.send (.byte (ByteOpcode.ofNat 6) E2 14 0) Main[30]),
    (.assertZero E6),
    (.assertZero Main[38]),
    (.assertZero E8),
    (.assertZero E9),
    (.assertZero E10),
  ]

end constraints
