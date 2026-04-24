import SP1Operations.Operation.AddOperation

namespace Jal

section constraints

-- Generated Lean code for chip JalChip
@[irreducible] def constraints (Main : Vector (Fin KB) 31) : SP1ConstraintList :=
  let E0 : Fin KB := Main[30] - 1
  let E1 : Fin KB := Main[30] * E0
  let CS0 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[Main[14], Main[15], Main[16], Main[17]] { value := #v[Main[22], Main[23], Main[24], Main[25]] } Main[30]
  let E2 : Fin KB := Main[22] * 1598029825
  let E3 : Fin KB := Main[1] * 65536
  let E4 : Fin KB := Main[2] + E3
  let E5 : Fin KB := Main[30] - 1
  let E6 : Fin KB := Main[30] * E5
  let E7 : Fin KB := E4 + 8
  let E8 : Fin KB := Main[2] - 1
  let E9 : Fin KB := E8 * 1864368129
  let E10 : Fin KB := Main[30] - 1
  let E11 : Fin KB := E10 * Main[13]
  let E12 : Fin KB := Main[30] - Main[13]
  let CS1 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0] { value := #v[Main[26], Main[27], Main[28], Main[29]] } E12
  let E13 : Fin KB := Main[13] * Main[26]
  let E14 : Fin KB := Main[13] * Main[27]
  let E15 : Fin KB := Main[13] * Main[28]
  let E16 : Fin KB := Main[1] * 65536
  let E17 : Fin KB := Main[2] + E16
  let E18 : Fin KB := Main[30] - 1
  let E19 : Fin KB := Main[30] * E18
  let E20 : Fin KB := Main[26] - 0
  let E21 : Fin KB := Main[13] * E20
  let E22 : Fin KB := Main[27] - 0
  let E23 : Fin KB := Main[13] * E22
  let E24 : Fin KB := Main[28] - 0
  let E25 : Fin KB := Main[13] * E24
  let E26 : Fin KB := Main[29] - 0
  let E27 : Fin KB := Main[13] * E26
  let E28 : Fin KB := E17 + 4
  let E29 : Fin KB := Main[30] - 1
  let E30 : Fin KB := Main[30] * E29
  let E31 : Fin KB := E28 - Main[11]
  let E32 : Fin KB := E31 - 1
  let E33 : Fin KB := E32 - Main[12]
  let E34 : Fin KB := E33 * 2130673921
  CS0 ++ CS1 ++ [
    (.assertZero E1),
    (.assertZero Main[25]),
    (.send (.byte (ByteOpcode.ofNat 6) E2 14 0) Main[30]),
    (.assertZero E6),
    (.receive (.state Main[0] E4 Main[3] Main[4] Main[5]) Main[30]),
    (.send (.state Main[0] E7 Main[22] Main[23] Main[24]) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 6) E9 13 0) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0) Main[30]),
    (.assertZero E11),
    (.assertZero Main[29]),
    (.assertZero E13),
    (.assertZero E14),
    (.assertZero E15),
    (.assertZero E19),
    (.send (.program Main[3] Main[4] Main[5] (Opcode.ofNat 46) Main[6] Main[14] Main[15] Main[16] Main[17] Main[18] Main[19] Main[20] Main[21] Main[13] 1 1) Main[30]),
    (.assertZero E21),
    (.assertZero E23),
    (.assertZero E25),
    (.assertZero E27),
    (.assertZero E30),
    (.send (.byte (ByteOpcode.ofNat 6) Main[12] 16 0) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E34 0) Main[30]),
    (.send (.memory Main[0] Main[11] Main[6] 0 0 Main[7] Main[8] Main[9] Main[10]) Main[30]),
    (.receive (.memory Main[0] E28 Main[6] 0 0 Main[26] Main[27] Main[28] Main[29]) Main[30]),
  ]

end constraints

end Jal
