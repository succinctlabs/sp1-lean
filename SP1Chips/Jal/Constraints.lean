import SP1Operations.Operation.AddOperation

namespace Jal

section constraints

-- Generated Lean code for chip JalChip
@[irreducible] def constraints (Main : Vector (Fin BB) 32) : SP1ConstraintList :=
  let E0 : Fin BB := Main[31] - 1
  let E1 : Fin BB := Main[31] * E0
  let CS0 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[Main[14], Main[15], Main[16], Main[17]] { value := #v[Main[23], Main[24], Main[25], Main[26]] } Main[31]
  let E2 : Fin BB := Main[23] * 1598029825
  let E3 : Fin BB := Main[1] * 65536
  let E4 : Fin BB := Main[2] + E3
  let E5 : Fin BB := Main[31] - 1
  let E6 : Fin BB := Main[31] * E5
  let E7 : Fin BB := E4 + 8
  let E8 : Fin BB := Main[2] - 1
  let E9 : Fin BB := E8 * 1864368129
  let E10 : Fin BB := Main[31] - 1
  let E11 : Fin BB := E10 * Main[13]
  let E12 : Fin BB := Main[31] - Main[13]
  let CS1 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0] { value := #v[Main[27], Main[28], Main[29], Main[30]] } E12
  let E13 : Fin BB := Main[13] * Main[27]
  let E14 : Fin BB := Main[13] * Main[28]
  let E15 : Fin BB := Main[13] * Main[29]
  let E16 : Fin BB := Main[1] * 65536
  let E17 : Fin BB := Main[2] + E16
  let E18 : Fin BB := Main[31] - 1
  let E19 : Fin BB := Main[31] * E18
  let E20 : Fin BB := Main[31] - Main[22]
  let E21 : Fin BB := E20 - 1
  let E22 : Fin BB := E20 * E21
  let E23 : Fin BB := Main[22] - 1
  let E24 : Fin BB := Main[22] * E23
  let E25 : Fin BB := E20 + Main[22]
  let E26 : Fin BB := E25 - Main[31]
  let E27 : Fin BB := mprotect_enabled () - 1
  let E28 : Fin BB := E20 * E27
  let E29 : Fin BB := Main[27] - 0
  let E30 : Fin BB := Main[13] * E29
  let E31 : Fin BB := Main[28] - 0
  let E32 : Fin BB := Main[13] * E31
  let E33 : Fin BB := Main[29] - 0
  let E34 : Fin BB := Main[13] * E33
  let E35 : Fin BB := Main[30] - 0
  let E36 : Fin BB := Main[13] * E35
  let E37 : Fin BB := E17 + 4
  let E38 : Fin BB := Main[31] - 1
  let E39 : Fin BB := Main[31] * E38
  let E40 : Fin BB := E37 - Main[11]
  let E41 : Fin BB := E40 - 1
  let E42 : Fin BB := E41 - Main[12]
  let E43 : Fin BB := E42 * 2130673921
  CS0 ++ CS1 ++ [
    (.assertZero E1),
    (.assertZero Main[26]),
    (.send (.byte (ByteOpcode.ofNat 6) E2 14 0) Main[31]),
    (.assertZero E6),
    (.receive (.state Main[0] E4 Main[3] Main[4] Main[5]) Main[31]),
    (.send (.state Main[0] E7 Main[23] Main[24] Main[25]) Main[31]),
    (.send (.byte (ByteOpcode.ofNat 6) E9 13 0) Main[31]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0) Main[31]),
    (.assertZero E11),
    (.assertZero Main[30]),
    (.assertZero E13),
    (.assertZero E14),
    (.assertZero E15),
    (.assertZero E19),
    (.assertZero E22),
    (.assertZero E24),
    (.assertZero E26),
    (.assertZero E28),
    (.send (.program Main[3] Main[4] Main[5] (Opcode.ofNat 33) Main[6] Main[14] Main[15] Main[16] Main[17] Main[18] Main[19] Main[20] Main[21] Main[13] 1 1) Main[22]),
    (.assertZero E30),
    (.assertZero E32),
    (.assertZero E34),
    (.assertZero E36),
    (.assertZero E39),
    (.send (.byte (ByteOpcode.ofNat 6) Main[12] 16 0) Main[31]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E43 0) Main[31]),
    (.send (.memory Main[0] Main[11] Main[6] 0 0 Main[7] Main[8] Main[9] Main[10]) Main[31]),
    (.receive (.memory Main[0] E37 Main[6] 0 0 Main[27] Main[28] Main[29] Main[30]) Main[31]),
  ]

end constraints
