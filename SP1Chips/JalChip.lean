import SP1Operations

namespace Jal

section constraints

def constraints (Main : Vector BabyBear 15) : List SP1Constraint :=
  let E0 : BabyBear := Main[14] - 1
  let E1 : BabyBear := Main[14] * E0
  let E2 : BabyBear := 1 * Main[10]
  let E3 : BabyBear := 0 + E2
  let E4 : BabyBear := 65536 * Main[11]
  let E5 : BabyBear := E3 + E4
  let E6 : BabyBear := Main[1] * 65536
  let E7 : BabyBear := Main[2] + E6
  let E8 : BabyBear := Main[14] - 1
  let E9 : BabyBear := Main[14] * E8
  let E10 : BabyBear := E7 + 8
  let E11 : BabyBear := Main[2] - 1
  let E12 : BabyBear := E11 * 1761607681
  let E13 : BabyBear := Main[1] * 65536
  let E14 : BabyBear := Main[2] + E13
  let E15 : BabyBear := Main[14] - 1
  let E16 : BabyBear := Main[14] * E15
  let E17 : BabyBear := Main[12] - 0
  let E18 : BabyBear := Main[9] * E17
  let E19 : BabyBear := Main[13] - 0
  let E20 : BabyBear := Main[9] * E19
  let E21 : BabyBear := E14 + 3
  let E22 : BabyBear := Main[14] - 1
  let E23 : BabyBear := Main[14] * E22
  let E24 : BabyBear := E21 - Main[7]
  let E25 : BabyBear := E24 - 1
  let E26 : BabyBear := E25 - Main[8]
  let E27 : BabyBear := E26 * 2013235201
  [
    .assertZero E1,
    .assertZero E9,
    .receive (.state Main[0] E7 Main[3]) Main[14],
    .send (.state Main[0] E10 E5) Main[14],
    .send (.byte (ByteOpcode.ofNat 6) E12 13 0) Main[14],
    .send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0) Main[14],
    .assertZero E16,
    .assertZero E18,
    .assertZero E20,
    .assertZero E23,
    .send (.byte (ByteOpcode.ofNat 6) Main[8] 16 0) Main[14],
    .send (.byte (ByteOpcode.ofNat 3) 0 E27 0) Main[14],
    .send (.memory Main[0] Main[7] Main[4] Main[5] Main[6]) Main[14],
    .receive (.memory Main[0] E21 Main[4] Main[12] Main[13]) Main[14]
  ]

end constraints

end Jal
