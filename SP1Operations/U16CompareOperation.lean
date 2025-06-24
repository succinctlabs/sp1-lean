import SP1Foundations

structure U16CompareOperation where
  bit : BabyBear

namespace U16CompareOperation

def constraints
  (a : BabyBear)
  (b : BabyBear)
  (cols : U16CompareOperation)
  (is_real : BabyBear)
  : SP1ConstraintList :=
  let E0 : BabyBear := is_real - 1
  let E1 : BabyBear := is_real * E0
  let E2 : BabyBear := cols.bit - 1
  let E3 : BabyBear := cols.bit * E2
  let E4 : BabyBear := a - b
  let E5 : BabyBear := cols.bit * 65536
  let E6 : BabyBear := E4 + E5
  [
    .assertZero E1,
    .assertZero E3,
    .send (.byte (ByteOpcode.ofNat 6) E6 16 0) is_real
  ]

end U16CompareOperation
