import SP1Foundations

structure U16MSBOperation where
  msb : BabyBear

namespace U16MSBOperation

def constraints
  (a : BabyBear)
  (cols : U16MSBOperation)
  (is_real : BabyBear)
  : SP1ConstraintList :=
  let E0 : BabyBear := is_real - 1
  let E1 : BabyBear := is_real * E0
  let E2 : BabyBear := cols.msb - 1
  let E3 : BabyBear := cols.msb * E2
  let E4 : BabyBear := 2 * a
  let E5 : BabyBear := cols.msb * 65536
  let E6 : BabyBear := E4 - E5
  [
    .assertZero E1,
    .assertZero E3,
    .send (.byte (ByteOpcode.ofNat 6) E6 16 0) is_real
  ]

end U16MSBOperation
