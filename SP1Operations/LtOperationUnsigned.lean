import SP1Foundations
import SP1Operations.U16CompareOperation

structure LtOperationUnsigned where
  u16_compare_operation : U16CompareOperation
  u16_flags : Vector BabyBear WORD_SIZE
  not_eq_inv : BabyBear
  comparison_limbs : Vector BabyBear 2

namespace LtOperationUnsigned

def constraints
  (b : Word BabyBear)
  (cc : Word BabyBear)
  (cols : LtOperationUnsigned)
  (is_real : BabyBear)
  : SP1ConstraintList :=
  let E0 : BabyBear := is_real - 1
  let E1 : BabyBear := is_real * E0
  let E2 : BabyBear := cols.u16_flags[0] + cols.u16_flags[1]
  let E3 : BabyBear := cols.u16_flags[0] - 1
  let E4 : BabyBear := cols.u16_flags[0] * E3
  let E5 : BabyBear := cols.u16_flags[1] - 1
  let E6 : BabyBear := cols.u16_flags[1] * E5
  let E7 : BabyBear := E2 - 1
  let E8 : BabyBear := E2 * E7
  let E9 : BabyBear := 1 - E2
  let E10 : BabyBear := 0 + cols.u16_flags[1]
  let E11 : BabyBear := is_real - E10
  let E12 : BabyBear := b[1] - cc[1]
  let E13 : BabyBear := E11 * E12
  let E14 : BabyBear := b[1] * cols.u16_flags[1]
  let E15 : BabyBear := 0 + E14
  let E16 : BabyBear := cc[1] * cols.u16_flags[1]
  let E17 : BabyBear := 0 + E16
  let E18 : BabyBear := E10 + cols.u16_flags[0]
  let E19 : BabyBear := is_real - E18
  let E20 : BabyBear := b[0] - cc[0]
  let E21 : BabyBear := E19 * E20
  let E22 : BabyBear := b[0] * cols.u16_flags[0]
  let E23 : BabyBear := E15 + E22
  let E24 : BabyBear := cc[0] * cols.u16_flags[0]
  let E25 : BabyBear := E17 + E24
  let E26 : BabyBear := E23 - cols.comparison_limbs[0]
  let E27 : BabyBear := E25 - cols.comparison_limbs[1]
  let E28 : BabyBear := E9 - 1
  let E29 : BabyBear := cols.comparison_limbs[0] - cols.comparison_limbs[1]
  let E30 : BabyBear := cols.not_eq_inv * E29
  let E31 : BabyBear := E30 - is_real
  let E32 : BabyBear := E28 * E31
  let CS0 : SP1ConstraintList := U16CompareOperation.constraints cols.comparison_limbs[0] cols.comparison_limbs[1] { bit := cols.u16_compare_operation.bit } is_real
  [
    .assertZero E1,
    .assertZero E4,
    .assertZero E6,
    .assertZero E8,
    .assertZero E13,
    .assertZero E21,
    .assertZero E26,
    .assertZero E27,
    .assertZero E32
  ] ++ CS0

end LtOperationUnsigned
