import SP1Foundations
import SP1Operations.U16CompareOperation

structure LtOperationUnsigned where
  u16_compare_operation : U16CompareOperation
  u16_flags : Vector (Fin BB) WORD_SIZE
  not_eq_inv : Fin BB
  comparison_limbs : Vector (Fin BB) 2

namespace LtOperationUnsigned

def constraints
  (b : Word (Fin BB))
  (cc : Word (Fin BB))
  (cols : LtOperationUnsigned)
  (is_real : Fin BB)
  : SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := cols.u16_flags[0] + cols.u16_flags[1]
  let E3 : Fin BB := cols.u16_flags[0] - 1
  let E4 : Fin BB := cols.u16_flags[0] * E3
  let E5 : Fin BB := cols.u16_flags[1] - 1
  let E6 : Fin BB := cols.u16_flags[1] * E5
  let E7 : Fin BB := E2 - 1
  let E8 : Fin BB := E2 * E7
  let E9 : Fin BB := 1 - E2
  let E10 : Fin BB := 0 + cols.u16_flags[1]
  let E11 : Fin BB := is_real - E10
  let E12 : Fin BB := b[1] - cc[1]
  let E13 : Fin BB := E11 * E12
  let E14 : Fin BB := b[1] * cols.u16_flags[1]
  let E15 : Fin BB := 0 + E14
  let E16 : Fin BB := cc[1] * cols.u16_flags[1]
  let E17 : Fin BB := 0 + E16
  let E18 : Fin BB := E10 + cols.u16_flags[0]
  let E19 : Fin BB := is_real - E18
  let E20 : Fin BB := b[0] - cc[0]
  let E21 : Fin BB := E19 * E20
  let E22 : Fin BB := b[0] * cols.u16_flags[0]
  let E23 : Fin BB := E15 + E22
  let E24 : Fin BB := cc[0] * cols.u16_flags[0]
  let E25 : Fin BB := E17 + E24
  let E26 : Fin BB := E23 - cols.comparison_limbs[0]
  let E27 : Fin BB := E25 - cols.comparison_limbs[1]
  let E28 : Fin BB := E9 - 1
  let E29 : Fin BB := cols.comparison_limbs[0] - cols.comparison_limbs[1]
  let E30 : Fin BB := cols.not_eq_inv * E29
  let E31 : Fin BB := E30 - is_real
  let E32 : Fin BB := E28 * E31
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
