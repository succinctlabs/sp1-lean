import SP1Operations.Compare.LtOperationUnsigned.Operation
import SP1Operations.Compare.U16CompareOperation

namespace LtOperationUnsigned

section constraints

@[irreducible] def constraints
  (b : (Word (Fin KB)))
  (cc : (Word (Fin KB)))
  (cols : LtOperationUnsigned)
  (is_real : (Fin KB))
  : SP1ConstraintList (Fin KB) :=
  let E0 : Fin KB := is_real - 1
  let E1 : Fin KB := is_real * E0
  let E2 : Fin KB := cols.u16_flags[0] + cols.u16_flags[1]
  let E3 : Fin KB := E2 + cols.u16_flags[2]
  let E4 : Fin KB := E3 + cols.u16_flags[3]
  let E5 : Fin KB := cols.u16_flags[0] - 1
  let E6 : Fin KB := cols.u16_flags[0] * E5
  let E7 : Fin KB := cols.u16_flags[1] - 1
  let E8 : Fin KB := cols.u16_flags[1] * E7
  let E9 : Fin KB := cols.u16_flags[2] - 1
  let E10 : Fin KB := cols.u16_flags[2] * E9
  let E11 : Fin KB := cols.u16_flags[3] - 1
  let E12 : Fin KB := cols.u16_flags[3] * E11
  let E13 : Fin KB := E4 - 1
  let E14 : Fin KB := E4 * E13
  let E15 : Fin KB := 1 - E4
  let E16 : Fin KB := 0 + cols.u16_flags[3]
  let E17 : Fin KB := is_real - E16
  let E18 : Fin KB := b[3] - cc[3]
  let E19 : Fin KB := E17 * E18
  let E20 : Fin KB := b[3] * cols.u16_flags[3]
  let E21 : Fin KB := 0 + E20
  let E22 : Fin KB := cc[3] * cols.u16_flags[3]
  let E23 : Fin KB := 0 + E22
  let E24 : Fin KB := E16 + cols.u16_flags[2]
  let E25 : Fin KB := is_real - E24
  let E26 : Fin KB := b[2] - cc[2]
  let E27 : Fin KB := E25 * E26
  let E28 : Fin KB := b[2] * cols.u16_flags[2]
  let E29 : Fin KB := E21 + E28
  let E30 : Fin KB := cc[2] * cols.u16_flags[2]
  let E31 : Fin KB := E23 + E30
  let E32 : Fin KB := E24 + cols.u16_flags[1]
  let E33 : Fin KB := is_real - E32
  let E34 : Fin KB := b[1] - cc[1]
  let E35 : Fin KB := E33 * E34
  let E36 : Fin KB := b[1] * cols.u16_flags[1]
  let E37 : Fin KB := E29 + E36
  let E38 : Fin KB := cc[1] * cols.u16_flags[1]
  let E39 : Fin KB := E31 + E38
  let E40 : Fin KB := E32 + cols.u16_flags[0]
  let E41 : Fin KB := is_real - E40
  let E42 : Fin KB := b[0] - cc[0]
  let E43 : Fin KB := E41 * E42
  let E44 : Fin KB := b[0] * cols.u16_flags[0]
  let E45 : Fin KB := E37 + E44
  let E46 : Fin KB := cc[0] * cols.u16_flags[0]
  let E47 : Fin KB := E39 + E46
  let E48 : Fin KB := E45 - cols.comparison_limbs[0]
  let E49 : Fin KB := E47 - cols.comparison_limbs[1]
  let E50 : Fin KB := E15 - 1
  let E51 : Fin KB := cols.comparison_limbs[0] - cols.comparison_limbs[1]
  let E52 : Fin KB := cols.not_eq_inv * E51
  let E53 : Fin KB := E52 - is_real
  let E54 : Fin KB := E50 * E53
  let CS0 : SP1ConstraintList (Fin KB) := U16CompareOperation.constraints cols.comparison_limbs[0] cols.comparison_limbs[1] { bit := cols.u16_compare_operation.bit } is_real
  CS0 ++ [
    (.assertZero E1),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.assertZero E12),
    (.assertZero E14),
    (.assertZero E19),
    (.assertZero E27),
    (.assertZero E35),
    (.assertZero E43),
    (.assertZero E48),
    (.assertZero E49),
    (.assertZero E54),
  ]

end constraints

end LtOperationUnsigned
