import SP1Operations.Compare.LtOperationSigned.Operation
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Compare.LtOperationUnsigned

namespace LtOperationSigned

section constraints

@[irreducible] def constraints
  (b : (Word (Fin KB)))
  (cc : (Word (Fin KB)))
  (cols : LtOperationSigned)
  (is_signed : (Fin KB))
  (is_real : (Fin KB))
  : SP1ConstraintList (Fin KB) :=
  let E0 : Fin KB := is_signed - 1
  let E1 : Fin KB := is_signed * E0
  let E2 : Fin KB := is_real - 1
  let E3 : Fin KB := is_real * E2
  let E4 : Fin KB := is_real - 1
  let E5 : Fin KB := E4 * is_signed
  let CS0 : SP1ConstraintList (Fin KB) := U16MSBOperation.constraints b[3] { msb := cols.b_msb.msb } is_signed
  let CS1 : SP1ConstraintList (Fin KB) := U16MSBOperation.constraints cc[3] { msb := cols.c_msb.msb } is_signed
  let E6 : Fin KB := is_signed - 1
  let E7 : Fin KB := E6 * cols.b_msb.msb
  let E8 : Fin KB := is_signed - 1
  let E9 : Fin KB := E8 * cols.c_msb.msb
  let E10 : Fin KB := is_signed * 32768
  let E11 : Fin KB := b[3] + E10
  let E12 : Fin KB := 65536 * cols.b_msb.msb
  let E13 : Fin KB := E11 - E12
  let E14 : Fin KB := is_signed * 32768
  let E15 : Fin KB := cc[3] + E14
  let E16 : Fin KB := 65536 * cols.c_msb.msb
  let E17 : Fin KB := E15 - E16
  let CS2 : SP1ConstraintList (Fin KB) := LtOperationUnsigned.constraints #v[b[0], b[1], b[2], E13] #v[cc[0], cc[1], cc[2], E17] { u16_compare_operation := { bit := cols.result.u16_compare_operation.bit }, u16_flags := #v[cols.result.u16_flags[0], cols.result.u16_flags[1], cols.result.u16_flags[2], cols.result.u16_flags[3]], not_eq_inv := cols.result.not_eq_inv, comparison_limbs := #v[cols.result.comparison_limbs[0], cols.result.comparison_limbs[1]] } is_real
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
  ]

end constraints

end LtOperationSigned
