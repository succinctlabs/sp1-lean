import SP1Operations.U16MSBOperation
import SP1Operations.Compare.LtOperationUnsigned

structure LtOperationSigned where
  result : LtOperationUnsigned
  b_msb : U16MSBOperation
  c_msb : U16MSBOperation

namespace LtOperationSigned

def constraints
  (b : (Word (Fin BB)))
  (d : (Word (Fin BB)))
  (cols : LtOperationSigned)
  (is_signed : (Fin BB))
  (is_real : (Fin BB))
  : SP1ConstraintList :=
  let E0 : Fin BB := is_signed - 1
  let E1 : Fin BB := is_signed * E0
  let E2 : Fin BB := is_real - 1
  let E3 : Fin BB := is_real * E2
  let E4 : Fin BB := is_real - 1
  let E5 : Fin BB := E4 * is_signed
  let CS0 : SP1ConstraintList := U16MSBOperation.constraints b[3] { msb := cols.b_msb.msb } is_signed
  let CS1 : SP1ConstraintList := U16MSBOperation.constraints d[3] { msb := cols.c_msb.msb } is_signed
  let E6 : Fin BB := is_signed - 1
  let E7 : Fin BB := E6 * cols.b_msb.msb
  let E8 : Fin BB := is_signed - 1
  let E9 : Fin BB := E8 * cols.c_msb.msb
  let E10 : Fin BB := is_signed * 32768
  let E11 : Fin BB := b[3] + E10
  let E12 : Fin BB := 65536 * cols.b_msb.msb
  let E13 : Fin BB := E11 - E12
  let E14 : Fin BB := is_signed * 32768
  let E15 : Fin BB := d[3] + E14
  let E16 : Fin BB := 65536 * cols.c_msb.msb
  let E17 : Fin BB := E15 - E16
  let CS2 : SP1ConstraintList := LtOperationUnsigned.constraints #v[b[0], b[1], b[2], E13] #v[d[0], d[1], d[2], E17] { u16_compare_operation := { bit := cols.result.u16_compare_operation.bit }, u16_flags := #v[cols.result.u16_flags[0], cols.result.u16_flags[1], cols.result.u16_flags[2], cols.result.u16_flags[3]], not_eq_inv := cols.result.not_eq_inv, comparison_limbs := #v[cols.result.comparison_limbs[0], cols.result.comparison_limbs[1]] } is_real
  [
    (.assertZero E1),
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
  ] ++ CS0 ++ CS1 ++ CS2

end LtOperationSigned
