import SP1Operations.Compare.U16CompareOperation

structure LtOperationUnsigned where
  u16_compare_operation : U16CompareOperation
  u16_flags : Word (Fin BB)
  not_eq_inv : Fin BB
  comparison_limbs : Vector (Fin BB) 2

namespace LtOperationUnsigned

def constraints
  (b : (Word (Fin BB)))
  (d : (Word (Fin BB)))
  (cols : LtOperationUnsigned)
  (is_real : (Fin BB))
  : SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := cols.u16_flags[0] + cols.u16_flags[1]
  let E3 : Fin BB := E2 + cols.u16_flags[2]
  let E4 : Fin BB := E3 + cols.u16_flags[3]
  let E5 : Fin BB := cols.u16_flags[0] - 1
  let E6 : Fin BB := cols.u16_flags[0] * E5
  let E7 : Fin BB := cols.u16_flags[1] - 1
  let E8 : Fin BB := cols.u16_flags[1] * E7
  let E9 : Fin BB := cols.u16_flags[2] - 1
  let E10 : Fin BB := cols.u16_flags[2] * E9
  let E11 : Fin BB := cols.u16_flags[3] - 1
  let E12 : Fin BB := cols.u16_flags[3] * E11
  let E13 : Fin BB := E4 - 1
  let E14 : Fin BB := E4 * E13
  let E15 : Fin BB := 1 - E4
  let E16 : Fin BB := 0 + cols.u16_flags[3]
  let E17 : Fin BB := is_real - E16
  let E18 : Fin BB := b[3] - d[3]
  let E19 : Fin BB := E17 * E18
  let E20 : Fin BB := b[3] * cols.u16_flags[3]
  let E21 : Fin BB := 0 + E20
  let E22 : Fin BB := d[3] * cols.u16_flags[3]
  let E23 : Fin BB := 0 + E22
  let E24 : Fin BB := E16 + cols.u16_flags[2]
  let E25 : Fin BB := is_real - E24
  let E26 : Fin BB := b[2] - d[2]
  let E27 : Fin BB := E25 * E26
  let E28 : Fin BB := b[2] * cols.u16_flags[2]
  let E29 : Fin BB := E21 + E28
  let E30 : Fin BB := d[2] * cols.u16_flags[2]
  let E31 : Fin BB := E23 + E30
  let E32 : Fin BB := E24 + cols.u16_flags[1]
  let E33 : Fin BB := is_real - E32
  let E34 : Fin BB := b[1] - d[1]
  let E35 : Fin BB := E33 * E34
  let E36 : Fin BB := b[1] * cols.u16_flags[1]
  let E37 : Fin BB := E29 + E36
  let E38 : Fin BB := d[1] * cols.u16_flags[1]
  let E39 : Fin BB := E31 + E38
  let E40 : Fin BB := E32 + cols.u16_flags[0]
  let E41 : Fin BB := is_real - E40
  let E42 : Fin BB := b[0] - d[0]
  let E43 : Fin BB := E41 * E42
  let E44 : Fin BB := b[0] * cols.u16_flags[0]
  let E45 : Fin BB := E37 + E44
  let E46 : Fin BB := d[0] * cols.u16_flags[0]
  let E47 : Fin BB := E39 + E46
  let E48 : Fin BB := E45 - cols.comparison_limbs[0]
  let E49 : Fin BB := E47 - cols.comparison_limbs[1]
  let E50 : Fin BB := E15 - 1
  let E51 : Fin BB := cols.comparison_limbs[0] - cols.comparison_limbs[1]
  let E52 : Fin BB := cols.not_eq_inv * E51
  let E53 : Fin BB := E52 - is_real
  let E54 : Fin BB := E50 * E53
  let CS0 : SP1ConstraintList := U16CompareOperation.constraints cols.comparison_limbs[0] cols.comparison_limbs[1] { bit := cols.u16_compare_operation.bit } is_real
  [
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
  ] ++ CS0

end LtOperationUnsigned
