import SP1Operations.Compare.LtOperationUnsigned.Operation
import SP1Operations.Compare.U16CompareOperation

namespace LtOperationUnsigned

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (b : (Word F))
  (cc : (Word F))
  (cols : LtOperationUnsigned F)
  (is_real : F)
  : SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := cols.u16_flags[0] + cols.u16_flags[1]
  let E3 : F := E2 + cols.u16_flags[2]
  let E4 : F := E3 + cols.u16_flags[3]
  let E5 : F := cols.u16_flags[0] - 1
  let E6 : F := cols.u16_flags[0] * E5
  let E7 : F := cols.u16_flags[1] - 1
  let E8 : F := cols.u16_flags[1] * E7
  let E9 : F := cols.u16_flags[2] - 1
  let E10 : F := cols.u16_flags[2] * E9
  let E11 : F := cols.u16_flags[3] - 1
  let E12 : F := cols.u16_flags[3] * E11
  let E13 : F := E4 - 1
  let E14 : F := E4 * E13
  let E15 : F := 1 - E4
  let E16 : F := 0 + cols.u16_flags[3]
  let E17 : F := is_real - E16
  let E18 : F := b[3] - cc[3]
  let E19 : F := E17 * E18
  let E20 : F := b[3] * cols.u16_flags[3]
  let E21 : F := 0 + E20
  let E22 : F := cc[3] * cols.u16_flags[3]
  let E23 : F := 0 + E22
  let E24 : F := E16 + cols.u16_flags[2]
  let E25 : F := is_real - E24
  let E26 : F := b[2] - cc[2]
  let E27 : F := E25 * E26
  let E28 : F := b[2] * cols.u16_flags[2]
  let E29 : F := E21 + E28
  let E30 : F := cc[2] * cols.u16_flags[2]
  let E31 : F := E23 + E30
  let E32 : F := E24 + cols.u16_flags[1]
  let E33 : F := is_real - E32
  let E34 : F := b[1] - cc[1]
  let E35 : F := E33 * E34
  let E36 : F := b[1] * cols.u16_flags[1]
  let E37 : F := E29 + E36
  let E38 : F := cc[1] * cols.u16_flags[1]
  let E39 : F := E31 + E38
  let E40 : F := E32 + cols.u16_flags[0]
  let E41 : F := is_real - E40
  let E42 : F := b[0] - cc[0]
  let E43 : F := E41 * E42
  let E44 : F := b[0] * cols.u16_flags[0]
  let E45 : F := E37 + E44
  let E46 : F := cc[0] * cols.u16_flags[0]
  let E47 : F := E39 + E46
  let E48 : F := E45 - cols.comparison_limbs[0]
  let E49 : F := E47 - cols.comparison_limbs[1]
  let E50 : F := E15 - 1
  let E51 : F := cols.comparison_limbs[0] - cols.comparison_limbs[1]
  let E52 : F := cols.not_eq_inv * E51
  let E53 : F := E52 - is_real
  let E54 : F := E50 * E53
  let CS0 : SP1ConstraintList F := U16CompareOperation.constraints cols.comparison_limbs[0] cols.comparison_limbs[1] { bit := cols.u16_compare_operation.bit } is_real
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
