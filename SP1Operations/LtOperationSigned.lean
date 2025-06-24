import SP1Foundations
import SP1Operations.U16CompareOperation
import SP1Operations.U16MSBOperation
import SP1Operations.LtOperationUnsigned

structure LtOperationSigned where
  result : LtOperationUnsigned
  b_msb : U16MSBOperation
  c_msb : U16MSBOperation

namespace LtOperationSigned

def constraints
  (b : Word BabyBear)
  (cc : Word BabyBear)
  (cols : LtOperationSigned)
  (is_signed : BabyBear)
  (is_real : BabyBear)
  : SP1ConstraintList :=
  let E0 : BabyBear := is_signed - 1
  let E1 : BabyBear := is_signed * E0
  let E2 : BabyBear := is_real - 1
  let E3 : BabyBear := is_real * E2
  let E4 : BabyBear := is_real - 1
  let E5 : BabyBear := E4 * is_signed
  let E6 : BabyBear := is_signed - 1
  let E7 : BabyBear := is_signed * E6
  let E8 : BabyBear := cols.b_msb.msb - 1
  let E9 : BabyBear := cols.b_msb.msb * E8
  let E10 : BabyBear := 2 * b[1]
  let E11 : BabyBear := cols.b_msb.msb * 65536
  let E12 : BabyBear := E10 - E11
  let E13 : BabyBear := is_signed - 1
  let E14 : BabyBear := is_signed * E13
  let E15 : BabyBear := cols.c_msb.msb - 1
  let E16 : BabyBear := cols.c_msb.msb * E15
  let E17 : BabyBear := 2 * cc[1]
  let E18 : BabyBear := cols.c_msb.msb * 65536
  let E19 : BabyBear := E17 - E18
  let E20 : BabyBear := is_signed - 1
  let E21 : BabyBear := E20 * cols.b_msb.msb
  let E22 : BabyBear := is_signed - 1
  let E23 : BabyBear := E22 * cols.c_msb.msb
  let E24 : BabyBear := is_signed * 32768
  let E25 : BabyBear := b[1] + E24
  let E26 : BabyBear := 65536 * cols.b_msb.msb
  let E27 : BabyBear := E25 - E26
  let E28 : BabyBear := is_signed * 32768
  let E29 : BabyBear := cc[1] + E28
  let E30 : BabyBear := 65536 * cols.c_msb.msb
  let E31 : BabyBear := E29 - E30
  let E32 : BabyBear := is_real - 1
  let E33 : BabyBear := is_real * E32
  let E34 : BabyBear := cols.result.u16_flags[0] + cols.result.u16_flags[1]
  let E35 : BabyBear := cols.result.u16_flags[0] - 1
  let E36 : BabyBear := cols.result.u16_flags[0] * E35
  let E37 : BabyBear := cols.result.u16_flags[1] - 1
  let E38 : BabyBear := cols.result.u16_flags[1] * E37
  let E39 : BabyBear := E34 - 1
  let E40 : BabyBear := E34 * E39
  let E41 : BabyBear := 1 - E34
  let E42 : BabyBear := 0 + cols.result.u16_flags[1]
  let E43 : BabyBear := is_real - E42
  let E44 : BabyBear := E27 - E31
  let E45 : BabyBear := E43 * E44
  let E46 : BabyBear := E27 * cols.result.u16_flags[1]
  let E47 : BabyBear := 0 + E46
  let E48 : BabyBear := E31 * cols.result.u16_flags[1]
  let E49 : BabyBear := 0 + E48
  let E50 : BabyBear := E42 + cols.result.u16_flags[0]
  let E51 : BabyBear := is_real - E50
  let E52 : BabyBear := b[0] - cc[0]
  let E53 : BabyBear := E51 * E52
  let E54 : BabyBear := b[0] * cols.result.u16_flags[0]
  let E55 : BabyBear := E47 + E54
  let E56 : BabyBear := cc[0] * cols.result.u16_flags[0]
  let E57 : BabyBear := E49 + E56
  let E58 : BabyBear := E55 - cols.result.comparison_limbs[0]
  let E59 : BabyBear := E57 - cols.result.comparison_limbs[1]
  let E60 : BabyBear := E41 - 1
  let E61 : BabyBear := cols.result.comparison_limbs[0] - cols.result.comparison_limbs[1]
  let E62 : BabyBear := cols.result.not_eq_inv * E61
  let E63 : BabyBear := E62 - is_real
  let E64 : BabyBear := E60 * E63
  let CS0 : SP1ConstraintList := U16CompareOperation.constraints cols.result.comparison_limbs[0] cols.result.comparison_limbs[1] { bit := cols.result.u16_compare_operation.bit } is_real
  [
    .assertZero E1,
    .assertZero E3,
    .assertZero E5,
    .assertZero E7,
    .assertZero E9,
    .send (.byte (ByteOpcode.ofNat 6) E12 16 0) is_signed,
    .assertZero E14,
    .assertZero E16,
    .send (.byte (ByteOpcode.ofNat 6) E19 16 0) is_signed,
    .assertZero E21,
    .assertZero E23,
    .assertZero E33,
    .assertZero E36,
    .assertZero E38,
    .assertZero E40,
    .assertZero E45,
    .assertZero E53,
    .assertZero E58,
    .assertZero E59,
    .assertZero E64
  ] ++ CS0

end LtOperationSigned
