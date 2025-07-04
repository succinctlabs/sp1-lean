import SP1Foundations

structure SubOperation where
  value : Word (Fin BB)

namespace SubOperation

def constraints
  (a : Word (Fin BB))
  (b : Word (Fin BB))
  (cols : SubOperation)
  (is_real : Fin BB)
  : SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := a[0] + 65536
  let E3 : Fin BB := E2 - 1
  let E4 : Fin BB := E3 - b[0]
  let E5 : Fin BB := E4 - cols.value[0]
  let E6 : Fin BB := E5 + 1
  let E7 : Fin BB := E6 * 2013235201
  let E8 : Fin BB := E7 - 1
  let E9 : Fin BB := E7 * E8
  let E10 : Fin BB := is_real * E9
  let E11 : Fin BB := a[1] + 65536
  let E12 : Fin BB := E11 - 1
  let E13 : Fin BB := E12 - b[1]
  let E14 : Fin BB := E13 - cols.value[1]
  let E15 : Fin BB := E14 + E7
  let E16 : Fin BB := E15 * 2013235201
  let E17 : Fin BB := E16 - 1
  let E18 : Fin BB := E16 * E17
  let E19 : Fin BB := is_real * E18
  [
    .assertZero E1,
    .assertZero E10,
    .assertZero E19,
    .send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real,
    .send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real
  ]

def spec
  (a b : Word U16)
  (cols : SubOperation)
  (is_real : U1) : Prop :=
    is_real = 1 → a.toBV32_U16 - b.toBV32_U16 = cols.value.toBV32

-- theorem correct
--   (a b : Word U16)
--   (cols : SubOperation)
--   (is_real : U1)
--   : (constraints a b cols is_real).allHold → spec a b cols is_real
--   := by
--     sorry

-- open BitVec

-- theorem correct'
--   (a b : Word U16)
--   (cols : SubOperation)
--   (is_real : U1)
--   (h_is_real : is_real = 1)
--   (pf : cols.value[0].val + cols.value[1].val * 65536 < 2 ^ BIT_WIDTH)
--   : (cols.value[0].val + cols.value[1].val * 65536)#'pf
--     = (a.toBV32_U16 - b.toBV32_U16)
--   := by
--       sorry

end SubOperation
