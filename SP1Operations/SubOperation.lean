import SP1Foundations

structure SubOperation (T : Type) where
  value : Word T

namespace SubOperation

def constraints
  (a : Word BabyBear)
  (b : Word BabyBear)
  (cols : SubOperation BabyBear)
  (is_real : BabyBear)
  : SP1ConstraintList :=
  let E0 : BabyBear := is_real - 1
  let E1 : BabyBear := is_real * E0
  let E2 : BabyBear := a[0] + 65536
  let E3 : BabyBear := E2 - 1
  let E4 : BabyBear := E3 - b[0]
  let E5 : BabyBear := E4 - cols.value[0]
  let E6 : BabyBear := E5 + 1
  let E7 : BabyBear := E6 * 2013235201
  let E8 : BabyBear := E7 - 1
  let E9 : BabyBear := E7 * E8
  let E10 : BabyBear := is_real * E9
  let E11 : BabyBear := a[1] + 65536
  let E12 : BabyBear := E11 - 1
  let E13 : BabyBear := E12 - b[1]
  let E14 : BabyBear := E13 - cols.value[1]
  let E15 : BabyBear := E14 + E7
  let E16 : BabyBear := E15 * 2013235201
  let E17 : BabyBear := E16 - 1
  let E18 : BabyBear := E16 * E17
  let E19 : BabyBear := is_real * E18
  [
    .assertZero E1,
    .assertZero E10,
    .assertZero E19,
    .send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real,
    .send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real
  ]

def spec
  (a b : Word U16)
  (cols : SubOperation BabyBear) 
  (is_real : U1) : Prop :=
    is_real = 1 → a.toBV32_U16 - b.toBV32_U16 = cols.value.toBV32

theorem correct
  (a b : Word U16)
  (cols : SubOperation BabyBear)
  (is_real : U1)
  : (constraints a b cols is_real).allHold → spec a b cols is_real
  := by
    sorry

open BitVec

theorem correct'
  (a b : Word U16)
  (cols : SubOperation BabyBear)
  (is_real : U1)
  (h_is_real : is_real = 1)
  (pf : cols.value[0].val + cols.value[1].val * 65536 < 2 ^ BIT_WIDTH)
  : (cols.value[0].val + cols.value[1].val * 65536)#'pf
    = (a.toBV32_U16 - b.toBV32_U16)
  := by
      sorry

end SubOperation
