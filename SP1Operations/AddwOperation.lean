import SP1Foundations
import SP1Operations.U16MSBOperation

structure AddwOperation where
  value : Vector (Fin BB) 2
  msb : U16MSBOperation

-- Generated Lean code for operation AddwOperation (from chip Addw)
namespace AddwOperation

def constraints
  (a : (Word (Fin BB)))
  (b : (Word (Fin BB)))
  (cols : AddwOperation)
  (is_real : (Fin BB))
  : SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := a[0] + b[0]
  let E3 : Fin BB := E2 - cols.value[0]
  let E4 : Fin BB := E3 + 0
  let E5 : Fin BB := E4 * 2013235201
  let E6 : Fin BB := E5 - 1
  let E7 : Fin BB := E5 * E6
  let E8 : Fin BB := is_real * E7
  let E9 : Fin BB := a[1] + b[1]
  let E10 : Fin BB := E9 - cols.value[1]
  let E11 : Fin BB := E10 + E5
  let E12 : Fin BB := E11 * 2013235201
  let E13 : Fin BB := E12 - 1
  let E14 : Fin BB := E12 * E13
  let E15 : Fin BB := is_real * E14
  let E16 : Fin BB := is_real - 1
  let E17 : Fin BB := is_real * E16
  let E18 : Fin BB := cols.msb.msb - 1
  let E19 : Fin BB := cols.msb.msb * E18
  let E20 : Fin BB := 2 * cols.value[1]
  let E21 : Fin BB := cols.msb.msb * 65536
  let E22 : Fin BB := E20 - E21
  [
    (.assertZero E1),
    (.assertZero E8),
    (.assertZero E15),
    (.send (.byte (ByteOpcode.ofNat 7) cols.value[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 7) cols.value[1] 16 0) is_real),
    (.assertZero E17),
    (.assertZero E19),
    (.send (.byte (ByteOpcode.ofNat 7) E22 16 0) is_real),
  ]

end AddwOperation
