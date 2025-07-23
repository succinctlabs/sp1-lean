import SP1Foundations
import SP1Operations.Operation.AddOperation.Operation

namespace AddOperation

section constraints

def constraints
  (a : (Word (Fin BB)))
  (b : (Word (Fin BB)))
  (cols : AddOperation)
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
  let E16 : Fin BB := a[2] + b[2]
  let E17 : Fin BB := E16 - cols.value[2]
  let E18 : Fin BB := E17 + E12
  let E19 : Fin BB := E18 * 2013235201
  let E20 : Fin BB := E19 - 1
  let E21 : Fin BB := E19 * E20
  let E22 : Fin BB := is_real * E21
  let E23 : Fin BB := a[3] + b[3]
  let E24 : Fin BB := E23 - cols.value[3]
  let E25 : Fin BB := E24 + E19
  let E26 : Fin BB := E25 * 2013235201
  let E27 : Fin BB := E26 - 1
  let E28 : Fin BB := E26 * E27
  let E29 : Fin BB := is_real * E28
  [
    (.assertZero E1),
    (.assertZero E8),
    (.assertZero E15),
    (.assertZero E22),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[2] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[3] 16 0) is_real),
  ]

end constraints
