import SP1Foundations
import SP1Operations.Operation.AddOperation.Operation

namespace AddOperation

section constraints

@[irreducible] def constraints
  (a : (Word (Fin KB)))
  (b : (Word (Fin KB)))
  (cols : AddOperation)
  (is_real : (Fin KB))
  : SP1ConstraintList :=
  let E0 : Fin KB := is_real - 1
  let E1 : Fin KB := is_real * E0
  let E2 : Fin KB := a[0] + b[0]
  let E3 : Fin KB := E2 - cols.value[0]
  let E4 : Fin KB := E3 + 0
  let E5 : Fin KB := E4 * 2130673921
  let E6 : Fin KB := E5 - 1
  let E7 : Fin KB := E5 * E6
  let E8 : Fin KB := is_real * E7
  let E9 : Fin KB := a[1] + b[1]
  let E10 : Fin KB := E9 - cols.value[1]
  let E11 : Fin KB := E10 + E5
  let E12 : Fin KB := E11 * 2130673921
  let E13 : Fin KB := E12 - 1
  let E14 : Fin KB := E12 * E13
  let E15 : Fin KB := is_real * E14
  let E16 : Fin KB := a[2] + b[2]
  let E17 : Fin KB := E16 - cols.value[2]
  let E18 : Fin KB := E17 + E12
  let E19 : Fin KB := E18 * 2130673921
  let E20 : Fin KB := E19 - 1
  let E21 : Fin KB := E19 * E20
  let E22 : Fin KB := is_real * E21
  let E23 : Fin KB := a[3] + b[3]
  let E24 : Fin KB := E23 - cols.value[3]
  let E25 : Fin KB := E24 + E19
  let E26 : Fin KB := E25 * 2130673921
  let E27 : Fin KB := E26 - 1
  let E28 : Fin KB := E26 * E27
  let E29 : Fin KB := is_real * E28
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
