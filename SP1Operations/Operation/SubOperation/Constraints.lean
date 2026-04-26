import SP1Foundations
import SP1Operations.Operation.SubOperation.Operation

namespace SubOperation

section constraints

@[irreducible] def constraints
  (a : (Word (Fin KB)))
  (b : (Word (Fin KB)))
  (cols : SubOperation)
  (is_real : (Fin KB))
  : SP1ConstraintList (Fin KB) :=
  let E0 : Fin KB := is_real - 1
  let E1 : Fin KB := is_real * E0
  let E2 : Fin KB := a[0] + 65536
  let E3 : Fin KB := E2 - 1
  let E4 : Fin KB := E3 - b[0]
  let E5 : Fin KB := E4 - cols.value[0]
  let E6 : Fin KB := E5 + 1
  let E7 : Fin KB := E6 * 2130673921
  let E8 : Fin KB := E7 - 1
  let E9 : Fin KB := E7 * E8
  let E10 : Fin KB := is_real * E9
  let E11 : Fin KB := a[1] + 65536
  let E12 : Fin KB := E11 - 1
  let E13 : Fin KB := E12 - b[1]
  let E14 : Fin KB := E13 - cols.value[1]
  let E15 : Fin KB := E14 + E7
  let E16 : Fin KB := E15 * 2130673921
  let E17 : Fin KB := E16 - 1
  let E18 : Fin KB := E16 * E17
  let E19 : Fin KB := is_real * E18
  let E20 : Fin KB := a[2] + 65536
  let E21 : Fin KB := E20 - 1
  let E22 : Fin KB := E21 - b[2]
  let E23 : Fin KB := E22 - cols.value[2]
  let E24 : Fin KB := E23 + E16
  let E25 : Fin KB := E24 * 2130673921
  let E26 : Fin KB := E25 - 1
  let E27 : Fin KB := E25 * E26
  let E28 : Fin KB := is_real * E27
  let E29 : Fin KB := a[3] + 65536
  let E30 : Fin KB := E29 - 1
  let E31 : Fin KB := E30 - b[3]
  let E32 : Fin KB := E31 - cols.value[3]
  let E33 : Fin KB := E32 + E25
  let E34 : Fin KB := E33 * 2130673921
  let E35 : Fin KB := E34 - 1
  let E36 : Fin KB := E34 * E35
  let E37 : Fin KB := is_real * E36
  [
    (.assertZero E1),
    (.assertZero E10),
    (.assertZero E19),
    (.assertZero E28),
    (.assertZero E37),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[2] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[3] 16 0) is_real),
  ]

end constraints

end SubOperation
