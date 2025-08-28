import SP1Foundations
import SP1Operations.Operation.SubOperation.Operation

namespace SubOperation

section constraints

@[irreducible] def constraints
  (a : (Word (Fin BB)))
  (b : (Word (Fin BB)))
  (cols : SubOperation)
  (is_real : (Fin BB))
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
  let E20 : Fin BB := a[2] + 65536
  let E21 : Fin BB := E20 - 1
  let E22 : Fin BB := E21 - b[2]
  let E23 : Fin BB := E22 - cols.value[2]
  let E24 : Fin BB := E23 + E16
  let E25 : Fin BB := E24 * 2013235201
  let E26 : Fin BB := E25 - 1
  let E27 : Fin BB := E25 * E26
  let E28 : Fin BB := is_real * E27
  let E29 : Fin BB := a[3] + 65536
  let E30 : Fin BB := E29 - 1
  let E31 : Fin BB := E30 - b[3]
  let E32 : Fin BB := E31 - cols.value[3]
  let E33 : Fin BB := E32 + E25
  let E34 : Fin BB := E33 * 2013235201
  let E35 : Fin BB := E34 - 1
  let E36 : Fin BB := E34 * E35
  let E37 : Fin BB := is_real * E36
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
