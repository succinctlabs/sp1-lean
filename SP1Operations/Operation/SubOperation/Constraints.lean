import SP1Foundations
import SP1Operations.Operation.SubOperation.Operation

namespace SubOperation

section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (a : (Word F))
  (b : (Word F))
  (cols : SubOperation F)
  (is_real : F)
  : SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := a[0] + 65536
  let E3 : F := E2 - 1
  let E4 : F := E3 - b[0]
  let E5 : F := E4 - cols.value[0]
  let E6 : F := E5 + 1
  let E7 : F := E6 * ((65536 : F)⁻¹)
  let E8 : F := E7 - 1
  let E9 : F := E7 * E8
  let E10 : F := is_real * E9
  let E11 : F := a[1] + 65536
  let E12 : F := E11 - 1
  let E13 : F := E12 - b[1]
  let E14 : F := E13 - cols.value[1]
  let E15 : F := E14 + E7
  let E16 : F := E15 * ((65536 : F)⁻¹)
  let E17 : F := E16 - 1
  let E18 : F := E16 * E17
  let E19 : F := is_real * E18
  let E20 : F := a[2] + 65536
  let E21 : F := E20 - 1
  let E22 : F := E21 - b[2]
  let E23 : F := E22 - cols.value[2]
  let E24 : F := E23 + E16
  let E25 : F := E24 * ((65536 : F)⁻¹)
  let E26 : F := E25 - 1
  let E27 : F := E25 * E26
  let E28 : F := is_real * E27
  let E29 : F := a[3] + 65536
  let E30 : F := E29 - 1
  let E31 : F := E30 - b[3]
  let E32 : F := E31 - cols.value[3]
  let E33 : F := E32 + E25
  let E34 : F := E33 * ((65536 : F)⁻¹)
  let E35 : F := E34 - 1
  let E36 : F := E34 * E35
  let E37 : F := is_real * E36
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
