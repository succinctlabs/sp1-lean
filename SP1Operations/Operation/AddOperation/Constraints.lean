import SP1Foundations
import SP1Operations.Operation.AddOperation.Operation

namespace AddOperation

section constraints

@[irreducible] def constraints {F : Type} [Field F]
  (a : (Word F))
  (b : (Word F))
  (cols : AddOperation F)
  (is_real : F)
  : SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := a[0] + b[0]
  let E3 : F := E2 - cols.value[0]
  let E4 : F := E3 + 0
  let E5 : F := E4 * ((65536 : F)⁻¹)
  let E6 : F := E5 - 1
  let E7 : F := E5 * E6
  let E8 : F := is_real * E7
  let E9 : F := a[1] + b[1]
  let E10 : F := E9 - cols.value[1]
  let E11 : F := E10 + E5
  let E12 : F := E11 * ((65536 : F)⁻¹)
  let E13 : F := E12 - 1
  let E14 : F := E12 * E13
  let E15 : F := is_real * E14
  let E16 : F := a[2] + b[2]
  let E17 : F := E16 - cols.value[2]
  let E18 : F := E17 + E12
  let E19 : F := E18 * ((65536 : F)⁻¹)
  let E20 : F := E19 - 1
  let E21 : F := E19 * E20
  let E22 : F := is_real * E21
  let E23 : F := a[3] + b[3]
  let E24 : F := E23 - cols.value[3]
  let E25 : F := E24 + E19
  let E26 : F := E25 * ((65536 : F)⁻¹)
  let E27 : F := E26 - 1
  let E28 : F := E26 * E27
  let E29 : F := is_real * E28
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

end AddOperation
