import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Operation.AddwOperation.Operation

namespace AddwOperation

section constraints

@[irreducible] def constraints {F : Type} [Field F]
  (a : (Word F))
  (b : (Word F))
  (cols : AddwOperation F)
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
  let CS0 : SP1ConstraintList F := U16MSBOperation.constraints cols.value[1] { msb := cols.msb.msb } is_real
  CS0 ++ [
    (.assertZero E1),
    (.assertZero E8),
    (.assertZero E15),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real),
  ]

end constraints

end AddwOperation
