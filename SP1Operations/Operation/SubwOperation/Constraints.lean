import SP1Foundations
import SP1Operations.Operation.SubwOperation.Operation
import SP1Operations.Operation.U16MSBOperation

namespace SubwOperation

section constraints

@[irreducible] def constraints
  (a : (Word (Fin KB)))
  (b : (Word (Fin KB)))
  (cols : SubwOperation)
  (is_real : (Fin KB))
  : SP1ConstraintList (Fin KB) :=
  let E0 : Fin KB := is_real - 1
  let E1 : Fin KB := is_real * E0
  let E2 : Fin KB := a[0] + 65536
  let E3 : Fin KB := E2 - 1
  let E4 : Fin KB := E3 - b[0]
  let E5 : Fin KB := E4 - cols.value[0]
  let E6 : Fin KB := E5 + 1
  let E7 : Fin KB := E6 * ((65536 : Fin KB)⁻¹)
  let E8 : Fin KB := E7 - 1
  let E9 : Fin KB := E7 * E8
  let E10 : Fin KB := is_real * E9
  let E11 : Fin KB := a[1] + 65536
  let E12 : Fin KB := E11 - 1
  let E13 : Fin KB := E12 - b[1]
  let E14 : Fin KB := E13 - cols.value[1]
  let E15 : Fin KB := E14 + E7
  let E16 : Fin KB := E15 * ((65536 : Fin KB)⁻¹)
  let E17 : Fin KB := E16 - 1
  let E18 : Fin KB := E16 * E17
  let E19 : Fin KB := is_real * E18
  let CS0 : SP1ConstraintList (Fin KB) := U16MSBOperation.constraints cols.value[1] { msb := cols.msb.msb } is_real
  CS0 ++ [
    (.assertZero E1),
    (.assertZero E10),
    (.assertZero E19),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real),
  ]

end constraints

end SubwOperation
