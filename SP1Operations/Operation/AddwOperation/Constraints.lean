import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Operation.AddwOperation.Operation

namespace AddwOperation

section constraints

@[irreducible] def constraints
  (a : (Word (Fin KB)))
  (b : (Word (Fin KB)))
  (cols : AddwOperation)
  (is_real : (Fin KB))
  : SP1ConstraintList (Fin KB) :=
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
  let CS0 : SP1ConstraintList (Fin KB) := U16MSBOperation.constraints cols.value[1] { msb := cols.msb.msb } is_real
  CS0 ++ [
    (.assertZero E1),
    (.assertZero E8),
    (.assertZero E15),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real),
  ]

end constraints

end AddwOperation
