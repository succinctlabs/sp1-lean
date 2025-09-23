import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Operation.AddwOperation.Operation

namespace AddwOperation

section constraints

@[irreducible] def constraints
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
  let E5 : Fin BB := E4 * 2130673921
  let E6 : Fin BB := E5 - 1
  let E7 : Fin BB := E5 * E6
  let E8 : Fin BB := is_real * E7
  let E9 : Fin BB := a[1] + b[1]
  let E10 : Fin BB := E9 - cols.value[1]
  let E11 : Fin BB := E10 + E5
  let E12 : Fin BB := E11 * 2130673921
  let E13 : Fin BB := E12 - 1
  let E14 : Fin BB := E12 * E13
  let E15 : Fin BB := is_real * E14
  let CS0 : SP1ConstraintList := U16MSBOperation.constraints cols.value[1] { msb := cols.msb.msb } is_real
  CS0 ++ [
    (.assertZero E1),
    (.assertZero E8),
    (.assertZero E15),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real),
  ]

end constraints
