import SP1Foundations
import SP1Operations.Operation.SubwOperation.Operation
import SP1Operations.Operation.U16MSBOperation

namespace SubwOperation

section constraints

def constraints
  (a : (Word (Fin BB)))
  (b : (Word (Fin BB)))
  (cols : SubwOperation)
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
  let CS0 : SP1ConstraintList := U16MSBOperation.constraints cols.value[1] { msb := cols.msb.msb } is_real
  [
    (.assertZero E1),
    (.assertZero E10),
    (.assertZero E19),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real),
  ] ++ CS0

end constraints
