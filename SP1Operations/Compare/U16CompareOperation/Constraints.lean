import SP1Operations.Compare.U16CompareOperation.Operation
import SP1Foundations

namespace U16CompareOperation

section constraints

@[irreducible] def constraints
  (a : (Fin KB))
  (b : (Fin KB))
  (cols : U16CompareOperation)
  (is_real : (Fin KB))
  : SP1ConstraintList :=
  let E0 : Fin KB := is_real - 1
  let E1 : Fin KB := is_real * E0
  let E2 : Fin KB := cols.bit - 1
  let E3 : Fin KB := cols.bit * E2
  let E4 : Fin KB := a - b
  let E5 : Fin KB := cols.bit * 65536
  let E6 : Fin KB := E4 + E5
  [
    (.assertZero E1),
    (.assertZero E3),
    (.send (.byte (ByteOpcode.ofNat 6) E6 16 0) is_real),
  ]

end constraints

end U16CompareOperation
