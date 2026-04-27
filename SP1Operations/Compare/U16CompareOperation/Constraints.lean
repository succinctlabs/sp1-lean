import SP1Operations.Compare.U16CompareOperation.Operation
import SP1Foundations

namespace U16CompareOperation

section constraints

@[irreducible] def constraints {F : Type*} [Field F]
  (a : F)
  (b : F)
  (cols : U16CompareOperation F)
  (is_real : F)
  : SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := cols.bit - 1
  let E3 : F := cols.bit * E2
  let E4 : F := a - b
  let E5 : F := cols.bit * 65536
  let E6 : F := E4 + E5
  [
    (.assertZero E1),
    (.assertZero E3),
    (.send (.byte (ByteOpcode.ofNat 6) E6 16 0) is_real),
  ]

end constraints

end U16CompareOperation
