import SP1Foundations
import SP1Operations.Operation.U16MSBOperation.Operation

namespace U16MSBOperation

section constraints

@[irreducible] def constraints {F : Type*} [Field F]
  (a : F)
  (cols : U16MSBOperation F)
  (is_real : F)
  : SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := cols.msb - 1
  let E3 : F := cols.msb * E2
  let E4 : F := 2 * a
  let E5 : F := cols.msb * 65536
  let E6 : F := E4 - E5
  [
    (.assertZero E1),
    (.assertZero E3),
    (.send (.byte (ByteOpcode.ofNat 6) E6 16 0) is_real),
  ]

end constraints

end U16MSBOperation
