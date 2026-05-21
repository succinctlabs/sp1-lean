import SP1Foundations
import SP1Operations.Operation.SubwOperation.Operation
import SP1Operations.Operation.U16MSBOperation

namespace SubwOperation

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (a : (Word F))
  (b : (Word F))
  (cols : SubwOperation F)
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
  let CS0 : SP1ConstraintList F := U16MSBOperation.constraints cols.value[1] { msb := cols.msb.msb } is_real
  CS0 ++ [
    (.assertZero E1),
    (.assertZero E10),
    (.assertZero E19),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.value[1] 16 0) is_real),
  ]

end constraints

end SubwOperation
