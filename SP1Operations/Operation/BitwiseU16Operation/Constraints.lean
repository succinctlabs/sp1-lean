import SP1Operations.Operation.U16toU8OperationUnsafe
import SP1Operations.Operation.BitwiseOperation
import SP1Operations.Operation.BitwiseU16Operation.Operation

namespace BitwiseU16Operation

section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (b : (Word F))
  (cc : (Word F))
  (cols : BitwiseU16Operation F)
  (opcode : F)
  (is_real : F)
  : (Word F) × SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let ⟨⟨⟨[E2, E3, E4, E5, E6, E7, E8, E9]⟩, _⟩, CS0⟩ := U16toU8OperationUnsafe.constraints #v[b[0], b[1], b[2], b[3]] { low_bytes := #v[cols.b_low_bytes.low_bytes[0], cols.b_low_bytes.low_bytes[1], cols.b_low_bytes.low_bytes[2], cols.b_low_bytes.low_bytes[3]] }
  let ⟨⟨⟨[E10, E11, E12, E13, E14, E15, E16, E17]⟩, _⟩, CS1⟩ := U16toU8OperationUnsafe.constraints #v[cc[0], cc[1], cc[2], cc[3]] { low_bytes := #v[cols.c_low_bytes.low_bytes[0], cols.c_low_bytes.low_bytes[1], cols.c_low_bytes.low_bytes[2], cols.c_low_bytes.low_bytes[3]] }
  let CS2 : SP1ConstraintList F := BitwiseOperation.constraints #v[E2, E3, E4, E5, E6, E7, E8, E9] #v[E10, E11, E12, E13, E14, E15, E16, E17] { result := #v[cols.bitwise_operation.result[0], cols.bitwise_operation.result[1], cols.bitwise_operation.result[2], cols.bitwise_operation.result[3], cols.bitwise_operation.result[4], cols.bitwise_operation.result[5], cols.bitwise_operation.result[6], cols.bitwise_operation.result[7]] } opcode is_real
  let E18 : F := cols.bitwise_operation.result[1] * 256
  let E19 : F := cols.bitwise_operation.result[0] + E18
  let E20 : F := cols.bitwise_operation.result[3] * 256
  let E21 : F := cols.bitwise_operation.result[2] + E20
  let E22 : F := cols.bitwise_operation.result[5] * 256
  let E23 : F := cols.bitwise_operation.result[4] + E22
  let E24 : F := cols.bitwise_operation.result[7] * 256
  let E25 : F := cols.bitwise_operation.result[6] + E24
  ⟨#v[E19, E21, E23, E25], CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
  ]⟩

end constraints

end BitwiseU16Operation
