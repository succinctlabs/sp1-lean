import SP1Foundations
import SP1Operations.Operation.U16toU8OperationUnsafe.Operation

namespace U16toU8OperationUnsafe

section constraints

@[irreducible] def constraints
  (u16_values : (Vector (Fin KB) 4))
  (cols : U16toU8Operation)
  : (Vector (Fin KB) 8) × SP1ConstraintList :=
  let E0 : Fin KB := u16_values[0] - cols.low_bytes[0]
  let E1 : Fin KB := E0 * 2122383361
  let E2 : Fin KB := u16_values[1] - cols.low_bytes[1]
  let E3 : Fin KB := E2 * 2122383361
  let E4 : Fin KB := u16_values[2] - cols.low_bytes[2]
  let E5 : Fin KB := E4 * 2122383361
  let E6 : Fin KB := u16_values[3] - cols.low_bytes[3]
  let E7 : Fin KB := E6 * 2122383361
  ⟨#v[cols.low_bytes[0], E1, cols.low_bytes[1], E3, cols.low_bytes[2], E5, cols.low_bytes[3], E7], [
  ]⟩

end constraints
