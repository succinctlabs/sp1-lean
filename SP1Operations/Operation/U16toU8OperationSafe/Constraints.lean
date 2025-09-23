import SP1Foundations
import SP1Operations.Operation.U16toU8OperationSafe.Operation

namespace U16toU8OperationSafe

section constraints

@[irreducible] def constraints
  (u16_values : (Vector (Fin BB) 4))
  (cols : U16toU8Operation)
  (is_real : (Fin BB))
  : (Vector (Fin BB) 8) × SP1ConstraintList :=
  let E0 : Fin BB := u16_values[0] - cols.low_bytes[0]
  let E1 : Fin BB := E0 * 2122383361
  let E2 : Fin BB := u16_values[1] - cols.low_bytes[1]
  let E3 : Fin BB := E2 * 2122383361
  let E4 : Fin BB := u16_values[2] - cols.low_bytes[2]
  let E5 : Fin BB := E4 * 2122383361
  let E6 : Fin BB := u16_values[3] - cols.low_bytes[3]
  let E7 : Fin BB := E6 * 2122383361
  ⟨#v[cols.low_bytes[0], E1, cols.low_bytes[1], E3, cols.low_bytes[2], E5, cols.low_bytes[3], E7], [
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[0] E1) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[1] E3) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[2] E5) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[3] E7) is_real),
  ]⟩

end constraints
