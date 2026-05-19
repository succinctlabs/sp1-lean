import SP1Foundations
import SP1Operations.Operation.U16toU8OperationSafe.Operation

namespace U16toU8OperationSafe

section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (u16_values : (Vector F 4))
  (cols : U16toU8Operation F)
  (is_real : F)
  : (Vector F 8) × SP1ConstraintList F :=
  let E0 : F := u16_values[0] - cols.low_bytes[0]
  let E1 : F := E0 * ((256 : F)⁻¹)
  let E2 : F := u16_values[1] - cols.low_bytes[1]
  let E3 : F := E2 * ((256 : F)⁻¹)
  let E4 : F := u16_values[2] - cols.low_bytes[2]
  let E5 : F := E4 * ((256 : F)⁻¹)
  let E6 : F := u16_values[3] - cols.low_bytes[3]
  let E7 : F := E6 * ((256 : F)⁻¹)
  ⟨#v[cols.low_bytes[0], E1, cols.low_bytes[1], E3, cols.low_bytes[2], E5, cols.low_bytes[3], E7], [
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[0] E1) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[1] E3) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[2] E5) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.low_bytes[3] E7) is_real),
  ]⟩

end constraints

end U16toU8OperationSafe
