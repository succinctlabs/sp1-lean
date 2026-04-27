import SP1Foundations
import SP1Operations.Operation.AddressOperation.Operation
import SP1Operations.Operation.AddrAddOperation.Constraints

namespace AddressOperation

section constraints

@[irreducible] def constraints
  (b : (Word (Fin KB)))
  (cc : (Word (Fin KB)))
  (offset_bit0 : (Fin KB))
  (offset_bit1 : (Fin KB))
  (offset_bit2 : (Fin KB))
  (is_real : (Fin KB))
  (cols : AddressOperation)
  : (Vector (Fin KB) 3) × SP1ConstraintList (Fin KB) :=
  let E0 : Fin KB := is_real - 1
  let E1 : Fin KB := is_real * E0
  let E2 : Fin KB := offset_bit0 - 1
  let E3 : Fin KB := offset_bit0 * E2
  let E4 : Fin KB := offset_bit1 - 1
  let E5 : Fin KB := offset_bit1 * E4
  let E6 : Fin KB := offset_bit2 - 1
  let E7 : Fin KB := offset_bit2 * E6
  let CS0 : SP1ConstraintList (Fin KB) := AddrAddOperation.constraints #v[b[0], b[1], b[2], b[3]] #v[cc[0], cc[1], cc[2], cc[3]] { value := #v[cols.addr_operation.value[0], cols.addr_operation.value[1], cols.addr_operation.value[2]] } is_real
  let E8 : Fin KB := cols.addr_operation.value[1] + cols.addr_operation.value[2]
  let E9 : Fin KB := cols.top_two_limb_inv * E8
  let E10 : Fin KB := E9 - is_real
  let E11 : Fin KB := 4 * offset_bit2
  let E12 : Fin KB := cols.addr_operation.value[0] - E11
  let E13 : Fin KB := 2 * offset_bit1
  let E14 : Fin KB := E12 - E13
  let E15 : Fin KB := E14 - offset_bit0
  let E16 : Fin KB := E15 * ((8 : Fin KB)⁻¹)
  let E17 : Fin KB := 4 * offset_bit2
  let E18 : Fin KB := cols.addr_operation.value[0] - E17
  let E19 : Fin KB := 2 * offset_bit1
  let E20 : Fin KB := E18 - E19
  let E21 : Fin KB := E20 - offset_bit0
  ⟨#v[E21, cols.addr_operation.value[1], cols.addr_operation.value[2]], CS0 ++ [
    (.assertZero E1),
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E10),
    (.send (.byte (ByteOpcode.ofNat 6) E16 13 0) is_real),
  ]⟩

end constraints

end AddressOperation
