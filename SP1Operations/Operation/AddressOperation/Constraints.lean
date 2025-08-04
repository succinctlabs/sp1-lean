import SP1Foundations
import SP1Operations.Operation.AddressOperation.Operation
import SP1Operations.Operation.AddrAddOperation.Constraints

namespace AddressOperation

section constraints

def constraints
  (b : (Word (Fin BB)))
  (cc : (Word (Fin BB)))
  (offset_bit0 : (Fin BB))
  (offset_bit1 : (Fin BB))
  (offset_bit2 : (Fin BB))
  (is_real : (Fin BB))
  (cols : AddressOperation)
  : (Vector (Fin BB) 3) × SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := offset_bit0 - 1
  let E3 : Fin BB := offset_bit0 * E2
  let E4 : Fin BB := offset_bit1 - 1
  let E5 : Fin BB := offset_bit1 * E4
  let E6 : Fin BB := offset_bit2 - 1
  let E7 : Fin BB := offset_bit2 * E6
  let CS0 : SP1ConstraintList := AddrAddOperation.constraints #v[b[0], b[1], b[2], b[3]] #v[cc[0], cc[1], cc[2], cc[3]] { value := #v[cols.addr_operation.value[0], cols.addr_operation.value[1], cols.addr_operation.value[2]] } is_real
  let E8 : Fin BB := cols.addr_operation.value[1] + cols.addr_operation.value[2]
  let E9 : Fin BB := cols.top_two_limb_inv * E8
  let E10 : Fin BB := E9 - is_real
  let E11 : Fin BB := 4 * offset_bit2
  let E12 : Fin BB := cols.addr_operation.value[0] - E11
  let E13 : Fin BB := 2 * offset_bit1
  let E14 : Fin BB := E12 - E13
  let E15 : Fin BB := E14 - offset_bit0
  let E16 : Fin BB := E15 * 1761607681
  let E17 : Fin BB := 4 * offset_bit2
  let E18 : Fin BB := cols.addr_operation.value[0] - E17
  let E19 : Fin BB := 2 * offset_bit1
  let E20 : Fin BB := E18 - E19
  let E21 : Fin BB := E20 - offset_bit0
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
