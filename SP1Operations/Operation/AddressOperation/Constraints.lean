import SP1Foundations
import SP1Operations.Operation.AddressOperation.Operation
import SP1Operations.Operation.AddrAddOperation.Constraints

namespace AddressOperation

section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (b : (Word F))
  (cc : (Word F))
  (offset_bit0 : F)
  (offset_bit1 : F)
  (offset_bit2 : F)
  (is_real : F)
  (cols : AddressOperation F)
  : (Vector F 3) × SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := offset_bit0 - 1
  let E3 : F := offset_bit0 * E2
  let E4 : F := offset_bit1 - 1
  let E5 : F := offset_bit1 * E4
  let E6 : F := offset_bit2 - 1
  let E7 : F := offset_bit2 * E6
  let CS0 : SP1ConstraintList F := AddrAddOperation.constraints #v[b[0], b[1], b[2], b[3]] #v[cc[0], cc[1], cc[2], cc[3]] { value := #v[cols.addr_operation.value[0], cols.addr_operation.value[1], cols.addr_operation.value[2]] } is_real
  let E8 : F := cols.addr_operation.value[1] + cols.addr_operation.value[2]
  let E9 : F := cols.top_two_limb_inv * E8
  let E10 : F := E9 - is_real
  let E11 : F := 4 * offset_bit2
  let E12 : F := cols.addr_operation.value[0] - E11
  let E13 : F := 2 * offset_bit1
  let E14 : F := E12 - E13
  let E15 : F := E14 - offset_bit0
  let E16 : F := E15 * ((8 : F)⁻¹)
  let E17 : F := 4 * offset_bit2
  let E18 : F := cols.addr_operation.value[0] - E17
  let E19 : F := 2 * offset_bit1
  let E20 : F := E18 - E19
  let E21 : F := E20 - offset_bit0
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
