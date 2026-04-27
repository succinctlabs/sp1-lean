import SP1Operations.Compare.IsZeroWordOperation.Operation
import SP1Operations.Compare.IsZeroOperation

namespace IsZeroWordOperation

section constraints

@[irreducible] def constraints {F : Type} [Field F]
  (a : (Word F))
  (cols : IsZeroWordOperation F)
  (is_real : F)
  : SP1ConstraintList F :=
  let CS0 : SP1ConstraintList F := IsZeroOperation.constraints a[0] { inverse := cols.is_zero_limb[0].inverse, result := cols.is_zero_limb[0].result } is_real
  let CS1 : SP1ConstraintList F := IsZeroOperation.constraints a[1] { inverse := cols.is_zero_limb[1].inverse, result := cols.is_zero_limb[1].result } is_real
  let CS2 : SP1ConstraintList F := IsZeroOperation.constraints a[2] { inverse := cols.is_zero_limb[2].inverse, result := cols.is_zero_limb[2].result } is_real
  let CS3 : SP1ConstraintList F := IsZeroOperation.constraints a[3] { inverse := cols.is_zero_limb[3].inverse, result := cols.is_zero_limb[3].result } is_real
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := cols.result - 1
  let E3 : F := cols.result * E2
  let E4 : F := cols.is_zero_limb[0].result * cols.is_zero_limb[1].result
  let E5 : F := cols.is_zero_first_half - E4
  let E6 : F := cols.is_zero_limb[2].result * cols.is_zero_limb[3].result
  let E7 : F := cols.is_zero_second_half - E6
  let E8 : F := cols.is_zero_first_half * cols.is_zero_second_half
  let E9 : F := cols.result - E8
  let E10 : F := is_real * E9
  CS0 ++ CS1 ++ CS2 ++ CS3 ++ [
    (.assertZero E1),
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E10),
  ]

end constraints

end IsZeroWordOperation
