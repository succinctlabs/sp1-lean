import SP1Operations.Compare.IsEqualWordOperation.Operation
import SP1Operations.Compare.IsZeroWordOperation.IsZeroWordOperation

namespace IsEqualWordOperation

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (a : (Word F))
  (b : (Word F))
  (cols : IsEqualWordOperation F)
  (is_real : F)
  : SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := a[0] - b[0]
  let E3 : F := a[1] - b[1]
  let E4 : F := a[2] - b[2]
  let E5 : F := a[3] - b[3]
  let CS0 : SP1ConstraintList F := IsZeroWordOperation.constraints #v[E2, E3, E4, E5] { is_zero_limb := #v[{ inverse := cols.is_diff_zero.is_zero_limb[0].inverse, result := cols.is_diff_zero.is_zero_limb[0].result }, { inverse := cols.is_diff_zero.is_zero_limb[1].inverse, result := cols.is_diff_zero.is_zero_limb[1].result }, { inverse := cols.is_diff_zero.is_zero_limb[2].inverse, result := cols.is_diff_zero.is_zero_limb[2].result }, { inverse := cols.is_diff_zero.is_zero_limb[3].inverse, result := cols.is_diff_zero.is_zero_limb[3].result }], is_zero_first_half := cols.is_diff_zero.is_zero_first_half, is_zero_second_half := cols.is_diff_zero.is_zero_second_half, result := cols.is_diff_zero.result } is_real
  CS0 ++ [
    (.assertZero E1),
  ]

end constraints

end IsEqualWordOperation
