import SP1Foundations
import SP1Operations.Compare.IsZeroOperation.Operation

namespace IsZeroOperation

section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (a : F)
  (cols : IsZeroOperation F)
  (is_real : F)
  : SP1ConstraintList F :=
  let E0 : F := cols.inverse * a
  let E1 : F := 1 - E0
  let E2 : F := E1 - cols.result
  let E3 : F := is_real * E2
  let E4 : F := cols.result - 1
  let E5 : F := cols.result * E4
  let E6 : F := is_real * E5
  let E7 : F := cols.result * a
  let E8 : F := is_real * E7
  [
    (.assertZero E3),
    (.assertZero E6),
    (.assertZero E8),
  ]

end constraints

end IsZeroOperation
