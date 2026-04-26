import SP1Foundations
import SP1Operations.Compare.IsZeroOperation.Operation

namespace IsZeroOperation

section constraints

@[irreducible] def constraints
  (a : (Fin KB))
  (cols : IsZeroOperation)
  (is_real : (Fin KB))
  : SP1ConstraintList (Fin KB) :=
  let E0 : Fin KB := cols.inverse * a
  let E1 : Fin KB := 1 - E0
  let E2 : Fin KB := E1 - cols.result
  let E3 : Fin KB := is_real * E2
  let E4 : Fin KB := cols.result - 1
  let E5 : Fin KB := cols.result * E4
  let E6 : Fin KB := is_real * E5
  let E7 : Fin KB := cols.result * a
  let E8 : Fin KB := is_real * E7
  [
    (.assertZero E3),
    (.assertZero E6),
    (.assertZero E8),
  ]

end constraints

end IsZeroOperation
