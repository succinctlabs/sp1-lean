import SP1Foundations
import SP1Operations.Compare.IsZeroOperation.Operation

namespace IsZeroOperation

section constraints

@[irreducible] def constraints
  (a : (Fin BB))
  (cols : IsZeroOperation)
  (is_real : (Fin BB))
  : SP1ConstraintList :=
  let E0 : Fin BB := cols.inverse * a
  let E1 : Fin BB := 1 - E0
  let E2 : Fin BB := E1 - cols.result
  let E3 : Fin BB := is_real * E2
  let E4 : Fin BB := cols.result - 1
  let E5 : Fin BB := cols.result * E4
  let E6 : Fin BB := is_real * E5
  let E7 : Fin BB := cols.result * a
  let E8 : Fin BB := is_real * E7
  [
    (.assertZero E3),
    (.assertZero E6),
    (.assertZero E8),
  ]

end constraints

end IsZeroOperation
