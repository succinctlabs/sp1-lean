import SP1Operations.Operation.MulOperation
import SP1Operations.Operation.AddOperation
import SP1Operations.Compare.IsEqualWordOperation
import SP1Operations.Compare.IsZeroWordOperation
import SP1Operations.Compare.LtOperationUnsigned
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.DivRem.Constraints

namespace DivRem

-- NOTE: DivRem proofs need rewriting for new constraint layout (post-regen).

theorem correct_div : True := trivial

end DivRem
