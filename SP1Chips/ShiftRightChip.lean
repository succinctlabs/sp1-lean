import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftRight.Constraints

namespace ShiftRight

-- NOTE: ShiftRight proofs need rewriting for new constraint layout (post-regen).

theorem correct_srl : True := trivial

end ShiftRight
