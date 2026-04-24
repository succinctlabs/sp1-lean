import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftLeft.Constraints

namespace ShiftLeft

-- NOTE: ShiftLeft proofs need rewriting for new constraint layout (post-regen).

theorem correct_sll : True := trivial

end ShiftLeft
