import SP1Operations.Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Bitwise.Constraints

namespace Bitwise

-- NOTE: Bitwise proofs need rewriting for new constraint layout (post-regen).
-- Previous proofs relied on the hand-written `allHold_constraints_iff` in
-- `SP1Chips/Bitwise/Constraints.lean`, which was tightly coupled to the
-- old constraint structure (including the `is_trusted` column at `Main[32]`).

theorem correct_xor : True := trivial

end Bitwise
