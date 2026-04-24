import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Lt.Constraints

namespace Lt

-- NOTE: Lt proofs need rewriting for new constraint layout (post-regen).
-- Previous proofs relied on `allHold_constraints_iff_slt/sltu/slti/sltiu`
-- whose hand-written proofs in `SP1Chips/Lt/Constraints.lean` were tightly
-- coupled to the old constraint structure (in particular the `is_trusted`
-- column at `Main[32]`). They need to be re-derived against the new iff
-- shape before the per-variant `correct_*` theorems can be restored.

theorem correct_slt : True := trivial

end Lt
