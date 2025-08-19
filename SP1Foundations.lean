import SP1Foundations.BitVec
import SP1Foundations.ByteOpcode
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Foundations.MemoryConsistency
import SP1Foundations.Misc
import SP1Foundations.Opcode
import SP1Foundations.Register
import SP1Foundations.SP1State
import SP1Foundations.SailM
import SP1Foundations.Tactics
import SP1Foundations.Unsigned
import SP1Foundations.Word

----------------------------------
---- Special Indexing Macro ------
----------------------------------
macro_rules | `(tactic| get_elem_tactic) => `(tactic| norm_num1)

-- syntax:max term noWs "[" withoutPosition(term) "]$" : term
-- macro_rules | `($x[$i]$ ) => `(getElem $x $i (by decide +kernel))
--------------------------------------------------------------------

section grind

grind_pattern Fin.coe_ofNat_eq_mod => (@Fin.val m (OfNat.ofNat n))

end grind
