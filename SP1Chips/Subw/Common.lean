import SP1Foundations
import SP1Operations.Operation.SubwOperation.SubwOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Subw.Constraints

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace Subw

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option linter.unusedSectionVars false in
-- Polymorphic iff lemma mirroring `Sub.allHold_constraints_iff` (canonical
-- ALU-chip shape: both sides in `.allHold` form, not `List.Forall toProp`).
-- Exposes 3 sub-allHolds (SubwOp/CPUState/RTypeReader) + 2 chip-list assertZeros.
lemma allHold_constraints_iff (Main : Vector (ZMod p) 32) :
    (constraints Main).allHold ↔
    SP1ConstraintList.allHold
        (SubwOperation.constraints (F := ZMod p)
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[22], Main[23], Main[24], Main[25]]
          { value := #v[Main[28], Main[29]], msb := { msb := Main[30] } }
          Main[31]) ∧
    SP1ConstraintList.allHold
        (_root_.CPUState.constraints
          (CPUState.mk Main[0] Main[1] Main[2] #v[Main[3], Main[4], Main[5]])
          #v[Main[3] + 4, Main[4], Main[5]] 8 Main[31]) ∧
    SP1ConstraintList.allHold
        (RTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536)
          #v[Main[3], Main[4], Main[5]] 20
          #v[Main[28], Main[29], Main[30] * 65535, Main[30] * 65535]
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13], op_b := Main[14],
            op_b_memory :=
              { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c := Main[21],
            op_c_memory :=
              { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } }
          Main[31] Main[31]) ∧
    Main[31] * (Main[31] - 1) = 0 ∧
    Main[13] = 0 := by
  simp only [constraints, List.forall_append, List.Forall, SP1Constraint.toProp,
    and_assoc]

end Subw
