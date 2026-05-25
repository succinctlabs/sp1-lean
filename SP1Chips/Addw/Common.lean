import SP1Foundations
import SP1Operations.Operation.AddwOperation.AddwOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.Addw.Constraints

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace Addw

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option linter.unusedSectionVars false in
-- Polymorphic iff lemma mirroring `Add.allHold_constraints_iff` (canonical
-- `.allHold` form, post-2026-05-24 pilot refactor).
-- Exposes 3 sub-allHolds (AddwOp/CPUState/ALUTypeReader) + 2 chip-list assertZeros.
lemma allHold_constraints_iff (Main : Vector (ZMod p) 36) :
    (constraints Main).allHold ↔
    SP1ConstraintList.allHold
        (AddwOperation.constraints (F := ZMod p)
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]]
          { value := #v[Main[32], Main[33]], msb := { msb := Main[34] } }
          Main[35]) ∧
    SP1ConstraintList.allHold
        (_root_.CPUState.constraints
          (CPUState.mk Main[0] Main[1] Main[2] #v[Main[3], Main[4], Main[5]])
          #v[Main[3] + 4, Main[4], Main[5]] 8 Main[35]) ∧
    SP1ConstraintList.allHold
        (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536)
          #v[Main[3], Main[4], Main[5]] 19
          #v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535]
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13], op_b := Main[14],
            op_b_memory :=
              { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c := #v[Main[21], Main[22], Main[23], Main[24]],
            op_c_memory :=
              { prev_value := #v[Main[25], Main[26], Main[27], Main[28]],
                access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } },
            imm_c := Main[31] }
          Main[35] Main[35]) ∧
    Main[35] * (Main[35] - 1) = 0 ∧
    Main[13] = 0 := by
  simp only [constraints, List.forall_append, List.Forall, SP1Constraint.toProp,
    and_assoc]

end Addw
