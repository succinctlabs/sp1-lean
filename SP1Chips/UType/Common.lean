import SP1Foundations
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.JTypeReader.JTypeReader
import SP1Chips.UType.Constraints

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace UType

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option linter.unusedSectionVars false in
-- Polymorphic iff lemma mirroring `Sub.allHold_constraints_iff`.
-- Exposes 3 sub-allHolds (CPUState/AddOp/JTypeReader) + 7 chip-list assertZeros.
lemma allHold_constraints_iff (Main : Vector (ZMod p) 31) :
    List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp
        (_root_.CPUState.constraints
          (CPUState.mk Main[0] Main[1] Main[2] #v[Main[3], Main[4], Main[5]])
          #v[Main[3] + 4, Main[4], Main[5]] 8 Main[30]) ∧
    List.Forall SP1Constraint.toProp
        (AddOperation.constraints (F := ZMod p)
          #v[Main[22], Main[23], Main[24], 0]
          #v[Main[14], Main[15], Main[16], Main[17]]
          { value := #v[Main[25], Main[26], Main[27], Main[28]] }
          (Main[30] - Main[13])) ∧
    List.Forall SP1Constraint.toProp
        (JTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536)
          #v[Main[3], Main[4], Main[5]]
          (Main[29] * 48 + ((1 : ZMod p) - Main[29]) * 49)
          #v[Main[25], Main[26], Main[27], Main[28]]
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13],
            op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]],
            op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] }
          Main[30] Main[30]) ∧
    Main[30] * (Main[30] - 1) = 0 ∧
    Main[29] * (Main[29] - 1) = 0 ∧
    Main[22] - (Main[29] * Main[3] + ((1 : ZMod p) - Main[29]) * 0) = 0 ∧
    Main[23] - (Main[29] * Main[4] + ((1 : ZMod p) - Main[29]) * 0) = 0 ∧
    Main[24] - (Main[29] * Main[5] + ((1 : ZMod p) - Main[29]) * 0) = 0 ∧
    (0 : ZMod p) - (Main[29] * 0 + ((1 : ZMod p) - Main[29]) * 0) = 0 ∧
    (Main[30] - (1 : ZMod p)) * Main[13] = 0 := by
  simp only [constraints, List.forall_append, List.Forall, SP1Constraint.toProp,
    and_assoc]
  push_cast
  rfl

end UType
