import SP1Foundations
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ITypeReader.ITypeReader
import SP1Chips.Jalr.Constraints

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace Jalr

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option linter.unusedSectionVars false in
-- Polymorphic iff lemma mirroring `Bitwise.allHold_constraints_iff`.
-- Exposes 4 sub-allHolds (AddOp jump-target + CPUState + ITypeReader +
-- AddOp return-addr) plus the 9 chip-list assertZero/byte-send props.
lemma allHold_constraints_iff (Main : Vector (ZMod p) 35) :
    List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp
        (AddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[21], Main[22], Main[23], Main[24]]
          { value := #v[Main[26], Main[27], Main[28], Main[29]] } Main[25]) ∧
    List.Forall SP1Constraint.toProp
        (_root_.CPUState.constraints
          (CPUState.mk Main[0] Main[1] Main[2] #v[Main[3], Main[4], Main[5]])
          #v[Main[26] - Main[34], Main[27], Main[28]] 8 Main[25]) ∧
    List.Forall SP1Constraint.toProp
        (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536)
          #v[Main[3], Main[4], Main[5]] 47
          #v[Main[30], Main[31], Main[32], Main[33]]
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13], op_b := Main[14],
            op_b_memory :=
              { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] }
          Main[25] Main[25]) ∧
    List.Forall SP1Constraint.toProp
        (AddOperation.constraints #v[Main[3], Main[4], Main[5], (0 : ZMod p)]
          #v[(4 : ZMod p), 0, 0, 0]
          { value := #v[Main[30], Main[31], Main[32], Main[33]] }
          (Main[25] - Main[13])) ∧
    Main[25] * (Main[25] - 1) = 0 ∧
    Main[29] = 0 ∧
    Main[34] * (Main[34] - 1) = 0 ∧
    (Main[25] ≠ 0 → (ByteOpcode.ofNat 6).constrain ((Main[26] - Main[34]) * (4 : ZMod p)⁻¹) 14 0) ∧
    (Main[25] - (1 : ZMod p)) * Main[13] = 0 ∧
    Main[33] = 0 ∧
    Main[13] * Main[30] = 0 ∧
    Main[13] * Main[31] = 0 ∧
    Main[13] * Main[32] = 0 := by
  simp only [constraints, List.forall_append, List.Forall, SP1Constraint.toProp,
    and_assoc]

end Jalr
