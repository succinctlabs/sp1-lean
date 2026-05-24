import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.ITypeReaderImmutable
import SP1Operations.Reader.CPUState.CPUState
import SP1Chips.Load.LoadX0.Constraints

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace Load

namespace LoadX0

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option linter.unusedSectionVars false in
-- Polymorphic iff lemma mirroring `Bitwise.allHold_constraints_iff`.
-- Unfolds AddressOperation.constraints (which itself produces an AddrAddOp
-- sub-list + offset asserts + an offset-byte send) and the chip-level
-- constraints. Exposes 2 named sub-allHolds (CPUState/ITypeReaderImmutable) +
-- the AddrAddOp sub-list + flattened chip-list props.
lemma allHold_constraints_iff (Main : Vector (ZMod p) 48) :
    List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp
        (AddrAddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[21], Main[22], Main[23], Main[24]]
          { value := #v[Main[25], Main[26], Main[27]] }
          (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47])) ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47]) *
      (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] - 1) = 0 ∧
    Main[38] * (Main[38] - 1) = 0 ∧
    Main[39] * (Main[39] - 1) = 0 ∧
    Main[40] * (Main[40] - 1) = 0 ∧
    Main[28] * (Main[26] + Main[27]) -
      (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47]) = 0 ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] ≠ 0 →
      (ByteOpcode.ofNat 6).constrain
        ((Main[25] - (4 : ZMod p) * Main[40] - (2 : ZMod p) * Main[39] - Main[38]) * (8 : ZMod p)⁻¹) 13 0) ∧
    List.Forall SP1Constraint.toProp
        (_root_.CPUState.constraints
          (CPUState.mk Main[0] Main[1] Main[2] #v[Main[3], Main[4], Main[5]])
          #v[Main[3] + 4, Main[4], Main[5]] 8
          (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47])) ∧
    List.Forall SP1Constraint.toProp
        (ITypeReaderImmutable.constraints Main[0] (Main[2] + Main[1] * 65536)
          #v[Main[3], Main[4], Main[5]]
          ((29 : ZMod p) * Main[41] + 32 * Main[42] + 30 * Main[43] + 33 * Main[44] +
            31 * Main[45] + 34 * Main[46] + 35 * Main[47])
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13], op_b := Main[14],
            op_b_memory :=
              { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] }
          (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47])
          (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47])) ∧
    Main[41] * (Main[41] - 1) = 0 ∧
    Main[42] * (Main[42] - 1) = 0 ∧
    Main[43] * (Main[43] - 1) = 0 ∧
    Main[44] * (Main[44] - 1) = 0 ∧
    Main[45] * (Main[45] - 1) = 0 ∧
    Main[46] * (Main[46] - 1) = 0 ∧
    Main[47] * (Main[47] - 1) = 0 ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47]) *
      (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] - 1) = 0 ∧
    Main[47] * Main[40] = 0 ∧
    (Main[45] + Main[46] + Main[47]) * Main[39] = 0 ∧
    (Main[43] + Main[44] + Main[45] + Main[46] + Main[47]) * Main[38] = 0 ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47]) *
      (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] - 1) = 0 ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47]) *
      (Main[35] * (Main[35] - 1)) = 0 ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47]) *
      (Main[35] * (Main[0] - Main[33])) = 0 ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47]) *
      (Main[35] * (Main[2] + Main[1] * 65536 + 1) + (1 - Main[35]) * Main[0] -
          (Main[35] * Main[34] + (1 - Main[35]) * Main[33]) - 1 -
        (Main[36] + Main[37] * 65536)) = 0 ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] ≠ 0 →
      (ByteOpcode.ofNat 6).constrain Main[36] 16 0) ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] ≠ 0 →
      (ByteOpcode.ofNat 3).constrain 0 Main[37] 0) ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] ≠ 0 →
      Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]]) ∧
    True ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47]) *
      (Main[13] - 1) = 0 ∧
    (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] - 1) *
      Main[13] = 0 := by
  unfold constraints AddressOperation.constraints
  simp only [List.forall_append, List.Forall, SP1Constraint.toProp, and_assoc,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  push_cast
  rfl

end LoadX0

end Load
