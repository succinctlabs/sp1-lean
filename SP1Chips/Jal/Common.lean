import SP1Foundations
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Chips.Jal.Constraints

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace Jal

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option linter.unusedSectionVars false in
-- Polymorphic iff lemma mirroring `Bitwise.allHold_constraints_iff`.
-- Exposes 2 AddOp sub-allHolds (jump-target + return-address) + the chip-list
-- assertZero/byte-send/state/memory props. The `True` conjuncts come from
-- `.receive (.state ...)` / `.send (.state ...)` / `.receive (.memory ...)`
-- whose `toProp` falls through to `True`.
lemma allHold_constraints_iff (Main : Vector (ZMod p) 31) :
    List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp
        (AddOperation.constraints
          #v[Main[3], Main[4], Main[5], (0 : ZMod p)]
          #v[Main[14], Main[15], Main[16], Main[17]]
          { value := #v[Main[22], Main[23], Main[24], Main[25]] } Main[30]) ∧
    List.Forall SP1Constraint.toProp
        (AddOperation.constraints
          #v[Main[3], Main[4], Main[5], (0 : ZMod p)]
          #v[(4 : ZMod p), 0, 0, 0]
          { value := #v[Main[26], Main[27], Main[28], Main[29]] }
          (Main[30] - Main[13])) ∧
    Main[30] * (Main[30] - 1) = 0 ∧
    Main[25] = 0 ∧
    (Main[30] ≠ 0 → (ByteOpcode.ofNat 6).constrain (Main[22] * (4 : ZMod p)⁻¹) 14 0) ∧
    Main[30] * (Main[30] - 1) = 0 ∧
    True ∧
    True ∧
    (Main[30] ≠ 0 → (ByteOpcode.ofNat 6).constrain ((Main[2] - 1) * (8 : ZMod p)⁻¹) 13 0) ∧
    (Main[30] ≠ 0 → (ByteOpcode.ofNat 3).constrain 0 Main[1] 0) ∧
    (Main[30] - (1 : ZMod p)) * Main[13] = 0 ∧
    Main[29] = 0 ∧
    Main[13] * Main[26] = 0 ∧
    Main[13] * Main[27] = 0 ∧
    Main[13] * Main[28] = 0 ∧
    Main[30] * (Main[30] - 1) = 0 ∧
    (Main[30] ≠ 0 →
      (Opcode.ofNat 46).trusted_instr Main[6] Main[14] Main[15] Main[16] Main[17]
          Main[18] Main[19] Main[20] Main[21] 1 1 ∧
        Main[6] < 32 ∧
        Main[14] < 65536 ∧ Main[15] < 65536 ∧ Main[16] < 65536 ∧ Main[17] < 65536 ∧
        Main[18] < 65536 ∧ Main[19] < 65536 ∧ Main[20] < 65536 ∧ Main[21] < 65536 ∧
        (Main[13] = 0 ∨ Main[13] = 1) ∧
        (Main[13] = 1 ↔ Main[6] = 0) ∧
        ((1 : ZMod p) = 0 ∨ True) ∧
        ((1 : ZMod p) = 0 ∨ True) ∧
        Main[3] % 4 = 0 ∧
        Main[3] < 65536 ∧ Main[4] < 65536 ∧ Main[5] < 65536) ∧
    Main[13] * (Main[26] - 0) = 0 ∧
    Main[13] * (Main[27] - 0) = 0 ∧
    Main[13] * (Main[28] - 0) = 0 ∧
    Main[13] * (Main[29] - 0) = 0 ∧
    Main[30] * (Main[30] - 1) = 0 ∧
    (Main[30] ≠ 0 → (ByteOpcode.ofNat 6).constrain Main[12] 16 0) ∧
    (Main[30] ≠ 0 → (ByteOpcode.ofNat 3).constrain 0
      ((Main[2] + Main[1] * (65536 : ZMod p) + (4 : ZMod p) - Main[11] - (1 : ZMod p) -
            Main[12]) * (65536 : ZMod p)⁻¹) 0) ∧
    (Main[30] ≠ 0 → Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]]) ∧
    True := by
  simp only [constraints, List.forall_append, List.Forall, SP1Constraint.toProp,
    and_assoc]

end Jal
