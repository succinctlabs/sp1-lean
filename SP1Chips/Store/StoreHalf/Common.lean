import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.Constraints
import SP1Operations.Reader.CPUState.Constraints
import SP1Chips.Store.StoreHalf.Constraints

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace Store

namespace StoreHalf

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 800000 in
-- Higher heartbeats: the iff destructure unfolds the full constraint list.
lemma allHold_constraints_iff_of_is_real (Main : Vector (ZMod p) 45)
    (h_is_real : is_real Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    (List.Forall SP1Constraint.toProp
      (AddrAddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[21], Main[22], Main[23], Main[24]]
        { value := #v[Main[25], Main[26], Main[27]] } 1) ∧
    (Main[38] = 0 ∨ Main[38] = 1) ∧
    (Main[39] = 0 ∨ Main[39] = 1) ∧
    Main[28] * (Main[26] + Main[27]) = 1 ∧
    ((Main[25] - 4 * Main[39] - 2 * Main[38]) * (8 : ZMod p)⁻¹).val <
      2 ^ ZMod.val (13 : ZMod p) ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReaderImmutable.constraints Main[0] (Main[2] + Main[1] * 65536)
        #v[Main[3], Main[4], Main[5]] 37
        { op_a := Main[6], op_a_memory :=
        { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
          access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
          op_a_0 := Main[13], op_b := Main[14],
          op_b_memory :=
          { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
            access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } 1 1) ∧
    (Main[35] = 0 ∨ Main[35] = 1) ∧
    (Main[35] = 0 ∨ Main[0] = Main[33]) ∧
    Main[35] * (Main[2] + Main[1] * 65536 + 1) + (1 - Main[35]) * Main[0] -
      (Main[35] * Main[34] + (1 - Main[35]) * Main[33]) - 1 =
        Main[36] + Main[37] * 65536 ∧
    Main[36].val < 65536 ∧
    ((0 : ZMod p) < 256 ∧ Main[37] < (256 : ZMod p) ∧ (0 : ZMod p) < 256) ∧
    Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] ∧
    Main[40] = Main[29] + (Main[7] - Main[29]) * (1 - Main[38]) * (1 - Main[39]) ∧
    Main[41] = Main[30] + (Main[7] - Main[30]) * Main[38] * (1 - Main[39]) ∧
    Main[42] = Main[31] + (Main[7] - Main[31]) * (1 - Main[38]) * Main[39] ∧
    Main[43] = Main[32] + (Main[7] - Main[32]) * Main[38] * Main[39]) := by
  have : Main[44] = 1 := h_is_real
  simp [constraints, AddressOperation.constraints, this, sub_eq_zero,
    SP1Constraint.toProp]

end StoreHalf

end Store
