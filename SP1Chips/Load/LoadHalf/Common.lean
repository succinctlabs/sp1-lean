import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Operation.U16MSBOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints
import SP1Chips.Load.LoadHalf.Constraints

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace Load

namespace LoadHalf

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

lemma allHold_constraints_iff_of_is_lh (Main : Vector (ZMod p) 44)
    (h_is_lh : is_lh Main) :
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
      (U16MSBOperation.constraints Main[40] { msb := Main[41] } 1) ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536)
        #v[Main[3], Main[4], Main[5]] 30
        #v[Main[40], 65535 * Main[41], 65535 * Main[41], 65535 * Main[41]]
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
    Main[43] = 0 ∧ Main[13] = 0 ∧
    (Main[38] = 1 ∨ Main[39] = 1 ∨ Main[40] = Main[29]) ∧
    (Main[38] = 0 ∨ Main[39] = 1 ∨ Main[40] = Main[30]) ∧
    (Main[38] = 1 ∨ Main[39] = 0 ∨ Main[40] = Main[31]) ∧
    (Main[38] = 0 ∨ Main[39] = 0 ∨ Main[40] = Main[32])) := by
  have : Main[42] = 1 := h_is_lh
  by_cases h43 : Main[43] = 0
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h43,
      SP1Constraint.toProp]
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h43,
      SP1Constraint.toProp]
    intros
    have h2 : (1 + 1 : ZMod p) ≠ 0 := by
      rw [show (1 + 1 : ZMod p) = (2 : ZMod p) from by norm_num]; exact val_2_ne_zero
    simp_all

lemma allHold_constraints_iff_of_is_lhu (Main : Vector (ZMod p) 44)
    (h_is_lhu : is_lhu Main) :
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
      (U16MSBOperation.constraints Main[40] { msb := Main[41] } 0) ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536)
        #v[Main[3], Main[4], Main[5]] 33
        #v[Main[40], 65535 * Main[41], 65535 * Main[41], 65535 * Main[41]]
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
    Main[42] = 0 ∧ Main[13] = 0 ∧
    (Main[38] = 1 ∨ Main[39] = 1 ∨ Main[40] = Main[29]) ∧
    (Main[38] = 0 ∨ Main[39] = 1 ∨ Main[40] = Main[30]) ∧
    (Main[38] = 1 ∨ Main[39] = 0 ∨ Main[40] = Main[31]) ∧
    (Main[38] = 0 ∨ Main[39] = 0 ∨ Main[40] = Main[32]) ∧
    Main[41] = 0) := by
  have : Main[43] = 1 := h_is_lhu
  by_cases h42 : Main[42] = 0
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h42,
      SP1Constraint.toProp]
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h42,
      SP1Constraint.toProp]
    intros
    have h2 : (1 + 1 : ZMod p) ≠ 0 := by
      rw [show (1 + 1 : ZMod p) = (2 : ZMod p) from by norm_num]; exact val_2_ne_zero
    simp_all

end LoadHalf

end Load
