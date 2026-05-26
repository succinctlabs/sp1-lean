import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.Lt.Constraints

namespace Lt

set_option linter.style.setOption false
set_option linter.style.longLine false

set_option linter.unusedSectionVars false in
-- Canonical .allHold-form iff (post-AddChip refactor, see
-- `docs/CLEAN_FUTURE.md` "Canonical ALU-chip Layer-0/Layer-2 shape").
-- Exposes 3 sub-allHolds
-- (LtOperationSigned/CPUState/ALUTypeReader) + 4 trailing scalar gates
-- (2 selector binaries + sum binary + op_a_0). Consumed by SP1Clean's
-- chip-level `allHold_iff_structural` bridge.
lemma allHold_constraints_iff
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (Main : Vector (ZMod p) 44) :
    (constraints Main).allHold ↔
    SP1ConstraintList.allHold
        (LtOperationSigned.constraints (F := ZMod p)
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]]
          { result := { u16_compare_operation := { bit := Main[34] },
                        u16_flags := #v[Main[35], Main[36], Main[37], Main[38]],
                        not_eq_inv := Main[39],
                        comparison_limbs := #v[Main[40], Main[41]] },
            b_msb := { msb := Main[42] },
            c_msb := { msb := Main[43] } }
          Main[32] (Main[32] + Main[33])) ∧
    SP1ConstraintList.allHold
        (_root_.CPUState.constraints
          (CPUState.mk Main[0] Main[1] Main[2] #v[Main[3], Main[4], Main[5]])
          #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[32] + Main[33])) ∧
    SP1ConstraintList.allHold
        (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536)
          #v[Main[3], Main[4], Main[5]]
          (Main[32] * 9 + Main[33] * 10)
          #v[0 + Main[34], 0, 0, 0]
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
          (Main[32] + Main[33]) (Main[32] + Main[33])) ∧
    Main[32] * (Main[32] - 1) = 0 ∧
    Main[33] * (Main[33] - 1) = 0 ∧
    (Main[32] + Main[33]) * (Main[32] + Main[33] - 1) = 0 ∧
    Main[13] = 0 := by
  -- Mirrors AddChip's iff; trailing `push_cast; rfl` cleans the
  -- `↑9` literal cast residue introduced by `Main[32] * 9 + Main[33] * 10`
  -- (the literals `9`/`10` are field-typed in the constraints body but
  -- the hand-typed RHS elaborates the leading `9` as `ℕ`).
  simp only [constraints, List.forall_append, List.Forall, SP1Constraint.toProp,
    and_assoc]
  push_cast
  rfl

lemma allHold_constraints_iff_slt
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (Main : Vector (ZMod p) 44) (h : is_slt Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[32] * 9 + Main[33] * 10) #v[Main[34], 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[32] + Main[33]) (Main[32] + Main[33])) ∧
    Main[33] = 0 ∧ Main[13] = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h32, h31⟩ := h
  have h2_lt : (2 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h2_val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2_lt
  have h2_ne : ((1 : ZMod p) + 1) ≠ 0 := by
    intro heq
    have : (2 : ZMod p) = 0 := by linear_combination heq
    rw [this, ZMod.val_zero] at h2_val
    omega
  simp_all [constraints, sub_eq_zero]
  intros
  refine ⟨?_, ?_⟩
  · rintro ⟨h33_bit, h_pair, h13⟩
    refine ⟨?_, h13⟩
    rcases h33_bit with h33 | h33
    · exact h33
    · exfalso
      rcases h_pair with h_pair | h_pair
      · rw [h33] at h_pair; exact h2_ne h_pair
      · rw [h_pair] at h33; exact zero_ne_one h33
  · rintro ⟨h33, h13⟩
    exact ⟨Or.inl h33, Or.inr h33, h13⟩

lemma allHold_constraints_iff_sltu
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (Main : Vector (ZMod p) 44) (h : is_sltu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[32] * 9 + Main[33] * 10) #v[Main[34], 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[32] + Main[33]) (Main[32] + Main[33])) ∧
    Main[32] = 0 ∧ Main[13] = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h33, h31⟩ := h
  have h2_lt : (2 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h2_val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2_lt
  have h2_ne : ((1 : ZMod p) + 1) ≠ 0 := by
    intro heq
    have : (2 : ZMod p) = 0 := by linear_combination heq
    rw [this, ZMod.val_zero] at h2_val
    omega
  simp_all [constraints, sub_eq_zero]
  intros
  refine ⟨?_, ?_⟩
  · rintro ⟨h32_bit, h_pair, h13⟩
    refine ⟨?_, h13⟩
    rcases h32_bit with h32 | h32
    · exact h32
    · exfalso
      rcases h_pair with h_pair | h_pair
      · rw [h32] at h_pair
        exact h2_ne (by linear_combination h_pair)
      · rw [h_pair] at h32; exact zero_ne_one h32
  · rintro ⟨h32, h13⟩
    exact ⟨Or.inl h32, Or.inr h32, h13⟩

lemma allHold_constraints_iff_slti
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (Main : Vector (ZMod p) 44) (h : is_slti Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[32] * 9 + Main[33] * 10) #v[Main[34], 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[32] + Main[33]) (Main[32] + Main[33])) ∧
    Main[33] = 0 ∧ Main[13] = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h32, h31⟩ := h
  have h2_lt : (2 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h2_val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2_lt
  have h2_ne : ((1 : ZMod p) + 1) ≠ 0 := by
    intro heq
    have : (2 : ZMod p) = 0 := by linear_combination heq
    rw [this, ZMod.val_zero] at h2_val
    omega
  simp_all [constraints, sub_eq_zero]
  intros
  refine ⟨?_, ?_⟩
  · rintro ⟨h33_bit, h_pair, h13⟩
    refine ⟨?_, h13⟩
    rcases h33_bit with h33 | h33
    · exact h33
    · exfalso
      rcases h_pair with h_pair | h_pair
      · rw [h33] at h_pair; exact h2_ne h_pair
      · rw [h_pair] at h33; exact zero_ne_one h33
  · rintro ⟨h33, h13⟩
    exact ⟨Or.inl h33, Or.inr h33, h13⟩

lemma allHold_constraints_iff_sltiu
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (Main : Vector (ZMod p) 44) (h : is_sltiu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp (LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 (Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[32] * 9 + Main[33] * 10) #v[Main[34], 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[32] + Main[33]) (Main[32] + Main[33])) ∧
    Main[32] = 0 ∧ Main[13] = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h33, h31⟩ := h
  have h2_lt : (2 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h2_val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2_lt
  have h2_ne : ((1 : ZMod p) + 1) ≠ 0 := by
    intro heq
    have : (2 : ZMod p) = 0 := by linear_combination heq
    rw [this, ZMod.val_zero] at h2_val
    omega
  simp_all [constraints, sub_eq_zero]
  intros
  refine ⟨?_, ?_⟩
  · rintro ⟨h32_bit, h_pair, h13⟩
    refine ⟨?_, h13⟩
    rcases h32_bit with h32 | h32
    · exact h32
    · exfalso
      rcases h_pair with h_pair | h_pair
      · rw [h32] at h_pair
        exact h2_ne (by linear_combination h_pair)
      · rw [h_pair] at h32; exact zero_ne_one h32
  · rintro ⟨h32, h13⟩
    exact ⟨Or.inl h32, Or.inr h32, h13⟩

end Lt
