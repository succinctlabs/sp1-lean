import SP1Operations.Operation.BitwiseU16Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.Bitwise.Constraints

namespace Bitwise

set_option linter.style.setOption false
set_option linter.style.longLine false

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

/-- From `a = 1` and `b, c ∈ {0,1}` with `a + b + c ∈ {0, 1}`, conclude
`a + b + c = 1`. Used by chip arms to derive `is_real = 1` from the variant
hypothesis plus the iff's bool/sum disjunctions. -/
lemma sum_eq_one_of_eq_one_left
    {a b c : ZMod p}
    (h_a : a = 1)
    (b_b : b = 0 ∨ b = 1) (b_c : c = 0 ∨ c = 1)
    (one_of : a + b + c = 0 ∨ a + b + c - 1 = 0) :
    a + b + c = 1 := by
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h2lt : (2 : ℕ) < p := by omega
  have h3lt : (3 : ℕ) < p := by omega
  have : NeZero p := ⟨by omega⟩
  have h1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h2_val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2lt
  have h3_val : (3 : ZMod p).val = 3 := ZMod.val_natCast_of_lt h3lt
  rcases one_of with h | h
  · exfalso
    rcases b_b with hb | hb <;> rcases b_c with hc | hc <;>
      rw [h_a, hb, hc] at h
    · -- 1 + 0 + 0 = 0 → 1 = 0
      have h1 : (1 : ZMod p) = 0 := by linear_combination h
      have : ((1 : ZMod p)).val = 0 := by rw [h1, ZMod.val_zero]
      omega
    · -- 1 + 0 + 1 = 0 → 2 = 0
      have h2 : (2 : ZMod p) = 0 := by linear_combination h
      have : ((2 : ZMod p)).val = 0 := by rw [h2, ZMod.val_zero]
      omega
    · -- 1 + 1 + 0 = 0 → 2 = 0
      have h2 : (2 : ZMod p) = 0 := by linear_combination h
      have : ((2 : ZMod p)).val = 0 := by rw [h2, ZMod.val_zero]
      omega
    · -- 1 + 1 + 1 = 0 → 3 = 0
      have h3 : (3 : ZMod p) = 0 := by linear_combination h
      have : ((3 : ZMod p)).val = 0 := by rw [h3, ZMod.val_zero]
      omega
  · linear_combination h

/-- Variant of `sum_eq_one_of_eq_one_left` with the `1`-valued column in the middle position. -/
lemma sum_eq_one_of_eq_one_mid
    {a b c : ZMod p}
    (h_b : b = 1)
    (b_a : a = 0 ∨ a = 1) (b_c : c = 0 ∨ c = 1)
    (one_of : a + b + c = 0 ∨ a + b + c - 1 = 0) :
    a + b + c = 1 := by
  have heq : b + a + c = 1 := sum_eq_one_of_eq_one_left h_b b_a b_c
    (by rcases one_of with h | h
        · left; linear_combination h
        · right; linear_combination h)
  linear_combination heq

/-- Variant of `sum_eq_one_of_eq_one_left` with the `1`-valued column in the right position. -/
lemma sum_eq_one_of_eq_one_right
    {a b c : ZMod p}
    (h_c : c = 1)
    (b_a : a = 0 ∨ a = 1) (b_b : b = 0 ∨ b = 1)
    (one_of : a + b + c = 0 ∨ a + b + c - 1 = 0) :
    a + b + c = 1 := by
  have heq : c + a + b = 1 := sum_eq_one_of_eq_one_left h_c b_a b_b
    (by rcases one_of with h | h
        · left; linear_combination h
        · right; linear_combination h)
  linear_combination heq

/-- Mutual exclusion: from the `b ∈ {0,1}` disjunctions plus `is_real = 1`,
the three opcode columns are mutually exclusive (only one can be `1`). -/
lemma single_op (Main : Vector (ZMod p) 51)
    (b_xor : Main[48] = 0 ∨ Main[48] = 1)
    (b_or : Main[49] = 0 ∨ Main[49] = 1)
    (b_and : Main[50] = 0 ∨ Main[50] = 1)
    (h_sum : Main[48] + Main[49] + Main[50] = 1) :
    (Main[48] = 1 → Main[49] = 0 ∧ Main[50] = 0) ∧
    (Main[49] = 1 → Main[48] = 0 ∧ Main[50] = 0) ∧
    (Main[50] = 1 → Main[48] = 0 ∧ Main[49] = 0) := by
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h2lt : (2 : ℕ) < p := by omega
  have h3lt : (3 : ℕ) < p := by omega
  have : NeZero p := ⟨by omega⟩
  have h1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h2_val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2lt
  have h3_val : (3 : ZMod p).val = 3 := ZMod.val_natCast_of_lt h3lt
  -- Each "x = 1 ∧ y = 1" case forces sum = 2 or 3, contradicting sum = 1.
  have h_sum_inj :
      ∀ (x y z : ZMod p), x + y + z = 1 → x + y + z ≠ 2 ∧ x + y + z ≠ 3 := by
    intro x y z h
    refine ⟨?_, ?_⟩ <;> intro hh <;> rw [h] at hh
    · have : ((1 : ZMod p)).val = (2 : ZMod p).val := congrArg ZMod.val hh
      omega
    · have : ((1 : ZMod p)).val = (3 : ZMod p).val := congrArg ZMod.val hh
      omega
  refine ⟨?_, ?_, ?_⟩ <;> intro h_X
  all_goals
    refine ⟨?_, ?_⟩
  -- Main[48] = 1 cases
  · rcases b_or with h | h; · exact h
    rcases b_and with h' | h'
    · exfalso; exact (h_sum_inj _ _ _ h_sum).1 (by linear_combination h_X + h + h')
    · exfalso; exact (h_sum_inj _ _ _ h_sum).2 (by linear_combination h_X + h + h')
  · rcases b_and with h | h; · exact h
    rcases b_or with h' | h'
    · exfalso; exact (h_sum_inj _ _ _ h_sum).1 (by linear_combination h_X + h' + h)
    · exfalso; exact (h_sum_inj _ _ _ h_sum).2 (by linear_combination h_X + h' + h)
  -- Main[49] = 1 cases
  · rcases b_xor with h | h; · exact h
    rcases b_and with h' | h'
    · exfalso; exact (h_sum_inj _ _ _ h_sum).1 (by linear_combination h + h_X + h')
    · exfalso; exact (h_sum_inj _ _ _ h_sum).2 (by linear_combination h + h_X + h')
  · rcases b_and with h | h; · exact h
    rcases b_xor with h' | h'
    · exfalso; exact (h_sum_inj _ _ _ h_sum).1 (by linear_combination h' + h_X + h)
    · exfalso; exact (h_sum_inj _ _ _ h_sum).2 (by linear_combination h' + h_X + h)
  -- Main[50] = 1 cases
  · rcases b_xor with h | h; · exact h
    rcases b_or with h' | h'
    · exfalso; exact (h_sum_inj _ _ _ h_sum).1 (by linear_combination h + h' + h_X)
    · exfalso; exact (h_sum_inj _ _ _ h_sum).2 (by linear_combination h + h' + h_X)
  · rcases b_or with h | h; · exact h
    rcases b_xor with h' | h'
    · exfalso; exact (h_sum_inj _ _ _ h_sum).1 (by linear_combination h' + h + h_X)
    · exfalso; exact (h_sum_inj _ _ _ h_sum).2 (by linear_combination h' + h + h_X)

set_option linter.unusedSectionVars false in
-- Mirror of `allHold_constraints_iff` over `ZMod p` via `` predicates.
-- Closes via the same `simp` recipe.
lemma allHold_constraints_iff (Main : Vector (ZMod p) 51) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    let ret_val := (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).1
    List.Forall SP1Constraint.toProp (BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } (Main[48] * 2 + Main[49] * 1 + Main[50] * 0) (Main[48] + Main[49] + Main[50])).2 ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[(Main[3] + 4), Main[4], Main[5]] 8 (Main[48] + Main[49] + Main[50])) ∧
    List.Forall SP1Constraint.toProp (ALUTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] (Main[48] * 3 + Main[49] * 4 + Main[50] * 5)
      #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } (Main[48] + Main[49] + Main[50]) (Main[48] + Main[49] + Main[50])) ∧
    (Main[48] = 0 ∨ Main[48] = 1) ∧
    (Main[49] = 0 ∨ Main[49] = 1) ∧
    (Main[50] = 0 ∨ Main[50] = 1) ∧
    (Main[48] + Main[49] + Main[50] = 0 ∨ Main[48] + Main[49] + Main[50] - 1 = 0) ∧
    Main[13] = 0 := by
  simp [and_assoc, constraints, BitwiseU16Operation.constraints,
    U16toU8OperationUnsafe.constraints, sub_eq_zero]

end Bitwise
