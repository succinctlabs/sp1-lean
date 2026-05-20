import SP1Operations.Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace Bitwise

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

-- Generated Lean code for chip BitwiseChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 51) : SP1ConstraintList F :=
  let E0 : F := Main[48] + Main[49]
  let E1 : F := E0 + Main[50]
  let E2 : F := Main[48] - 1
  let E3 : F := Main[48] * E2
  let E4 : F := Main[49] - 1
  let E5 : F := Main[49] * E4
  let E6 : F := Main[50] - 1
  let E7 : F := Main[50] * E6
  let E8 : F := E1 - 1
  let E9 : F := E1 * E8
  let E10 : F := Main[48] * 2
  let E11 : F := Main[49] * 1
  let E12 : F := E10 + E11
  let E13 : F := Main[50] * 0
  let E14 : F := E12 + E13
  let E15 : F := Main[48] * 3
  let E16 : F := Main[49] * 4
  let E17 : F := E15 + E16
  let E18 : F := Main[50] * 5
  let E19 : F := E17 + E18
  let E20 : F := Main[48] * 4
  let E21 : F := Main[49] * 6
  let E22 : F := E20 + E21
  let E23 : F := Main[50] * 7
  let E24 : F := E22 + E23
  let E25 : F := Main[48] * 0
  let E26 : F := Main[49] * 0
  let E27 : F := E25 + E26
  let E28 : F := Main[50] * 0
  let E29 : F := E27 + E28
  let E30 : F := Main[48] * 51
  let E31 : F := Main[49] * 51
  let E32 : F := E30 + E31
  let E33 : F := Main[50] * 51
  let E34 : F := E32 + E33
  let E35 : F := 32 * Main[31]
  let E36 : F := E34 - E35
  let E37 : F := Main[48] * 8
  let E38 : F := Main[49] * 8
  let E39 : F := E37 + E38
  let E40 : F := Main[50] * 8
  let E41 : F := E39 + E40
  let E42 : F := 4 * Main[31]
  let E43 : F := E41 - E42
  let ⟨⟨⟨[E44, E45, E46, E47]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { b_low_bytes := { low_bytes := #v[Main[32], Main[33], Main[34], Main[35]] }, c_low_bytes := { low_bytes := #v[Main[36], Main[37], Main[38], Main[39]] }, bitwise_operation := { result := #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]] } } E14 E1
  let E48 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E48, Main[4], Main[5]] 8 E1
  let E49 : F := Main[1] * 65536
  let E50 : F := Main[2] + E49
  let CS2 : SP1ConstraintList F := ALUTypeReader.constraints Main[0] E50 #v[Main[3], Main[4], Main[5]] E19 #v[E44, E45, E46, E47] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E1 E1
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero Main[13]),
  ]

end constraints

section poly_helpers

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

@[simp] def is_real (Main : Vector (ZMod p) 51) : Prop :=
  Main[48] = 1 ∨ Main[49] = 1 ∨ Main[50] = 1

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

@[simp] def is_xor (Main : Vector (ZMod p) 51) := Main[48] = 1 ∧ Main[31] = 0
@[simp] def is_xori (Main : Vector (ZMod p) 51) := Main[48] = 1 ∧ Main[31] = 1
@[simp] def is_or (Main : Vector (ZMod p) 51) := Main[49] = 1 ∧ Main[31] = 0
@[simp] def is_ori (Main : Vector (ZMod p) 51) := Main[49] = 1 ∧ Main[31] = 1
@[simp] def is_and (Main : Vector (ZMod p) 51) := Main[50] = 1 ∧ Main[31] = 0
@[simp] def is_andi (Main : Vector (ZMod p) 51) := Main[50] = 1 ∧ Main[31] = 1

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 800000 in
-- Mirror of `allHold_constraints_iff` over `ZMod p` via `` predicates.
-- Closes via the same `simp` recipe; budget elevated for the BitwiseU16Operation
-- expansion plus 51-column constraint body.
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

end poly_helpers

end Bitwise
