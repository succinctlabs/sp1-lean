import SP1Operations.Operation.MulOperation.MulOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Mul.Constraints

namespace Mul

set_option linter.style.setOption false
set_option linter.style.longLine false

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

/-- From `a = 1` and the four other 5-arm flags `∈ {0,1}` and the sum-disjunction
`Σ = 0 ∨ Σ - 1 = 0`, conclude `Σ = 1`. Mirrors `Bitwise.sum_eq_one_of_eq_one_*`
extended to the 5-arm Mul shape. The `_left` variant assumes `a` (the first
slot) is the active variant. -/
lemma sum_eq_one_of_eq_one_left
    {a b c d e : ZMod p}
    (h_a : a = 1)
    (b_b : b = 0 ∨ b = 1) (b_c : c = 0 ∨ c = 1)
    (b_d : d = 0 ∨ d = 1) (b_e : e = 0 ∨ e = 1)
    (one_of : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1) :
    a + b + c + d + e = 1 := by
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  haveI : NeZero p := ⟨by omega⟩
  have h2lt : (2 : ℕ) < p := by omega
  have h3lt : (3 : ℕ) < p := by omega
  have h4lt : (4 : ℕ) < p := by omega
  have h5lt : (5 : ℕ) < p := by omega
  have h1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h2_val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2lt
  have h3_val : (3 : ZMod p).val = 3 := ZMod.val_natCast_of_lt h3lt
  have h4_val : (4 : ZMod p).val = 4 := ZMod.val_natCast_of_lt h4lt
  have h5_val : (5 : ZMod p).val = 5 := ZMod.val_natCast_of_lt h5lt
  have h1_ne : (1 : ZMod p) ≠ 0 := by
    intro h0; have := congrArg ZMod.val h0; rw [h1_val, ZMod.val_zero] at this; omega
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro h0; have := congrArg ZMod.val h0; rw [h2_val, ZMod.val_zero] at this; omega
  have h3_ne : (3 : ZMod p) ≠ 0 := by
    intro h0; have := congrArg ZMod.val h0; rw [h3_val, ZMod.val_zero] at this; omega
  have h4_ne : (4 : ZMod p) ≠ 0 := by
    intro h0; have := congrArg ZMod.val h0; rw [h4_val, ZMod.val_zero] at this; omega
  have h5_ne : (5 : ZMod p) ≠ 0 := by
    intro h0; have := congrArg ZMod.val h0; rw [h5_val, ZMod.val_zero] at this; omega
  rcases one_of with h | h
  · exfalso
    rcases b_b with rfl | rfl <;> rcases b_c with rfl | rfl <;>
      rcases b_d with rfl | rfl <;> rcases b_e with rfl | rfl <;>
      rw [h_a] at h <;>
      first
        | exact h1_ne (by linear_combination h)
        | exact h2_ne (by linear_combination h)
        | exact h3_ne (by linear_combination h)
        | exact h4_ne (by linear_combination h)
        | exact h5_ne (by linear_combination h)
  · linear_combination h

/-- Mid-position variants of `sum_eq_one_of_eq_one_left`. The active flag occupies the
2nd, 3rd, 4th, or 5th slot of the sum. -/
lemma sum_eq_one_of_eq_one_2
    {a b c d e : ZMod p}
    (h_b : b = 1)
    (b_a : a = 0 ∨ a = 1) (b_c : c = 0 ∨ c = 1)
    (b_d : d = 0 ∨ d = 1) (b_e : e = 0 ∨ e = 1)
    (one_of : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1) :
    a + b + c + d + e = 1 := by
  have heq : b + a + c + d + e = 1 := sum_eq_one_of_eq_one_left h_b b_a b_c b_d b_e
    (by rcases one_of with h | h
        · left; linear_combination h
        · right; linear_combination h)
  linear_combination heq

lemma sum_eq_one_of_eq_one_3
    {a b c d e : ZMod p}
    (h_c : c = 1)
    (b_a : a = 0 ∨ a = 1) (b_b : b = 0 ∨ b = 1)
    (b_d : d = 0 ∨ d = 1) (b_e : e = 0 ∨ e = 1)
    (one_of : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1) :
    a + b + c + d + e = 1 := by
  have heq : c + a + b + d + e = 1 := sum_eq_one_of_eq_one_left h_c b_a b_b b_d b_e
    (by rcases one_of with h | h
        · left; linear_combination h
        · right; linear_combination h)
  linear_combination heq

lemma sum_eq_one_of_eq_one_4
    {a b c d e : ZMod p}
    (h_d : d = 1)
    (b_a : a = 0 ∨ a = 1) (b_b : b = 0 ∨ b = 1)
    (b_c : c = 0 ∨ c = 1) (b_e : e = 0 ∨ e = 1)
    (one_of : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1) :
    a + b + c + d + e = 1 := by
  have heq : d + a + b + c + e = 1 := sum_eq_one_of_eq_one_left h_d b_a b_b b_c b_e
    (by rcases one_of with h | h
        · left; linear_combination h
        · right; linear_combination h)
  linear_combination heq

lemma sum_eq_one_of_eq_one_5
    {a b c d e : ZMod p}
    (h_e : e = 1)
    (b_a : a = 0 ∨ a = 1) (b_b : b = 0 ∨ b = 1)
    (b_c : c = 0 ∨ c = 1) (b_d : d = 0 ∨ d = 1)
    (one_of : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1) :
    a + b + c + d + e = 1 := by
  have heq : e + a + b + c + d = 1 := sum_eq_one_of_eq_one_left h_e b_a b_b b_c b_d
    (by rcases one_of with h | h
        · left; linear_combination h
        · right; linear_combination h)
  linear_combination heq

set_option maxHeartbeats 4000000 in
-- Polymorphic mirror of `single_op` (line 118): from the chip-level constraints,
-- only one of `Main[77..81]` can be `1`. Mirrors the KB proof pattern but
-- destructures the constraint list directly via simp+List.forall_append rather
-- than going through a chip-level `iff` lemma. Note constraint compiler
-- emits the boolean assertions in the order `77, 78, 79, 81, 80` (mulw before
-- mulhsu), matching the existing KB iff at line 100-105.
lemma single_op (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold (constraints Main)) :
    (Main[77] = 1 → Main[78] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0) ∧
    (Main[78] = 1 → Main[77] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0) ∧
    (Main[79] = 1 → Main[77] = 0 ∧ Main[78] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0) ∧
    (Main[80] = 1 → Main[77] = 0 ∧ Main[78] = 0 ∧ Main[79] = 0 ∧ Main[81] = 0) ∧
    (Main[81] = 1 → Main[77] = 0 ∧ Main[78] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0) := by
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨_h_mop, _h_cpu⟩, _h_alu⟩, b_77, b_78, b_79, b_81, b_80, sum_disj, _h_M13⟩ := cstrs
  -- Map Main[77..81] to is_mul/is_mulh/is_mulhu/is_mulhsu/is_mulw and apply
  -- MulOperation.single_op. Note the slot mapping per the constraint
  -- compiler: 77=mul, 78=mulh, 79=mulhu, 80=mulhsu, 81=mulw.
  have h_77 := fun h_77_one => sum_eq_one_of_eq_one_left h_77_one b_78 b_79 b_80 b_81 sum_disj
  have h_78 := fun h_78_one => sum_eq_one_of_eq_one_2 h_78_one b_77 b_79 b_80 b_81 sum_disj
  have h_79 := fun h_79_one => sum_eq_one_of_eq_one_3 h_79_one b_77 b_78 b_80 b_81 sum_disj
  have h_80 := fun h_80_one => sum_eq_one_of_eq_one_4 h_80_one b_77 b_78 b_79 b_81 sum_disj
  have h_81 := fun h_81_one => sum_eq_one_of_eq_one_5 h_81_one b_77 b_78 b_79 b_80 sum_disj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h_one
  · have h_sum : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := h_77 h_one
    have ⟨h78, h81, h79, h80⟩ :=
      (MulOperation.single_op b_77 b_78 b_79 b_80 b_81 h_sum).1 h_one
    exact ⟨h78, h79, h80, h81⟩
  · have h_sum : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := h_78 h_one
    have ⟨h77, h81, h79, h80⟩ :=
      (MulOperation.single_op b_77 b_78 b_79 b_80 b_81 h_sum).2.1 h_one
    exact ⟨h77, h79, h80, h81⟩
  · have h_sum : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := h_79 h_one
    have ⟨h77, h78, h81, h80⟩ :=
      (MulOperation.single_op b_77 b_78 b_79 b_80 b_81 h_sum).2.2.2.1 h_one
    exact ⟨h77, h78, h80, h81⟩
  · have h_sum : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := h_80 h_one
    have ⟨h77, h78, h81, h79⟩ :=
      (MulOperation.single_op b_77 b_78 b_79 b_80 b_81 h_sum).2.2.2.2 h_one
    exact ⟨h77, h78, h79, h81⟩
  · have h_sum : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := h_81 h_one
    have ⟨h77, h78, h79, h80⟩ :=
      (MulOperation.single_op b_77 b_78 b_79 b_80 b_81 h_sum).2.2.1 h_one
    exact ⟨h77, h78, h79, h80⟩


set_option maxHeartbeats 4000000 in
-- Polymorphic mirror of `ops_U64_b_c` (line 176): both `b` and `c` operands
-- are 64-bit values. Uses `RTypeReader.allHold_constraints_iff_is_real`
-- after extracting the ALU sub-constraints from `cstrs`. Takes the
-- specialized `is_real = 1` (sum of the 5 variant flags = 1) as input,
-- since deriving it requires the boolean disjunctions which the chip-level
-- `correct_*` proofs extract once via `sum_eq_one_of_eq_one_*`.
lemma ops_U64_b_c (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_is_real_eq_one :
      Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1) :
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨_h_mop, _h_cpu⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real_eq_one h_is_real_eq_one] at h_alu
  obtain ⟨_, _, _, _, _, _, _, h_complex, _⟩ := h_alu
  obtain ⟨_, _, _, h_isU64_b, h_isU64_c⟩ := h_complex
  exact ⟨h_isU64_b, h_isU64_c⟩

/-- Derive `Main[77] + ... + Main[81] = 1` from cstrs + `Main[77] = 1`.
Used by chip-level `correct_mul` so that downstream helpers
(`ops_U64_b_c`, `register_bounds`) can be invoked with raw
cstrs + this single derived fact. -/
lemma is_real_eq_one_of_mul (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_77 : Main[77] = 1) :
    Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := by
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨_, _b_77, b_78, b_79, b_81, b_80, sum_disj, _⟩ := cstrs
  exact sum_eq_one_of_eq_one_left h_77 b_78 b_79 b_80 b_81 sum_disj

lemma is_real_eq_one_of_mulh (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_78 : Main[78] = 1) :
    Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := by
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨_, b_77, _b_78, b_79, b_81, b_80, sum_disj, _⟩ := cstrs
  exact sum_eq_one_of_eq_one_2 h_78 b_77 b_79 b_80 b_81 sum_disj

lemma is_real_eq_one_of_mulhu (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_79 : Main[79] = 1) :
    Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := by
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨_, b_77, b_78, _b_79, b_81, b_80, sum_disj, _⟩ := cstrs
  exact sum_eq_one_of_eq_one_3 h_79 b_77 b_78 b_80 b_81 sum_disj

lemma is_real_eq_one_of_mulhsu (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_80 : Main[80] = 1) :
    Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := by
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨_, b_77, b_78, b_79, b_81, _b_80, sum_disj, _⟩ := cstrs
  exact sum_eq_one_of_eq_one_4 h_80 b_77 b_78 b_79 b_81 sum_disj

lemma is_real_eq_one_of_mulw (Main : Vector (ZMod p) 82)
    (cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_81 : Main[81] = 1) :
    Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1 := by
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨_, b_77, b_78, b_79, _b_81, b_80, sum_disj, _⟩ := cstrs
  exact sum_eq_one_of_eq_one_5 h_81 b_77 b_78 b_79 b_80 sum_disj


end Mul
