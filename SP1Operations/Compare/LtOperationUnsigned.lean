import SP1Operations.Compare.LtOperationUnsigned.Constraints

namespace LtOperationUnsigned

set_option linter.style.setOption false
set_option linter.style.longLine false

lemma allHold_constraints_iff_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (b : Word (ZMod p))
  (d : Word (ZMod p))
  (cols : LtOperationUnsigned (ZMod p))
  (is_real : ZMod p) :
  List.Forall SP1Constraint.toProp (constraints b d cols is_real) ↔
    List.Forall SP1Constraint.toProp (U16CompareOperation.constraints cols.comparison_limbs[0] cols.comparison_limbs[1] cols.u16_compare_operation is_real) ∧
    ((is_real = 0 ∨ is_real = 1) ∧
    (cols.u16_flags[0] = 0 ∨ cols.u16_flags[0] = 1) ∧
    (cols.u16_flags[1] = 0 ∨ cols.u16_flags[1] = 1) ∧
    (cols.u16_flags[2] = 0 ∨ cols.u16_flags[2] = 1) ∧
    (cols.u16_flags[3] = 0 ∨ cols.u16_flags[3] = 1) ∧
    (cols.u16_flags[0] + cols.u16_flags[1] + cols.u16_flags[2] + cols.u16_flags[3] = 0 ∨ cols.u16_flags[0] + cols.u16_flags[1] + cols.u16_flags[2] + cols.u16_flags[3] = 1) ∧
    (is_real = cols.u16_flags[3] ∨ b[3] = d[3]) ∧
    (is_real = cols.u16_flags[3] + cols.u16_flags[2] ∨ b[2] = d[2]) ∧
    (is_real = cols.u16_flags[3] + cols.u16_flags[2] + cols.u16_flags[1] ∨ b[1] = d[1]) ∧
    (is_real = cols.u16_flags[3] + cols.u16_flags[2] + cols.u16_flags[1] + cols.u16_flags[0] ∨ b[0] = d[0]) ∧
    b[3] * cols.u16_flags[3] + b[2] * cols.u16_flags[2] + b[1] * cols.u16_flags[1] + b[0] * cols.u16_flags[0] = cols.comparison_limbs[0] ∧
    d[3] * cols.u16_flags[3] + d[2] * cols.u16_flags[2] + d[1] * cols.u16_flags[1] + d[0] * cols.u16_flags[0] = cols.comparison_limbs[1] ∧
    (-cols.u16_flags[3] + (-cols.u16_flags[2] + (-cols.u16_flags[1] + -cols.u16_flags[0])) = 0 ∨ cols.not_eq_inv * (cols.comparison_limbs[0] - cols.comparison_limbs[1]) = is_real))
  := by
    simp [and_assoc, constraints, sub_eq_zero, SP1Constraint.toProp]

set_option maxHeartbeats 8000000 in
-- 16-way case split on the 4 boolean flags. The "sum ≤ 1" constraint
-- (`h_sum`) discards 14 of 16 cases (those with 2+ flags = 1) via
-- field-level contradictions. The 2 remaining valid cases (0 flags or
-- exactly 1 flag) close by rewriting `cols.comparison_limbs[i]` via
-- `← h_e0` / `← h_e1` and using the `isU64_poly` bounds.
@[grind →]
lemma cl_are_U16_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b : Word (ZMod p)}
  {d : Word (ZMod p)}
  {cols : LtOperationUnsigned (ZMod p)}
  {is_real : ZMod p}
  (h_b_isU64 : Word.isU64_poly b)
  (h_d_isU64 : Word.isU64_poly d) :
  List.Forall SP1Constraint.toProp (constraints b d cols is_real) →
    is_real = 1 →
      cols.comparison_limbs[0].val < 65536 ∧ cols.comparison_limbs[1].val < 65536
  := by
    intro cstrs his
    rw [allHold_constraints_iff_poly] at cstrs
    rcases cstrs with
      ⟨_, _, h_f0, h_f1, h_f2, h_f3, h_sum, _, _, _, _, h_e0, h_e1, _⟩
    obtain ⟨h_b0, h_b1, h_b2, h_b3⟩ := Word.lt_cases_of_isU64_poly h_b_isU64
    obtain ⟨h_d0, h_d1, h_d2, h_d3⟩ := Word.lt_cases_of_isU64_poly h_d_isU64
    rcases h_f0 with hf0 | hf0 <;> rcases h_f1 with hf1 | hf1 <;>
      rcases h_f2 with hf2 | hf2 <;> rcases h_f3 with hf3 | hf3 <;>
      rcases h_sum with h_sum | h_sum <;>
      rw [hf0, hf1, hf2, hf3] at h_e0 h_e1 h_sum <;>
      simp only [zero_mul, one_mul, mul_zero, mul_one, zero_add, add_zero] at h_e0 h_e1
    all_goals first
      | (exfalso
         have h4 : (4 : ZMod p) = 0 := by linear_combination h_sum
         exact val_4_ne_zero h4)
      | (exfalso
         have h3 : (3 : ZMod p) = 0 := by linear_combination h_sum
         exact val_3_ne_zero h3)
      | (exfalso
         have h2 : (2 : ZMod p) = 0 := by linear_combination h_sum
         exact val_2_ne_zero h2)
      | (exfalso
         have h1 : (1 : ZMod p) = 0 := by linear_combination h_sum
         exact one_ne_zero h1)
      | (constructor <;>
         first
           | (rw [← h_e0]; omega)
           | (rw [← h_e1]; omega)
           | (rw [← h_e0]; simp)
           | (rw [← h_e1]; simp))

/-- Helper: `not_eq_inv * (a - b) = 1` implies `a.val ≠ b.val`. Used in
the `_poly` cascade to bridge field-level inequality (encoded by the
`not_eq_inv` constraint) to Nat-level inequality (which `omega` /
`grind` can use for limb-comparison reasoning). -/
private lemma val_ne_of_inv_mul_eq {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    {a b inv : ZMod p} (h : inv * (a - b) = 1) : a.val ≠ b.val := by
  intro hval
  have hab : a = b := ZMod.val_injective _ hval
  rw [hab, sub_self, mul_zero] at h
  exact zero_ne_one h

set_option maxHeartbeats 64000000 in
-- Heartbeats elevated for the 32-way case split (16 flag combos × 2
-- sum-disjuncts × 2 inv-disjuncts). The proof structure: discharge
-- impossible flag-sum cases via `val_k_ne_zero` (sum=2,3,4); for valid
-- cases (sum=0 or sum=1), split on the `not_eq_inv` constraint
-- disjunction; use `grind` with an optional `h_neq` hint from
-- `val_ne_of_inv_mul_eq` to close.
@[grind →, aesop safe forward]
lemma spec.nat_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b d : Word (ZMod p)}
  {cols : LtOperationUnsigned (ZMod p)}
  (h_b_isU64 : Word.isU64_poly b)
  (h_d_isU64 : Word.isU64_poly d) :
  List.Forall SP1Constraint.toProp (constraints b d cols 1) →
    cols.u16_compare_operation.bit =
      if b.toNat_poly < d.toNat_poly then (1 : ZMod p) else (0 : ZMod p)
  := by
    intro cstrs
    have ⟨h_cl0, h_cl1⟩ := cl_are_U16_poly h_b_isU64 h_d_isU64 cstrs (by rfl)
    rw [allHold_constraints_iff_poly] at cstrs
    rcases cstrs with ⟨h_comp_limbs, _, h_flag_0_bool, h_flag_1_bool,
      h_flag_2_bool, h_flag_3_bool, h_sum, h_eq3, h_eq2, h_eq1, h_eq0,
      h_e0, h_e1, h_inv⟩
    have h_bit := U16CompareOperation.spec_poly _ _
      cols.u16_compare_operation h_cl0 h_cl1 h_comp_limbs
    obtain ⟨h_b0, h_b1, h_b2, h_b3⟩ := Word.lt_cases_of_isU64_poly h_b_isU64
    obtain ⟨h_d0, h_d1, h_d2, h_d3⟩ := Word.lt_cases_of_isU64_poly h_d_isU64
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    unfold Word.toNat_poly
    rcases h_flag_0_bool with hf0 | hf0 <;>
      rcases h_flag_1_bool with hf1 | hf1 <;>
      rcases h_flag_2_bool with hf2 | hf2 <;>
      rcases h_flag_3_bool with hf3 | hf3 <;>
      rcases h_sum with h_sum | h_sum <;>
      rw [hf0, hf1, hf2, hf3] at h_e0 h_e1 h_sum h_inv <;>
      simp only [zero_mul, one_mul, mul_zero, mul_one, zero_add, add_zero,
                 neg_zero, neg_neg] at h_e0 h_e1 h_inv
    all_goals first
      | (exfalso
         have h4 : (4 : ZMod p) = 0 := by linear_combination h_sum
         exact val_4_ne_zero h4)
      | (exfalso
         have h3 : (3 : ZMod p) = 0 := by linear_combination h_sum
         exact val_3_ne_zero h3)
      | (exfalso
         have h2 : (2 : ZMod p) = 0 := by linear_combination h_sum
         exact val_2_ne_zero h2)
      | skip
    all_goals rcases h_inv with h_inv | h_inv
    all_goals first
      | grind
      | (have h_neq := val_ne_of_inv_mul_eq h_inv; grind)

/-- BitVec form. Bridges `spec.nat_poly` to the BitVec form via
`execute_RTYPE_pure_w_poly`'s SLTU arm. -/
lemma spec_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b d : Word (ZMod p)}
  {cols : LtOperationUnsigned (ZMod p)}
  (h_b_isU64 : Word.isU64_poly b)
  (h_d_isU64 : Word.isU64_poly d) :
  List.Forall SP1Constraint.toProp (constraints b d cols 1) →
    BitVec.ofNat 64 cols.u16_compare_operation.bit.val = execute_RTYPE_pure_w_poly b d .SLTU
  := by
    intro cstrs
    have h := spec.nat_poly h_b_isU64 h_d_isU64 cstrs
    simp only [execute_RTYPE_pure_w_poly]
    rw [h]
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    split_ifs <;> simp [ZMod.val_one, ZMod.val_zero]

section gen

lemma spec.nat.gen_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b d : Word (ZMod p)}
  {cols : LtOperationUnsigned (ZMod p)}
  {is_real : ZMod p}
  (h_b_isU64 : Word.isU64_poly b)
  (h_d_isU64 : Word.isU64_poly d) :
  List.Forall SP1Constraint.toProp (constraints b d cols is_real) →
    is_real = 1 →
      cols.u16_compare_operation.bit =
        if b.toNat_poly < d.toNat_poly then (1 : ZMod p) else (0 : ZMod p)
  := by
    intro cstrs h_is_real
    subst h_is_real
    exact spec.nat_poly h_b_isU64 h_d_isU64 cstrs

end gen

end LtOperationUnsigned
