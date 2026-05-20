import SP1Operations.Compare.U16CompareOperation.Operation
import SP1Operations.Compare.U16CompareOperation.Constraints

namespace U16CompareOperation

set_option maxHeartbeats 4000000 in
-- Case-splits on `cols.bit ∈ {0, 1}` and uses `val_sub_cases` from
-- `Field.lean` to handle `(a - b).val` (the wrap-around branch is
-- impossible when `a.val, b.val < 65536` and `p > 2^17`). The
-- `cols.bit = 1` case uses `ZMod.val_add_of_lt` to compute
-- `(a - b + 65536).val`.
lemma spec_poly
  {p : ℕ} [Fact (Nat.Prime p)] [hp17 : Fact (2 ^ 17 < p)]
  (a b : ZMod p)
  (cols : U16CompareOperation (ZMod p))
  (h_a_isU16 : a.val < 65536)
  (h_b_isU16 : b.val < 65536) :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    (cols.bit = if a.val < b.val then 1 else 0)
  := by
  have hp_lt : 2 ^ 17 < p := hp17.out
  have hp_neZero : NeZero p := ⟨by omega⟩
  have h65536_val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  simp [constraints, SP1Constraint.toProp, sub_eq_zero, mul_eq_zero]
  intro hbit hrange
  rcases hbit with hbit | hbit
  · simp [hbit] at hrange ⊢
    rw [val_sub_cases] at hrange
    split_ifs at hrange with hba
    · exact hba
    · omega
  · simp [hbit] at hrange ⊢
    by_cases hba : a.val < b.val
    · exact hba
    · exfalso
      have hba' : b.val ≤ a.val := Nat.le_of_not_lt hba
      have h_ab : (a - b).val = a.val - b.val := by
        rw [val_sub_cases, if_pos hba']
      have h_add : (a - b + 65536).val = (a - b).val + 65536 := by
        rw [ZMod.val_add_of_lt, h65536_val]
        rw [h65536_val]; omega
      omega

end U16CompareOperation
