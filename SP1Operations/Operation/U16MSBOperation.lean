import SP1Foundations
import SP1Operations.Operation.U16MSBOperation.Operation
import SP1Operations.Operation.U16MSBOperation.Constraints

namespace U16MSBOperation

/-- The `Range` constraint emits a `.val < 65536` shape via
`SP1Constraint.toProp`, so this iff states the bound at the `ℕ`
level rather than the field level. -/
lemma allHold_constraints_iff_poly {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    [Fact (2 ^ 17 < p)]
  {a : ZMod p}
  {cols : U16MSBOperation (ZMod p)}
  {is_real : ZMod p} :
  List.Forall SP1Constraint.toProp (constraints a cols is_real) ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (cols.msb = 0 ∨ cols.msb = 1) ∧
    (¬is_real = 0 → (2 * a - cols.msb * 65536).val < 65536)
  := by simp [constraints]; grind

set_option maxHeartbeats 4000000 in
-- Case-splits on `cols.msb ∈ {0, 1}` and uses `val_sub_cases` for the
-- wrap-around in `(2 * a - 65536).val`.
lemma spec_poly
  {p : ℕ} [Fact (Nat.Prime p)] [hp17 : Fact (2 ^ 17 < p)]
  {a : ZMod p}
  {cols : U16MSBOperation (ZMod p)}
  (h_a_isU16 : a.val < 65536) :
  List.Forall SP1Constraint.toProp (constraints a cols 1) →
    cols.msb = if a.val ≥ 32768 then 1 else 0 := by
  have hp_lt : 2 ^ 17 < p := hp17.out
  have hp_neZero : NeZero p := ⟨by omega⟩
  have h2_val : (2 : ZMod p).val = 2 := val_2_zmod_p
  have h65536_val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h_2a_val : (2 * a).val = 2 * a.val := by
    rw [ZMod.val_mul_of_lt (by rw [h2_val]; omega), h2_val]
  intro h
  rw [allHold_constraints_iff_poly] at h
  obtain ⟨_, hbit, hrange⟩ := h
  specialize hrange one_ne_zero
  rcases hbit with hbit | hbit
  · simp [hbit] at hrange
    rw [h_2a_val] at hrange
    rw [hbit]
    split_ifs with h32k
    · omega
    · rfl
  · simp [hbit] at hrange
    rw [hbit]
    split_ifs with h32k
    · rfl
    · exfalso
      have hlt : a.val < 32768 := by omega
      have h_sub_val : (2 * a - 65536).val = p - (65536 - 2 * a.val) := by
        rw [val_sub_cases, h_2a_val, h65536_val, if_neg (by omega)]
      omega

lemma spec.U64_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {w : Word (ZMod p)}
  {cols : U16MSBOperation (ZMod p)}
  (h_w_isU64 : w.isU64_poly) :
  List.Forall SP1Constraint.toProp (constraints w[3] cols 1) →
    cols.msb = if w.isNegative_poly then 1 else 0 := by
  intro h
  have h_w3_lt : w[3].val < 65536 := h_w_isU64 3
  have := spec_poly h_w3_lt h
  simp [Word.isNegative_poly]
  exact this

section gen

lemma spec.gen_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {a : ZMod p}
  {cols : U16MSBOperation (ZMod p)}
  {is_real : ZMod p}
  (h_a_isU16 : a.val < 65536) :
  List.Forall SP1Constraint.toProp (constraints a cols is_real) →
    is_real = 1 →
      cols.msb = if a.val ≥ 32768 then 1 else 0 := by
  intros h hir
  subst hir
  exact spec_poly h_a_isU16 h

end gen

end U16MSBOperation
