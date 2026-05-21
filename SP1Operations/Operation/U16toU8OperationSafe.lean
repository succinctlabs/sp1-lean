import SP1Operations.Operation.U16toU8OperationUnsafe
import SP1Operations.Operation.U16toU8OperationSafe.Operation
import SP1Operations.Operation.U16toU8OperationSafe.Constraints

namespace U16toU8OperationSafe

set_option linter.style.setOption false
set_option linter.style.longLine false

/-- The auto-gen U8Range opcode produces field-level `<` (per the B.8
finding on `constrain_U8Range`); the proof needs an explicit
`(0 : ZMod p) < (256 : ZMod p)` hypothesis. -/
lemma allHold_constraints_iff
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (u16_values : (Vector (ZMod p) 4))
  (cols : U16toU8Operation (ZMod p))
  (is_real : ZMod p) :
  List.Forall SP1Constraint.toProp (constraints u16_values cols is_real).2 ↔
    (¬is_real = 0 → cols.low_bytes[0] < 256 ∧ ((u16_values[0] - cols.low_bytes[0]) * (256 : ZMod p)⁻¹) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[1] < 256 ∧ ((u16_values[1] - cols.low_bytes[1]) * (256 : ZMod p)⁻¹) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[2] < 256 ∧ ((u16_values[2] - cols.low_bytes[2]) * (256 : ZMod p)⁻¹) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[3] < 256 ∧ ((u16_values[3] - cols.low_bytes[3]) * (256 : ZMod p)⁻¹) < 256)
  := by
  have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
    change (0 : ZMod p).val < (256 : ZMod p).val; simp
  simp [constraints, SP1Constraint.toProp, h0_lt_256]

/-- Given the two `< 256` bounds (low byte and high byte after dividing
by `256⁻¹`) in field-level form (matching the iff RHS shape),
derives `a.val < 65536` plus the byte decomposition at the `.val` level. -/
private lemma u16_to_u8_decomposition
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] {a b : ZMod p} :
  b < 256 → ((a - b) * (256 : ZMod p)⁻¹) < 256 →
    a.val < 65536 ∧ a.val % 256 = b.val ∧ ((a - b) * (256 : ZMod p)⁻¹).val = a.val / 256
  := by
    intro h_b h_diff
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have hp : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    -- Convert field-level `<` to Nat-level `.val <`
    have h_b' : b.val < 256 := by
      have : b.val < (256 : ZMod p).val := h_b
      rw [val_256_zmod_p] at this; exact this
    have h_diff' : ((a - b) * (256 : ZMod p)⁻¹).val < 256 := by
      have : ((a - b) * (256 : ZMod p)⁻¹).val < (256 : ZMod p).val := h_diff
      rw [val_256_zmod_p] at this; exact this
    set high : ZMod p := (a - b) * (256 : ZMod p)⁻¹ with h_high_def
    have h_high_mul : high * 256 = a - b := by
      rw [h_high_def, mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one]
    have h_a_eq : a = b + high * 256 := by linear_combination -h_high_mul
    have h_high_val_mul : (high * 256).val = high.val * 256 := by
      rw [ZMod.val_mul_of_lt (by rw [val_256_zmod_p]; nlinarith), val_256_zmod_p]
    have h_a_val : a.val = b.val + high.val * 256 := by
      rw [h_a_eq]
      rw [ZMod.val_add_of_lt (by rw [h_high_val_mul]; nlinarith), h_high_val_mul]
    exact ⟨by omega, by omega, by omega⟩

/-- Bridges from the constraint list (each limb decomposes into a low
byte `< 256` and a high byte `< 256` derived via the `256⁻¹` multiplication)
to a concrete `Word.toBWord` byte vector. The 8 byte-level equations
follow from applying `u16_to_u8_decomposition` per limb. -/
lemma spec.unsafe.return
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {u16_values : (Vector (ZMod p) 4)}
  {cols : U16toU8Operation (ZMod p)} :
  List.Forall SP1Constraint.toProp (constraints u16_values cols 1).2 →
    (U16toU8OperationUnsafe.constraints u16_values cols).1 = Word.toBWord u16_values
  := by
    intro cstrs
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨c0, c1, c2, c3⟩
    obtain ⟨h_b0_lt, h_diff0_lt⟩ := c0 one_ne_zero
    obtain ⟨h_b1_lt, h_diff1_lt⟩ := c1 one_ne_zero
    obtain ⟨h_b2_lt, h_diff2_lt⟩ := c2 one_ne_zero
    obtain ⟨h_b3_lt, h_diff3_lt⟩ := c3 one_ne_zero
    obtain ⟨_, hmod0, hdiv0⟩ := u16_to_u8_decomposition h_b0_lt h_diff0_lt
    obtain ⟨_, hmod1, hdiv1⟩ := u16_to_u8_decomposition h_b1_lt h_diff1_lt
    obtain ⟨_, hmod2, hdiv2⟩ := u16_to_u8_decomposition h_b2_lt h_diff2_lt
    obtain ⟨_, hmod3, hdiv3⟩ := u16_to_u8_decomposition h_b3_lt h_diff3_lt
    simp [U16toU8OperationUnsafe.constraints, Word.toBWord]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (rw [hmod0]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [hmod1]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [hmod2]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [hmod3]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [← hdiv0]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [← hdiv1]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [← hdiv2]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [← hdiv3]; exact (ZMod.natCast_zmod_val _).symm)

/-- The `.1` projection of `U16toU8OperationSafe.constraints` is
definitionally the same byte vector as
`U16toU8OperationUnsafe.constraints.1` (only the trailing constraint list
differs), so we can dispatch to `spec.unsafe.return` after a
definitional bridge. -/
lemma spec.return
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {u16_values : (Vector (ZMod p) 4)}
  {cols : U16toU8Operation (ZMod p)}
  (is_real : ZMod p) :
  List.Forall SP1Constraint.toProp (constraints u16_values cols 1).2 →
    (constraints u16_values cols is_real).1 = Word.toBWord u16_values
  := by
    intro cstrs
    have h_unsafe := spec.unsafe.return cstrs
    simp [constraints, U16toU8OperationUnsafe.constraints] at h_unsafe ⊢
    exact h_unsafe

end U16toU8OperationSafe
