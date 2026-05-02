import SP1Operations.Operation.U16toU8OperationUnsafe
import SP1Operations.Operation.U16toU8OperationSafe.Operation
import SP1Operations.Operation.U16toU8OperationSafe.Constraints

namespace U16toU8OperationSafe

section decomposition

lemma u16_to_u8_decomposition_bv64_bv64 (a b : BitVec 64) :
  a < KB → b < 256 → ((KB - b + a) * 2122383361) % KB < 256 → a < 65536 ∧ b = a % 256 ∧ ((a - b) * 2122383361) % KB = a / 256
  := by bv_decide (timeout := 10000)

lemma u16_to_u8_decomposition_fin64 {a b : Fin (2 ^ 64)} :
  a < KB →
  b < 256 →
  ((KB - b + a) * 2122383361) % KB < 256 →
  a < 65536 ∧ b = a % 256 ∧ (((a - b) * 2122383361) % KB) = a / 256
  := by
    intro h_a h_b h_diff
    have ⟨h_lt, h_mod, h_div⟩ :=
      u16_to_u8_decomposition_bv64_bv64 (.ofFin a) (.ofFin b)
                                        (by simp_all) (by simp_all)
                                        (by bv_amicus_kerneli at *
                                            exact BitVec.ofNat_lt_ofNat.2 (Nat.mod_lt_of_lt h_diff))
    rw [← BitVec.toFin_inj] at h_mod h_div
    bv_amicus_kerneli at *
    simp_all

@[grind →, aesop safe forward]
lemma u16_to_u8_decomposition_bb {a b : Fin KB} :
  b < 256 → ((a - b) * (256 : Fin KB)⁻¹) < 256 → a < 65536 ∧ b = a % 256 ∧ ((a - b) * (256 : Fin KB)⁻¹) = a / 256
  := by
    intro h_b h_diff
    have h_inv : ((256 : Fin KB)⁻¹).val = 2122383361 := rfl
    set a64 : Fin (2^64) := ⟨a.val, by omega⟩ with h_eq_a64
    set b64 : Fin (2^64) := ⟨b.val, by omega⟩ with h_eq_b64
    have h_diff_64 : ((KB - b64 + a64) * 2122383361) % KB < 256 := by
      simp [Fin.lt_def, Fin.mul_def, Fin.sub_def, h_inv] at h_diff
      simp only [Fin.lt_def, Fin.mul_def, Fin.mod_val]
      have h_eq : (KB - b64 + a64).val = ((KB : ℕ) - ↑b + ↑a) := by
        rw [Fin.add_def, Fin.sub_val_of_le (by aesop (add safe cases Fin) (add safe (by omega)))]
        aesop (add safe cases Fin) (add safe (by omega))
      rw [Nat.mod_eq_of_lt (b := 2 ^ 64)] <;> aesop (add safe (by omega))
    have := u16_to_u8_decomposition_fin64 (by aesop (add safe cases Fin)) (by aesop) h_diff_64
    rw [← Fin.val_eq_val] at this
    simp only [Fin.lt_def, Fin.mul_def, Fin.sub_def, h_inv]
    aesop (add safe (by omega))

end decomposition

lemma allHold_constraints_iff
  (u16_values : (Vector (Fin KB) 4))
  (cols : U16toU8Operation (Fin KB))
  (is_real : Fin KB) :
  List.Forall SP1Constraint.toProp (constraints u16_values cols is_real).2 ↔
    (¬is_real = 0 → cols.low_bytes[0] < 256 ∧ ((u16_values[0] - cols.low_bytes[0]) * (256 : Fin KB)⁻¹) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[1] < 256 ∧ ((u16_values[1] - cols.low_bytes[1]) * (256 : Fin KB)⁻¹) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[2] < 256 ∧ ((u16_values[2] - cols.low_bytes[2]) * (256 : Fin KB)⁻¹) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[3] < 256 ∧ ((u16_values[3] - cols.low_bytes[3]) * (256 : Fin KB)⁻¹) < 256)
  := by simp [constraints]

/-- Polymorphic companion of `allHold_constraints_iff` over `ZMod p`. The
auto-gen U8Range opcode produces field-level `<` (per the B.8 finding
on `constrain_poly_U8Range`); the only delta vs the `Fin KB` proof is
that we need to provide `(0 : ZMod p) < (256 : ZMod p)` explicitly
(the `Fin KB` version sees this `decide`-true). -/
lemma allHold_constraints_iff_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (u16_values : (Vector (ZMod p) 4))
  (cols : U16toU8Operation (ZMod p))
  (is_real : ZMod p) :
  List.Forall SP1Constraint.toProp_poly (constraints u16_values cols is_real).2 ↔
    (¬is_real = 0 → cols.low_bytes[0] < 256 ∧ ((u16_values[0] - cols.low_bytes[0]) * (256 : ZMod p)⁻¹) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[1] < 256 ∧ ((u16_values[1] - cols.low_bytes[1]) * (256 : ZMod p)⁻¹) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[2] < 256 ∧ ((u16_values[2] - cols.low_bytes[2]) * (256 : ZMod p)⁻¹) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[3] < 256 ∧ ((u16_values[3] - cols.low_bytes[3]) * (256 : ZMod p)⁻¹) < 256)
  := by
  have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
    change (0 : ZMod p).val < (256 : ZMod p).val; simp
  simp [constraints, SP1Constraint.toProp_poly, h0_lt_256]

lemma spec.cstrs
  {u16_values : (Vector (Fin KB) 4)}
  {cols : U16toU8Operation (Fin KB)} :
  List.Forall SP1Constraint.toProp (constraints u16_values cols 1).2 →
    cols.low_bytes[0] = u16_values[0]! % 256 ∧ ((u16_values[0] - cols.low_bytes[0]!) * (256 : Fin KB)⁻¹) = u16_values[0] / 256 ∧
    cols.low_bytes[1] = u16_values[1]! % 256 ∧ ((u16_values[1] - cols.low_bytes[1]!) * (256 : Fin KB)⁻¹) = u16_values[1] / 256 ∧
    cols.low_bytes[2] = u16_values[2]! % 256 ∧ ((u16_values[2] - cols.low_bytes[2]!) * (256 : Fin KB)⁻¹) = u16_values[2] / 256 ∧
    cols.low_bytes[3] = u16_values[3]! % 256 ∧ ((u16_values[3] - cols.low_bytes[3]!) * (256 : Fin KB)⁻¹) = u16_values[3] / 256
  := by intro cstrs; rw [allHold_constraints_iff] at cstrs; aesop

lemma spec.return
  {u16_values : (Vector (Fin KB) 4)}
  {cols : U16toU8Operation (Fin KB)} :
  List.Forall SP1Constraint.toProp (constraints u16_values cols 1).2 →
    (constraints u16_values cols is_real).1 = Word.toBWord u16_values
  := by
    intro cstrs; apply spec.cstrs at cstrs
    simp [constraints, Word.toBWord]; aesop

lemma spec.unsafe.return
  {u16_values : (Vector (Fin KB) 4)}
  {cols : U16toU8Operation (Fin KB)} :
  List.Forall SP1Constraint.toProp (constraints u16_values cols 1).2 →
    (U16toU8OperationUnsafe.constraints u16_values cols).1 = Word.toBWord u16_values
  := by
    intro cstrs; apply spec.cstrs at cstrs
    simp [U16toU8OperationUnsafe.constraints, Word.toBWord]; aesop

/-- Polymorphic counterpart of `u16_to_u8_decomposition_bb`. Given the
two `< 256` bounds (low byte and high byte after dividing by `256⁻¹`)
in field-level form (matching the iff_poly RHS shape), derives
`a.val < 65536` plus the byte decomposition at the `.val` level. -/
private lemma u16_to_u8_decomposition_poly
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

/-- Polymorphic counterpart of `spec.unsafe.return`. Bridges from the
constraint list (each limb decomposes into a low byte `< 256` and a high
byte `< 256` derived via the `256⁻¹` multiplication) to a concrete
`Word.toBWord_poly` byte vector. The 8 byte-level equations follow from
applying `u16_to_u8_decomposition_poly` per limb. -/
lemma spec.unsafe.return_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {u16_values : (Vector (ZMod p) 4)}
  {cols : U16toU8Operation (ZMod p)} :
  List.Forall SP1Constraint.toProp_poly (constraints u16_values cols 1).2 →
    (U16toU8OperationUnsafe.constraints u16_values cols).1 = Word.toBWord_poly u16_values
  := by
    intro cstrs
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    rw [allHold_constraints_iff_poly] at cstrs
    rcases cstrs with ⟨c0, c1, c2, c3⟩
    obtain ⟨h_b0_lt, h_diff0_lt⟩ := c0 one_ne_zero
    obtain ⟨h_b1_lt, h_diff1_lt⟩ := c1 one_ne_zero
    obtain ⟨h_b2_lt, h_diff2_lt⟩ := c2 one_ne_zero
    obtain ⟨h_b3_lt, h_diff3_lt⟩ := c3 one_ne_zero
    obtain ⟨_, hmod0, hdiv0⟩ := u16_to_u8_decomposition_poly h_b0_lt h_diff0_lt
    obtain ⟨_, hmod1, hdiv1⟩ := u16_to_u8_decomposition_poly h_b1_lt h_diff1_lt
    obtain ⟨_, hmod2, hdiv2⟩ := u16_to_u8_decomposition_poly h_b2_lt h_diff2_lt
    obtain ⟨_, hmod3, hdiv3⟩ := u16_to_u8_decomposition_poly h_b3_lt h_diff3_lt
    simp [U16toU8OperationUnsafe.constraints, Word.toBWord_poly]
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

end U16toU8OperationSafe
