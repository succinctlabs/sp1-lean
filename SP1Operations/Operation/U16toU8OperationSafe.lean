import SP1Operations.Operation.U16toU8OperationUnsafe
import SP1Operations.Operation.U16toU8OperationSafe.Operation
import SP1Operations.Operation.U16toU8OperationSafe.Constraints

namespace U16toU8OperationSafe

lemma allHold_constraints_iff
  (u16_values : (Vector (Fin BB) 4))
  (cols : U16toU8Operation)
  (is_real : Fin BB) :
  (constraints u16_values cols is_real).2.allHold ↔
    (¬is_real = 0 → cols.low_bytes[0] < 256 ∧ ((u16_values[0] - cols.low_bytes[0]) * 2005401601) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[1] < 256 ∧ ((u16_values[1] - cols.low_bytes[1]) * 2005401601) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[2] < 256 ∧ ((u16_values[2] - cols.low_bytes[2]) * 2005401601) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[3] < 256 ∧ ((u16_values[3] - cols.low_bytes[3]) * 2005401601) < 256)
  := by
    simp [and_assoc, constraints, sub_eq_zero, Fin.lt_iff_val_lt_val]

lemma u16_to_u8_decomposition_bv64_bv64 (a b : BitVec 64) :
  a < BB → b < 256 → ((BB - b + a) * 2005401601) % BB < 256 → a < 65536 ∧ b = a % 256 ∧ ((a - b) * 2005401601) % 2013265921 = a / 256
  := by bv_check "U16toU8OperationSafe.u16_to_u8_decomposition_bv64_bv64-21-8.lrat"

lemma u16_to_u8_decomposition_fin64 {a b : Fin (2 ^ 64)} :
  a < BB →
  b < 256 →
  ((BB - b + a) * 2005401601) % BB < 256 →
  a < 65536 ∧ b = a % 256 ∧ (((a - b) * 2005401601) % BB) = a / 256
  := by
    intro h_a h_b h_diff
    have ⟨ h_lt, h_mod, h_div ⟩ :=
      u16_to_u8_decomposition_bv64_bv64 (.ofFin a) (.ofFin b)
                                        (by simp_all) (by simp_all)
                                        (by bv_amicus_kerneli at *
                                            exact BitVec.ofNat_lt_ofNat.2 (Nat.mod_lt_of_lt h_diff))
    rw [← BitVec.toFin_inj] at h_mod h_div
    bv_amicus_kerneli at *
    simp_all

lemma u16_to_u8_decomposition_bb (a b : Fin BB) :
  b < 256 → ((a - b) * 2005401601) < 256 → a < 65536 ∧ b = a % 256 ∧ ((a - b) * 2005401601) = a / 256
  := by
    intro h_b h_diff
    set a64 : Fin (2^64) := ⟨a.val, by omega⟩ with h_eq_a64
    set b64 : Fin (2^64) := ⟨b.val, by omega⟩ with h_eq_b64
    have h_diff_64 : ((BB - b64 + a64) * 2005401601) % BB < 256 := by
      simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at h_diff
      simp only [Fin.lt_def, Fin.mul_def, Fin.mod_val]
      have h_eq : (BB - b64 + a64).val = ((BB : ℕ) - ↑b + ↑a) := by
        rw [Fin.add_def, Fin.sub_val_of_le (by aesop (add safe cases Fin) (add safe (by omega)))]
        aesop (add safe cases Fin) (add safe (by omega))
      rw [Nat.mod_eq_of_lt (b := 2 ^ 64)] <;> aesop (add safe (by omega))
    have := u16_to_u8_decomposition_fin64 (by aesop (add safe cases Fin)) (by aesop) h_diff_64
    rw [← Fin.val_eq_val] at this
    aesop (add safe (by omega))

lemma spec.cstrs
  (u16_values : (Vector (Fin BB) 4))
  (cols : U16toU8Operation)
  (is_real : Fin BB)
  (cstrs : (constraints u16_values cols is_real).2.allHold)
  (h_is_real : is_real ≠ 0) :
      cols.low_bytes[0]! = u16_values[0]! % 256 ∧ ((u16_values[0] - cols.low_bytes[0]!) * 2005401601) = u16_values[0] / 256 ∧
      cols.low_bytes[1]! = u16_values[1]! % 256 ∧ ((u16_values[1] - cols.low_bytes[1]!) * 2005401601) = u16_values[1] / 256 ∧
      cols.low_bytes[2]! = u16_values[2]! % 256 ∧ ((u16_values[2] - cols.low_bytes[2]!) * 2005401601) = u16_values[2] / 256 ∧
      cols.low_bytes[3]! = u16_values[3]! % 256 ∧ ((u16_values[3] - cols.low_bytes[3]!) * 2005401601) = u16_values[3] / 256
  := by
    rw [allHold_constraints_iff] at cstrs; simp_all
    rcases cstrs with ⟨ ⟨ h_lb_0, h_lb_1 ⟩, ⟨ h_lb_2, h_lb_3 ⟩,  ⟨ h_lb_4, h_lb_5 ⟩,  ⟨ h_lb_6, h_lb_7 ⟩  ⟩
    have := u16_to_u8_decomposition_bb _ _ h_lb_0 h_lb_1
    have := u16_to_u8_decomposition_bb _ _ h_lb_2 h_lb_3
    have := u16_to_u8_decomposition_bb _ _ h_lb_4 h_lb_5
    have := u16_to_u8_decomposition_bb _ _ h_lb_6 h_lb_7
    aesop

lemma spec.return
  (u16_values : (Vector (Fin BB) 4))
  (cols : U16toU8Operation)
  (is_real : Fin BB)
  (cstrs : (constraints u16_values cols is_real).2.allHold)
  (h_is_real : is_real ≠ 0) :
    (constraints u16_values cols is_real).1 = Word.toByteWord u16_values
  := by
    have ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩ := spec.cstrs u16_values cols is_real cstrs h_is_real
    simp [constraints, Word.toByteWord]
    aesop

end U16toU8OperationSafe
