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
  b < 256 → ((a - b) * 2122383361) < 256 → a < 65536 ∧ b = a % 256 ∧ ((a - b) * 2122383361) = a / 256
  := by
    intro h_b h_diff
    set a64 : Fin (2^64) := ⟨a.val, by omega⟩ with h_eq_a64
    set b64 : Fin (2^64) := ⟨b.val, by omega⟩ with h_eq_b64
    have h_diff_64 : ((KB - b64 + a64) * 2122383361) % KB < 256 := by
      simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at h_diff
      simp only [Fin.lt_def, Fin.mul_def, Fin.mod_val]
      have h_eq : (KB - b64 + a64).val = ((KB : ℕ) - ↑b + ↑a) := by
        rw [Fin.add_def, Fin.sub_val_of_le (by aesop (add safe cases Fin) (add safe (by omega)))]
        aesop (add safe cases Fin) (add safe (by omega))
      rw [Nat.mod_eq_of_lt (b := 2 ^ 64)] <;> aesop (add safe (by omega))
    have := u16_to_u8_decomposition_fin64 (by aesop (add safe cases Fin)) (by aesop) h_diff_64
    rw [← Fin.val_eq_val] at this
    aesop (add safe (by omega))

end decomposition

lemma allHold_constraints_iff
  (u16_values : (Vector (Fin KB) 4))
  (cols : U16toU8Operation)
  (is_real : Fin KB) :
  List.Forall SP1Constraint.toProp (constraints u16_values cols is_real).2 ↔
    (¬is_real = 0 → cols.low_bytes[0] < 256 ∧ ((u16_values[0] - cols.low_bytes[0]) * 2122383361) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[1] < 256 ∧ ((u16_values[1] - cols.low_bytes[1]) * 2122383361) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[2] < 256 ∧ ((u16_values[2] - cols.low_bytes[2]) * 2122383361) < 256) ∧
    (¬is_real = 0 → cols.low_bytes[3] < 256 ∧ ((u16_values[3] - cols.low_bytes[3]) * 2122383361) < 256)
  := by simp [constraints]

lemma spec.cstrs
  {u16_values : (Vector (Fin KB) 4)}
  {cols : U16toU8Operation} :
  List.Forall SP1Constraint.toProp (constraints u16_values cols 1).2 →
    cols.low_bytes[0] = u16_values[0]! % 256 ∧ ((u16_values[0] - cols.low_bytes[0]!) * 2122383361) = u16_values[0] / 256 ∧
    cols.low_bytes[1] = u16_values[1]! % 256 ∧ ((u16_values[1] - cols.low_bytes[1]!) * 2122383361) = u16_values[1] / 256 ∧
    cols.low_bytes[2] = u16_values[2]! % 256 ∧ ((u16_values[2] - cols.low_bytes[2]!) * 2122383361) = u16_values[2] / 256 ∧
    cols.low_bytes[3] = u16_values[3]! % 256 ∧ ((u16_values[3] - cols.low_bytes[3]!) * 2122383361) = u16_values[3] / 256
  := by intro cstrs; rw [allHold_constraints_iff] at cstrs; aesop

lemma spec.return
  {u16_values : (Vector (Fin KB) 4)}
  {cols : U16toU8Operation} :
  List.Forall SP1Constraint.toProp (constraints u16_values cols 1).2 →
    (constraints u16_values cols is_real).1 = Word.toBWord u16_values
  := by
    intro cstrs; apply spec.cstrs at cstrs
    simp [constraints, Word.toBWord]; aesop

lemma spec.unsafe.return
  {u16_values : (Vector (Fin KB) 4)}
  {cols : U16toU8Operation} :
  List.Forall SP1Constraint.toProp (constraints u16_values cols 1).2 →
    (U16toU8OperationUnsafe.constraints u16_values cols).1 = Word.toBWord u16_values
  := by
    intro cstrs; apply spec.cstrs at cstrs
    simp [U16toU8OperationUnsafe.constraints, Word.toBWord]; aesop

end U16toU8OperationSafe
