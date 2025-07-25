import SP1Operations.Compare.LtOperationSigned.Operation
import SP1Operations.Compare.LtOperationSigned.Constraints

namespace LtOperationSigned

lemma allHold_constraints_iff
  (b : Word (Fin BB))
  (d : Word (Fin BB))
  (cols : LtOperationSigned)
  (is_signed : Fin BB)
  (is_real : Fin BB) :
  (constraints b d cols is_signed is_real).allHold ↔
    (U16MSBOperation.constraints b[3] cols.b_msb is_signed).allHold ∧
    (U16MSBOperation.constraints d[3] cols.c_msb is_signed).allHold ∧
    (LtOperationUnsigned.constraints
      #v[b[0], b[1], b[2], b[3] + is_signed * 32768 - 65536 * cols.b_msb.msb]
      #v[d[0], d[1], d[2], d[3] + is_signed * 32768 - 65536 * cols.c_msb.msb]
      { u16_compare_operation := cols.result.u16_compare_operation,
        u16_flags := #v[cols.result.u16_flags[0], cols.result.u16_flags[1], cols.result.u16_flags[2], cols.result.u16_flags[3]],
        not_eq_inv := cols.result.not_eq_inv,
        comparison_limbs := #v[cols.result.comparison_limbs[0], cols.result.comparison_limbs[1]] }
      is_real).allHold ∧
    ((is_signed = 0 ∨ is_signed = 1) ∧
    (is_real = 0 ∨ is_real = 1) ∧
    (is_real = 1 ∨ is_signed = 0) ∧
    (is_signed = 1 ∨ cols.b_msb.msb = 0) ∧
    (is_signed = 1 ∨ cols.c_msb.msb = 0))
  := by
    simp [and_assoc, constraints, sub_eq_zero, Fin.lt_iff_val_lt_val]

set_option maxHeartbeats 1000000 in
lemma spec.unsigned
  (b : Word (Fin BB))
  (d : Word (Fin BB))
  (cols : LtOperationSigned)
  (is_signed : Fin BB)
  (is_real : Fin BB)
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d):
  (constraints b d cols is_signed is_real).allHold →
    (is_real ≠ 0 → is_signed = 0 → cols.result.u16_compare_operation.bit = if b.toNat < d.toNat then 1 else 0)
  := by
    intro cstrs h_is_real h_is_signed
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨ h_b_msb, h_c_msb, h_lt, ⟨ h_is_signed_bool, h_is_real_bool, h_is_real_is_signed, h_is_signed_b_msb, h_is_signed_c_msb ⟩ ⟩
    apply U16MSBOperation.spec.U64 (h_w_isU64 := h_b_isU64) at h_b_msb
    apply U16MSBOperation.spec.U64 (h_w_isU64 := h_d_isU64) at h_c_msb
    apply Word.lt_cases_of_isU64 at h_b_isU64
    apply Word.lt_cases_of_isU64 at h_d_isU64
    apply LtOperationUnsigned.spec at h_lt
    . unfold Word.toNat at *; simp_all
    . apply Word.isU64_of_cases <;> simp_all
    . apply Word.isU64_of_cases <;> simp_all

set_option maxHeartbeats 1000000 in
lemma spec.signed
  (b : Word (Fin BB))
  (d : Word (Fin BB))
  (cols : LtOperationSigned)
  (is_signed : Fin BB)
  (is_real : Fin BB)
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d):
  (constraints b d cols is_signed is_real).allHold →
    (is_real ≠ 0 → is_signed = 1 → cols.result.u16_compare_operation.bit = if b.toInt < d.toInt then 1 else 0)
  := by
    intro cstrs h_is_real h_is_signed
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨  h_b_msb, h_c_msb, h_lt, ⟨ h_is_signed_bool, h_is_real_bool, h_is_real_is_signed, h_is_signed_b_msb, h_is_signed_c_msb ⟩ ⟩
    apply U16MSBOperation.spec.U64 (h_w_isU64 := h_b_isU64) at h_b_msb
    apply U16MSBOperation.spec.U64 (h_w_isU64 := h_d_isU64) at h_c_msb
    apply Word.lt_cases_of_isU64 at h_b_isU64
    apply Word.lt_cases_of_isU64 at h_d_isU64
    subst is_signed; simp at *
    have h_sb_isU64 : Word.isU64 #v[b[0], b[1], b[2], b[3] + 32768 - 65536 * cols.b_msb.msb] := by
      rw [h_b_msb]; clear h_lt h_b_msb h_c_msb
      by_cases b.isNegative <;> unfold Word.isNegative at * <;> simp_all
      . apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> simp_all
        omega
      . apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> simp_all
        rw [if_neg] <;> omega
    have h_sd_isU64 : Word.isU64 #v[d[0], d[1], d[2], d[3] + 32768 - 65536 * cols.c_msb.msb] := by
      rw [h_c_msb]; clear h_lt h_b_msb h_c_msb
      by_cases d.isNegative <;> unfold Word.isNegative at * <;> simp_all
      . apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> simp_all
        omega
      . apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> simp_all
        rw [if_neg] <;> omega
    apply LtOperationUnsigned.spec (h_b_isU64 := h_sb_isU64) (h_d_isU64 := h_sd_isU64) at h_lt
    unfold Word.toNat at h_lt; repeat rw [Vector.getElem_mk] at h_lt
    unfold Word.toInt Word.toNat
    by_cases h_b_neg : b.isNegative <;>
    by_cases h_b_neg : d.isNegative <;>
    simp_all <;> unfold Word.isNegative at * <;>
    split_ifs <;> omega

end LtOperationSigned
