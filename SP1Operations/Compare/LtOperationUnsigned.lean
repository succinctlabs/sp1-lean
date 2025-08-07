import SP1Operations.Compare.LtOperationUnsigned.Operation
import SP1Operations.Compare.LtOperationUnsigned.Constraints

namespace LtOperationUnsigned

lemma allHold_constraints_iff
  (b : Word (Fin BB))
  (d : Word (Fin BB))
  (cols : LtOperationUnsigned)
  (is_real : Fin BB) :
  (constraints b d cols is_real).allHold ↔
    (U16CompareOperation.constraints cols.comparison_limbs[0] cols.comparison_limbs[1] cols.u16_compare_operation is_real).allHold ∧
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
    simp [and_assoc, constraints, sub_eq_zero, Fin.lt_iff_val_lt_val]

set_option maxHeartbeats 500000 in
lemma cl_are_U16
  (b : Word (Fin BB))
  (d : Word (Fin BB))
  (cols : LtOperationUnsigned)
  (is_real : Fin BB)
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  (constraints b d cols is_real).allHold →
    is_real ≠ 0 →
      (cols.comparison_limbs[0] : ℕ) < 65536 ∧ (cols.comparison_limbs[1] : ℕ) < 65536
  := by
    intro cstrs h_is_real
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨ h_comp_limbs, ⟨ h_is_real_bool, h_flag_0_bool, h_flag_1_bool, h_flag_2_bool, h_flag_3_bool, cstrs ⟩ ⟩
    apply Word.lt_cases_of_isU64 at h_b_isU64
    apply Word.lt_cases_of_isU64 at h_d_isU64
    rcases h_is_real_bool <;> simp_all
    rcases h_flag_0_bool <;> rcases h_flag_1_bool <;>
    rcases h_flag_2_bool <;> rcases h_flag_3_bool <;>
    simp_all
    omega

set_option maxHeartbeats 1000000 in
lemma spec
  (b : Word (Fin BB))
  (d : Word (Fin BB))
  (cols : LtOperationUnsigned)
  (is_real : Fin BB)
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d):
  (constraints b d cols is_real).allHold →
    (is_real ≠ 0 → BitVec.ofNat 64 cols.u16_compare_operation.bit = execute_RTYPE_pure_w b d .SLTU)
  := by
    intro cstrs h_is_real
    suffices : cols.u16_compare_operation.bit = if b.toNat < d.toNat then 1 else 0
    . simp [Word.toNat, Nat.shiftLeft_eq] at *
      aesop
    . have ⟨ _, _ ⟩ := cl_are_U16 b d cols is_real h_b_isU64 h_d_isU64 cstrs h_is_real
      rw [allHold_constraints_iff] at cstrs
      rcases cstrs with ⟨ h_comp_limbs, ⟨ h_is_real_bool, h_flag_0_bool, h_flag_1_bool, h_flag_2_bool, h_flag_3_bool, cstrs ⟩ ⟩
      apply U16CompareOperation.spec at h_comp_limbs <;> try assumption
      apply Word.lt_cases_of_isU64 at h_b_isU64
      apply Word.lt_cases_of_isU64 at h_d_isU64
      simp [Word.toNat, Nat.shiftLeft_eq]
      rcases h_is_real_bool <;> simp_all
      rcases h_flag_0_bool <;> rcases h_flag_1_bool <;>
      rcases h_flag_2_bool <;> rcases h_flag_3_bool <;>
      simp_all <;> clear h_comp_limbs
      . omega
      . rcases cstrs with ⟨ h_cl0, h_cl1, h_cl_diff ⟩
        simp [← h_cl0, ← h_cl1] at *
        have h_neq : b[3] ≠ d[3] := by by_contra!; rw [this] at h_cl_diff; simp_all
        split_ifs <;> omega
      . rcases cstrs with ⟨ h_eq_3, h_cl0, h_cl1, h_cl_diff ⟩
        simp [← h_cl0, ← h_cl1] at *
        have h_neq : b[2] ≠ d[2] := by by_contra!; rw [this] at h_cl_diff; simp_all
        split_ifs <;> omega
      . rcases cstrs with ⟨ h_eq_3, h_eq_2, h_cl0, h_cl1, h_cl_diff ⟩
        simp [← h_cl0, ← h_cl1] at *
        have h_neq : b[1] ≠ d[1] := by by_contra!; rw [this] at h_cl_diff; simp_all
        split_ifs <;> omega

end LtOperationUnsigned
