import SP1Operations.Compare.LtOperationUnsigned.Constraints

namespace LtOperationUnsigned

lemma allHold_constraints_iff
  (b : Word (Fin KB))
  (d : Word (Fin KB))
  (cols : LtOperationUnsigned)
  (is_real : Fin KB) :
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
    simp [and_assoc, constraints, sub_eq_zero, Fin.lt_def]

@[grind →]
lemma cl_are_U16
  {b : Word (Fin KB)}
  {d : Word (Fin KB)}
  {cols : LtOperationUnsigned}
  {is_real : Fin KB}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols is_real) →
    is_real = 1 →
      (cols.comparison_limbs[0] : ℕ) < 65536 ∧ (cols.comparison_limbs[1] : ℕ) < 65536
  := by simp [constraints]; sorry --grind (splits := 16)

set_option maxHeartbeats 1000000 in
@[grind →, aesop safe forward]
lemma spec.nat
  {b d : Word (Fin KB)}
  {cols : LtOperationUnsigned}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols 1) →
    cols.u16_compare_operation.bit = if b.toNat < d.toNat then (1 : Fin KB) else (0 : Fin KB)
  := by
    intro cstrs
    have ⟨ _, _ ⟩ := cl_are_U16 h_b_isU64 h_d_isU64 cstrs (by rfl)
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨ h_comp_limbs, ⟨ h_is_real_bool, h_flag_0_bool, h_flag_1_bool, h_flag_2_bool, h_flag_3_bool, cstrs ⟩ ⟩
    apply U16CompareOperation.spec at h_comp_limbs <;> try assumption
    unfold Word.toNat
    rcases h_flag_0_bool <;> rcases h_flag_1_bool <;>
    rcases h_flag_2_bool <;> rcases h_flag_3_bool <;>
    aesop (add safe (by omega)) (add safe cases LtOperationUnsigned)

lemma spec
  {b d : Word (Fin KB)}
  {cols : LtOperationUnsigned}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols 1) →
    BitVec.ofNat 64 cols.u16_compare_operation.bit = execute_RTYPE_pure_w b d .SLTU
  := by aesop

section gen

lemma spec.nat.gen
  {b d : Word (Fin KB)}
  {cols : LtOperationUnsigned}
  {is_real : Fin KB}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols is_real) →
    is_real = 1 →
      cols.u16_compare_operation.bit = if b.toNat < d.toNat then (1 : Fin KB) else (0 : Fin KB)
    := by aesop

end gen

end LtOperationUnsigned
